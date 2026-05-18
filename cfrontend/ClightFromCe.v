(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Translation from ClightCe to Clight.
    Mostly borrowed from SimplExpr. *)

Require Import Coqlib Maps Integers Floats Values AST Memory Errors.
Require Import Ctypes Cop ClightCe Clight.

Local Open Scope string_scope.
Local Open Scope list_scope.

(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
  gen_next: ident;
  gen_trail: list (ident * type)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.

Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g (Ple_refl (gen_next g)).

Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' i =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
      end
    end.

Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Declare Scope gensym_monad_scope.
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X name, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X name, Y name, A at level 100, B at level 200)
   : gensym_monad_scope.

Parameter first_unused_ident: unit -> ident.

Definition initial_generator (x: unit) : generator :=
  mkgenerator (first_unused_ident x) nil.

Definition gensym (ty: type): mon ident :=
  fun (g: generator) =>
    Res (gen_next g)
        (mkgenerator (Pos.succ (gen_next g)) ((gen_next g, ty) :: gen_trail g))
        (Ple_succ (gen_next g)).

(** Construct a sequence from a list of statements.  To facilitate the
   proof, the sequence is nested to the left and starts with a [Sskip]. *)

Fixpoint makeseq_rec (s: statement) (l: list statement) : statement :=
  match l with
  | nil => s
  | s' :: l' => makeseq_rec (Ssequence s s') l'
  end.

Definition makeseq (l: list statement) : statement :=
  makeseq_rec Sskip l.

Section SIMPL_Cond.

Local Open Scope gensym_monad_scope.

(*Variable ce: composite_env.*)

(** Smart constructor for [if ... then ... else]. *)

Fixpoint eval_simpl_expr (a: expr) : option val :=
  match a with
  | Econst_int n _ => Some(Vint n)
  | Econst_float n _ => Some(Vfloat n)
  | Econst_single n _ => Some(Vsingle n)
  | Econst_long n _ => Some(Vlong n)
  | Ecast b ty =>
      match eval_simpl_expr b with
      | None => None
      | Some v => sem_cast v (typeof b) ty Mem.empty
      end
  | _ => None
  end.

Function makeif (a: expr) (s1 s2: statement) : statement :=
  match eval_simpl_expr a with
  | Some v =>
      match bool_val v (typeof a) Mem.empty with
      | Some b => if b then s1 else s2
      | None   => Sifthenelse a s1 s2
      end
  | None => Sifthenelse a s1 s2
  end.

(*
(** Smart constructors for [&] and [*].  They optimize away [&*] and [*&] sequences. *)

Definition Ederef' (a: expr) (t: type) : expr :=
  match a with
  | Eaddrof a' t' => if type_eq t (typeof a') then a' else Ederef a t
  | _ => Ederef a t
  end.

Definition Eaddrof' (a: expr) (t: type) : expr :=
  match a with
  | Ederef a' t' => if type_eq t (typeof a') then a' else Eaddrof a t
  | _ => Eaddrof a t
  end.

(** Translation of pre/post-increment/decrement. *)

Definition transl_incrdecr (id: incr_or_decr) (a: expr) (ty: type) : expr :=
  match id with
  | Incr => Ebinop Oadd a (Econst_int Int.one type_int32s) (incrdecr_type ty)
  | Decr => Ebinop Osub a (Econst_int Int.one type_int32s) (incrdecr_type ty)
  end.

(** Given a simple l-value expression [l], determine whether it
    designates a bitfield.  *)

Definition is_bitfield_access_aux
              (fn: composite_env -> ident -> members -> res (Z * bitfield))
              (id: ident) (fld: ident) : mon bitfield :=
  match ce!id with
  | None => error (MSG "unknown composite " :: CTX id :: nil)
  | Some co =>
      match fn ce fld (co_members co) with
      | OK (_, bf) => ret bf
      | Error _ => error (MSG "unknown field " :: CTX fld :: nil)
      end
  end.

Definition is_bitfield_access (l: expr) : mon bitfield :=
  match l with
  | Efield r f _ =>
      match typeof r with
      | Tstruct id _ => is_bitfield_access_aux field_offset id f
      | Tunion id _  => is_bitfield_access_aux union_field_offset id f
      | _ => error (msg "is_bitfield_access")
      end
  | _ => ret Full
  end.

(** According to the CompCert C semantics, an access to a l-value of
    volatile-qualified type can either
  - produce an event in the trace of observable events, or
  - produce no event and behave as if no volatile qualifier was there.

    The latter case, where the volatile qualifier is ignored, happens if
  - the l-value is a struct or union
  - the l-value is an access to a bit field.

    The [chunk_for_volatile_type] function distinguishes between the two
    cases.  It returns [Some chunk] if the semantics is to produce
    an observable event of the [Event_vload chunk] or [Event_vstore chunk]
    kind.  It returns [None] if the semantics is that of a non-volatile
    access. *)

Definition chunk_for_volatile_type (ty: type) (bf: bitfield) : option memory_chunk :=
  if type_is_volatile ty then
    match access_mode ty with
    | By_value chunk =>
        match bf with
        | Full => Some chunk
        | Bits _ _ _ _ => None
        end
    | _ => None
    end
  else None.

(** Generate a [Sset] or [Sbuiltin] operation as appropriate
  to dereference a l-value [l] and store its result in temporary variable [id]. *)

Definition make_set (bf: bitfield) (id: ident) (l: expr) : statement :=
  match chunk_for_volatile_type (typeof l) bf with
  | None => Sset id l
  | Some chunk =>
      let typtr := Tpointer (typeof l) noattr in
      Sbuiltin (Some id) (EF_vload chunk) (typtr :: nil) ((Eaddrof l typtr):: nil)
  end.

(** Translation of a "valof" operation.
  If the l-value accessed is of volatile type, we go through a temporary. *)

Definition transl_valof (ty: type) (l: expr) : mon (list statement * expr) :=
  if type_is_volatile ty
  then do t <- gensym ty;
       do bf <- is_bitfield_access l;
       ret (make_set bf t l :: nil, Etempvar t ty)
  else ret (nil, l).

(** Translation of an assignment. *)

Definition make_assign (bf: bitfield) (l r: expr) : statement :=
  match chunk_for_volatile_type (typeof l) bf with
  | None =>
      Sassign l r
  | Some chunk =>
      let ty := typeof l in
      let typtr := Tpointer ty noattr in
      Sbuiltin None (EF_vstore chunk) (typtr :: ty :: nil)
                    (Eaddrof l typtr :: r :: nil)
  end.

(** Translation of the value of an assignment expression.
    For non-bitfield assignments, it's the value of the right-hand side
    converted to the type of the left-hand side.
    For assignments to bitfields, an additional normalization to
    the width and signedness of the bitfield is required. *)

Definition make_normalize (sz: intsize) (sg: signedness) (width: Z) (r: expr) :=
  let intconst (n: Z) := Econst_int (Int.repr n) type_int32s in
  if intsize_eq sz IBool || signedness_eq sg Unsigned then
    let mask := two_p width - 1 in
    Ebinop Oand r (intconst mask) (typeof r)
  else
    let amount := Int.zwordsize - width in
    Ebinop Oshr
           (Ebinop Oshl r (intconst amount) type_int32s)
           (intconst amount)
           (typeof r).

Definition make_assign_value (bf: bitfield) (r: expr): expr :=
  match bf with
  | Full => r
  | Bits sz sg pos width => make_normalize sz sg width r
  end.
 *)

(*(** The destinations for evaluating an expression.
- [For_val]: evaluate the expression for its side effects and its final value.
- [For_effects]: evaluate the expression for its side effects only;
  the final value is ignored.
- [For_set dest]: evaluate the expression for its side effects and its value,
  then cast and assign its value to temporaries as described in [dest],
  which is a nonempty list of (destination-type, source-type, temporary-name)
  triples. *)

Inductive set_destination : Type :=
  | SDbase (tycast ty: type) (tmp: ident)
  | SDcons (tycast ty: type) (tmp: ident) (sd: set_destination).

Inductive destination : Type :=
  | For_val
  | For_effects
  | For_set (sd: set_destination).

Definition dummy_expr := Econst_int Int.zero type_int32s.

(** Perform the assignments described by [sd]. *)

Fixpoint do_set (sd: set_destination) (a: expr) : list statement :=
  match sd with
  | SDbase tycast ty tmp => Sset tmp (Ecast a tycast) :: nil
  | SDcons tycast ty tmp sd' => Sset tmp (Ecast a tycast) :: do_set sd' (Etempvar tmp ty)
  end.

(** Perform the assignments described by [dst], if any. *)

Definition finish (dst: destination) (sl: list statement) (a: expr) :=
  match dst with
  | For_val => (sl, a)
  | For_effects => (sl, a)
  | For_set sd => (sl ++ do_set sd a, a)
  end.

(** Smart constructor for destinations.
    For chained assignments, better code is generated eventually
    if the same temporary is reused.  However, temporaries must have
    unique types, otherwise Cminor type reconstruction can fail,
    hence reuse is restricted to the case where the new type
    and the original type coincide. *)

Definition sd_temp (sd: set_destination) :=
  match sd with SDbase _ _ tmp => tmp | SDcons _ _ tmp _ => tmp end.

Definition sd_head_type (sd: set_destination) :=
  match sd with SDbase _ ty _ => ty | SDcons _ ty _ _ => ty end.

Definition temp_for_sd (ty: type) (sd: set_destination) : mon ident :=
    if type_eq ty (sd_head_type sd) then ret (sd_temp sd) else gensym ty.
 *)
(*
(** Translation of expressions.  Return a pair [(sl, a)] of
    a list of statements [sl] and a pure expression [a].
- If the [dst] argument is [For_val], the statements [sl]
  perform the side effects of the original expression,
  and [a] evaluates to the same value as the original expression.
- If the [dst] argument is [For_effects], the statements [sl]
  perform the side effects of the original expression,
  and [a] is meaningless.
- If the [dst] argument is [For_set sd], the statements [sl]
  perform the side effects of the original expression, then
  assign the value of the original expression to one or several
  temporaries, as described by the destination [sd].
*)
*)

Fixpoint transl_cexpr  (a: cexpr) : mon (list statement * expr) :=
  match a with
  | CE_expr e     => ret (nil,Ecast e type_bool)
  | CE_and r1 r2  =>
      do (sl1, a1) <- transl_cexpr  r1;
      do t <- gensym type_bool;
      do (sl2, a2) <- transl_cexpr  r2;
      ret (sl1 ++
             makeif a1 (Ssequence (makeseq sl2) (Sset t a2)) (Sset t (Econst_int Int.zero type_bool)) :: nil,
          Etempvar t type_bool)
  | CE_or r1 r2  =>
      do (sl1, a1) <- transl_cexpr  r1;
      do t <- gensym type_bool;
      do (sl2, a2) <- transl_cexpr  r2;
          ret (sl1 ++
                 makeif a1 (Sset t (Econst_int Int.one type_bool))  (Ssequence (makeseq sl2) (Sset t a2 )) :: nil,
              Etempvar t type_bool)
  | CE_not r1 =>
      do (sl1, a1) <- transl_cexpr  r1;
      ret (sl1, Eunop Onotbool a1 type_bool)
  end.

(** Translation of statements *)
Fixpoint transl_stmt (s: ClightCe.statement) : mon Clight.statement :=
  match s with
  | ClightCe.Sskip => ret Sskip
  | ClightCe.Sassign e1 e2 => ret (Sassign e1 e2)
  | ClightCe.Sset i e => ret (Sset i e)
  | ClightCe.Scall oi e l => ret (Scall oi e l)
  | ClightCe.Sbuiltin oi ef t l => ret (Sbuiltin oi ef t l)
  | ClightCe.Ssequence s1 s2   =>
      do s1 <- transl_stmt s1 ;
        do s2 <- transl_stmt s2 ;
        ret (Ssequence s1 s2)
  | ClightCe.Sifthenelse e s1 s2 =>
      do (s,e) <- transl_cexpr e ;
      do s1 <- transl_stmt s1 ;
      do s2 <- transl_stmt s2 ;
      ret (Ssequence (makeseq s) (Sifthenelse e s1 s2))
  | ClightCe.Sloop s1 s2 =>
      do s1 <- transl_stmt s1 ;
      do s2 <- transl_stmt s2 ;
      ret (Sloop s1 s2)
  | ClightCe.Sbreak => ret Sbreak
  | ClightCe.Scontinue => ret Scontinue
  | ClightCe.Sreturn oe => ret (Sreturn oe)
  | ClightCe.Sswitch e ls =>
      do ls <- transl_lblstmt ls ;
      ret (Sswitch e ls)
  | ClightCe.Slabel lb s =>
      do s <- transl_stmt s ;
      ret (Slabel lb s)
  | ClightCe.Sgoto lb => ret (Sgoto lb)
  end
with transl_lblstmt (lb : ClightCe.labeled_statements) : mon labeled_statements  :=
       match lb with
       | ClightCe.LSnil => ret LSnil
       | ClightCe.LScons z s ls  => do s <- transl_stmt s ;
                           do ls <- transl_lblstmt ls ;
                           ret (LScons z s ls)
       end.

(** Translation of a function *)

Definition make_generator (id:ident) :=
  {| gen_next := id ; gen_trail := nil |}.

Definition max_ident (id:ident) (l:list (ident * type)) :=
  List.fold_left (fun acc it => Pos.max acc (fst it)) l id.

Definition fresh_id (f: ClightCe.function)  :=
  (max_ident (max_ident (max_ident xH (ClightCe.fn_params f)) (ClightCe.fn_vars f)) (ClightCe.fn_temps f) + 1)%positive.


Fixpoint temps_of_expr (e:expr) :=
  match e with
  | Econst_int _ _ => nil
  | Econst_float _ _ => nil
  | Econst_single _ _ => nil
  | Econst_long _ _ => nil
  | Eenumlit _ _    => nil
  | Evar _ _ => nil
  | Etempvar id _ => id::nil
  | Ederef e _ => temps_of_expr e
  | Eaddrof e _ => temps_of_expr e
  | Eunop _ e _ => temps_of_expr e
  | Ebinop _ e1 e2 _ => temps_of_expr e1 ++ temps_of_expr e2
  | Ecast e _ => temps_of_expr e
  | Efield e _ _ => temps_of_expr e
  | Esizeof _ _ => nil
  | Ealignof _ _ => nil
  end.

Definition optid_list (o:option ident) : list ident :=
  match o with
  | None => nil
  | Some i => i :: nil
  end.

Definition optexpr_list (o:option expr) : list ident :=
  match o with
  | None => nil
  | Some e => temps_of_expr e
  end.



Fixpoint temps_of_cexpr (e:cexpr) : list ident :=
  match e with
  | CE_expr e => temps_of_expr e
  | CE_and e1 e2 => temps_of_cexpr e1 ++ temps_of_cexpr e2
  | CE_or e1 e2  => temps_of_cexpr e1 ++ temps_of_cexpr e2
  | CE_not e     => temps_of_cexpr e
  end.

  Definition to_list {A B : Type} (F: A -> list B) (l:list A):=
    List.fold_right (fun e acc => F e ++ acc) nil l.

  Fixpoint temps_of_stmt (s:ClightCe.statement) : list ident :=
    match s with
    | ClightCe.Sskip  => nil
    | ClightCe.Sassign e1 e2 => temps_of_expr e1 ++ temps_of_expr e2
    | ClightCe.Sset i e =>  i :: temps_of_expr e
    | ClightCe.Scall  oi e l => optid_list oi ++ temps_of_expr e ++ (to_list temps_of_expr l)
    | ClightCe.Sbuiltin oi _ _ l => optid_list oi ++  to_list temps_of_expr l
    | ClightCe.Ssequence s1 s2 => temps_of_stmt s1 ++ temps_of_stmt s2
  | ClightCe.Sifthenelse c s1 s2 => temps_of_cexpr c ++ temps_of_stmt s1 ++ temps_of_stmt s2
  | ClightCe.Sloop s1 s2 => temps_of_stmt s1 ++ temps_of_stmt s2
  | ClightCe.Sbreak => nil
  | ClightCe.Scontinue => nil
  | ClightCe.Sreturn oe => optexpr_list oe
  | ClightCe.Sswitch  e lb => temps_of_expr e ++ temps_of_lbstmts lb
  | ClightCe.Slabel _ s => temps_of_stmt s
  | ClightCe.Sgoto lb   => nil
  end
with temps_of_lbstmts (l :ClightCe.labeled_statements) :=
         match l with
         | ClightCe.LSnil => nil
         | ClightCe.LScons _ s l => temps_of_stmt s ++ temps_of_lbstmts l
         end.

Definition transl_function (f: ClightCe.function) : res function :=
    let fr := fresh_id f in
    if forallb (fun x => Pos.ltb x fr) (temps_of_stmt f.(ClightCe.fn_body))
    then
      match transl_stmt f.(ClightCe.fn_body) (make_generator (fresh_id f)) with
      | Err msg =>
          Error msg
      | Res tbody g i =>
        OK (mkfunction
              f.(ClightCe.fn_return)
                  f.(ClightCe.fn_callconv)
                      f.(ClightCe.fn_params)
                          f.(ClightCe.fn_vars)
                              (f.(ClightCe.fn_temps) ++ g.(gen_trail))
                              tbody)
      end
    else Error (MSG "Some tempories are not declared" :: nil).

Local Open Scope error_monad_scope.

Definition transl_fundef (fd: ClightCe.fundef) : res fundef :=
  match fd with
  | Internal f =>
      do tf <- transl_function f; OK (Internal tf)
  | External ef targs tres cc =>
      OK (External ef targs tres cc)
  end.

End SIMPL_Cond.

Local Open Scope error_monad_scope.

Definition transl_program (p: ClightCe.program) : res program :=
  do p1 <- AST.transform_partial_program (transl_fundef ) p;
  OK {| prog_defs := AST.prog_defs p1;
        prog_public := AST.prog_public p1;
        prog_main := AST.prog_main p1;
        prog_types := prog_types p;
        prog_comp_env := prog_comp_env p;
        prog_comp_env_eq := prog_comp_env_eq p |}.
