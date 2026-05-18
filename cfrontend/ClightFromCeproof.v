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

(** Correctness proof for expression simplification. *)

From Coq Require Import FunInd.
Require Import Coqlib Maps Errors Integers.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Ctypes Cop Csyntax ClightCe Clight.
Require Import ClightFromCe ClightFromCespec.

(** ** Relational specification of the translation. *)

Definition match_prog (p: ClightCe.program) (tp: Clight.program) :=
  match_program (fun _ f tf => ClightFromCe.transl_fundef f = Errors.OK tf) eq p  tp /\
    prog_types tp = prog_types p.


Lemma transf_program_match:
  forall p tp, transl_program p = OK tp -> match_prog p tp.
Proof.
  unfold transl_program; intros. monadInv H.
  constructor.
  apply match_transform_partial_program.
  destruct x; simpl;auto.
  simpl. reflexivity.
Qed.

(** ** Semantic preservation *)

Section PRESERVATION.

Variable prog: ClightCe.program.
Variable tprog: Clight.program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := ClightCe.globalenv prog.
Let tge := Clight.globalenv tprog.

(** Invariance properties. *)

Lemma comp_env_preserved:
  Clight.genv_cenv tge = ClightCe.genv_cenv ge.
Proof.
  unfold tge, ge. destruct prog, tprog; simpl.
  inv TRANSL. simpl in *.
  congruence.
Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof
  (Genv.find_symbol_transf_partial (proj1 TRANSL)).


Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
  apply (Genv.senv_transf_partial (proj1 TRANSL)).
Qed.

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists  tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof   (Genv.find_funct_ptr_transf_partial (proj1 TRANSL)).

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof.
  apply (Genv.find_funct_transf_partial (proj1 TRANSL)).
Qed.

Ltac destr_if :=
  match goal with
  | |- context[if ?A then ?B else ?C] => destruct A
  end.


Lemma type_of_fundef_preserved:
  forall  f tf, transl_fundef f = OK tf ->
  type_of_fundef tf = ClightCe.type_of_fundef f.
Proof.
  intros until tf. unfold transl_fundef, transf_partial_fundef.
  case f; intro.
  unfold transl_function.
  destr_if; try discriminate.
  case (transl_stmt (ClightCe.fn_body f0) (make_generator (fresh_id f0))); simpl; intros.
  discriminate.
  inversion H. reflexivity.
  intros. inversion H. reflexivity.
Qed.

Lemma function_return_preserved:
  forall f tf, transl_function  f = OK tf ->
  fn_return tf = ClightCe.fn_return f.
Proof.
  intros. unfold transl_function in H.
  revert H.
  destr_if ; try discriminate.
  destruct (transl_stmt (ClightCe.fn_body f)
              (make_generator (fresh_id f))); try discriminate.
  intros. inv H.
  reflexivity.
Qed.

Lemma function_params_preserved:
  forall f tf, transl_function  f = OK tf ->
  fn_params tf = ClightCe.fn_params f.
Proof.
  intros. unfold transl_function in H.
  revert H.
  destr_if ; try discriminate.
  destruct (transl_stmt (ClightCe.fn_body f) ((make_generator (fresh_id f))));
    try discriminate.
  intros.
  inv H. reflexivity.
Qed.

Lemma function_vars_preserved:
  forall f tf, transl_function  f = OK tf ->
  fn_vars tf = ClightCe.fn_vars f.
Proof.
  intros. unfold transl_function in H.
  revert H.
  destr_if ; try discriminate.
  destruct (transl_stmt (ClightCe.fn_body f) ((make_generator (fresh_id f))));
    try discriminate.
  intros.
  inv H. reflexivity.
Qed.

(** Properties of smart constructors. *)

Section TRANSLATION.

(*Variable cunit: Csyntax.program.
Hypothesis LINKORDER: linkorder cunit prog.
Let ce := cunit.(prog_comp_env).

Lemma eval_Ederef':
  forall ge e le m a t l ofs,
  eval_expr ge e le m a (Vptr l ofs) ->
  eval_lvalue ge e le m (Ederef' a t) l ofs Full.
Proof.
  intros. unfold Ederef'; destruct a; auto using eval_Ederef.
  destruct (type_eq t (typeof a)); auto using eval_Ederef.
  inv H.
- auto. 
- inv H0.
Qed.

Lemma typeof_Ederef':
  forall a t, typeof (Ederef' a t) = t.
Proof.
  unfold Ederef'; intros; destruct a; auto. destruct (type_eq t (typeof a)); auto. 
Qed.

Lemma eval_Eaddrof':
  forall ge e le m a t l ofs,
  eval_lvalue ge e le m a l ofs Full ->
  eval_expr ge e le m (Eaddrof' a t) (Vptr l ofs).
Proof.
  intros. unfold Eaddrof'; destruct a; auto using eval_Eaddrof.
  destruct (type_eq t (typeof a)); auto using eval_Eaddrof.
  inv H; auto.
Qed.

Lemma typeof_Eaddrof':
  forall a t, typeof (Eaddrof' a t) = t.
Proof.
  unfold Eaddrof'; intros; destruct a; auto. destruct (type_eq t (typeof a)); auto. 
Qed.

Lemma eval_make_normalize:
  forall ge e le m a n sz sg sg1 attr width,
  0 < width -> width <= bitsize_intsize sz ->
  typeof a = Tint sz sg1 attr ->
  eval_expr ge e le m a (Vint n) ->
  eval_expr ge e le m (make_normalize sz sg width a) (Vint (bitfield_normalize sz sg width n)).
Proof.
  intros. unfold make_normalize, bitfield_normalize.
  assert (bitsize_intsize sz <= Int.zwordsize) by (destruct sz; compute; congruence).
  destruct (intsize_eq sz IBool || signedness_eq sg Unsigned).
- rewrite Int.zero_ext_and by lia. econstructor. eauto. econstructor. 
  rewrite H1; simpl. unfold sem_and, sem_binarith.
  assert (A: exists sg2, classify_binarith (Tint sz sg1 attr) type_int32s = bin_case_i sg2).
  { unfold classify_binarith. unfold type_int32s. destruct sz, sg1; econstructor; eauto. }
  destruct A as (sg2 & A); rewrite A.
  unfold binarith_type.
  assert (B: forall i sz0 sg0 attr0,
             sem_cast (Vint i) (Tint sz0 sg0 attr0) (Tint I32 sg2 noattr) m = Some (Vint i)).
  { intros. unfold sem_cast, classify_cast. destruct Archi.ptr64; reflexivity. }
  unfold type_int32s; rewrite ! B. auto.
- rewrite Int.sign_ext_shr_shl by lia.
  set (amount := Int.repr (Int.zwordsize - width)).
  assert (LT: Int.ltu amount Int.iwordsize = true).
  { unfold Int.ltu. rewrite Int.unsigned_repr_wordsize. apply zlt_true.
    unfold amount; rewrite Int.unsigned_repr. lia.
    assert (Int.zwordsize < Int.max_unsigned) by reflexivity. lia. }
  econstructor.
  econstructor. eauto. econstructor.
  rewrite H1. unfold sem_binary_operation, sem_shl, sem_shift. rewrite LT. destruct sz, sg1; reflexivity.
  econstructor.
  unfold sem_binary_operation, sem_shr, sem_shift. rewrite LT. reflexivity.
Qed.

(** Translation of simple expressions. *)

Lemma tr_simple_nil:
  (forall le dst r sl a tmps, tr_expr ce le dst r sl a tmps ->
   dst = For_val \/ dst = For_effects -> simple r = true -> sl = nil)
/\(forall le rl sl al tmps, tr_exprlist ce le rl sl al tmps ->
   simplelist rl = true -> sl = nil).
Proof.
  assert (A: forall dst a, dst = For_val \/ dst = For_effects -> final dst a = nil).
    intros. destruct H; subst dst; auto.
  apply tr_expr_exprlist; intros; simpl in *; try discriminate; auto.
- rewrite H0; auto. simpl; auto.
- rewrite H0; auto. simpl; auto.
- destruct H1; congruence.
- destruct (andb_prop _ _ H6). inv H1.
    rewrite H0; eauto. simpl; auto.
    unfold chunk_for_volatile_type in H9.
    destruct (type_is_volatile (Csyntax.typeof e1)); simpl in H8; congruence.
- rewrite H0; auto. simpl; auto.
- rewrite H0; auto. simpl; auto.
- destruct (andb_prop _ _ H7). rewrite H0; auto. rewrite H2; auto. simpl; auto.
- rewrite H0; auto. simpl; auto.
- destruct (andb_prop _ _ H6). rewrite H0; auto.
Qed.

Lemma tr_simple_expr_nil:
  forall le dst r sl a tmps, tr_expr ce le dst r sl a tmps ->
  dst = For_val \/ dst = For_effects -> simple r = true -> sl = nil.
Proof (proj1 tr_simple_nil).

Lemma tr_simple_exprlist_nil:
  forall le rl sl al tmps, tr_exprlist ce le rl sl al tmps ->
  simplelist rl = true -> sl = nil.
Proof (proj2 tr_simple_nil).

(** Translation of [deref_loc] and [assign_loc] operations. *)

Remark deref_loc_translated:
  forall ty m b ofs bf t v,
  Csem.deref_loc ge ty m b ofs bf t v ->
  match chunk_for_volatile_type ty bf with
  | None => t = E0 /\ Clight.deref_loc ty m b ofs bf v
  | Some chunk => bf = Full /\ volatile_load tge chunk m b ofs t v
  end.
Proof.
  intros. unfold chunk_for_volatile_type. inv H.
- (* By_value, not volatile *)
  rewrite H1. split; auto. eapply deref_loc_value; eauto.
- (* By_value, volatile *)
  rewrite H0, H1. split; auto. eapply volatile_load_preserved with (ge1 := ge); auto. apply senv_preserved.
- (* By reference *)
  rewrite H0. destruct (type_is_volatile ty); split; auto; eapply deref_loc_reference; eauto.
- (* By copy *)
  rewrite H0. destruct (type_is_volatile ty); split; auto; eapply deref_loc_copy; eauto.
- (* Bitfield *)
  destruct (type_is_volatile ty); [destruct (access_mode ty)|]; auto using deref_loc_bitfield.
Qed.

Remark assign_loc_translated:
  forall ty m b ofs bf v t m' v',
  Csem.assign_loc ge ty m b ofs bf v t m' v' ->
  match chunk_for_volatile_type ty bf with
  | None => t = E0 /\ Clight.assign_loc tge ty m b ofs bf v m'
  | Some chunk => bf = Full /\ volatile_store tge chunk m b ofs v t m'
  end.
Proof.
  intros. unfold chunk_for_volatile_type. inv H.
- (* By_value, not volatile *)
  rewrite H1. split; auto. eapply assign_loc_value; eauto.
- (* By_value, volatile *)
  rewrite H0, H1. split; auto. eapply volatile_store_preserved with (ge1 := ge); auto. apply senv_preserved.
- (* By copy *)
  rewrite H0. rewrite <- comp_env_preserved in *.
  destruct (type_is_volatile ty); split; auto; eapply assign_loc_copy; eauto.
- (* Bitfield *)
  destruct (type_is_volatile ty); [destruct (access_mode ty)|]; eauto using assign_loc_bitfield.
Qed.

(** Bitfield accesses *)

Lemma is_bitfield_access_sound: forall e le m a b ofs bf bf',
  eval_lvalue tge e le m a b ofs bf ->
  tr_is_bitfield_access ce a bf' ->
  bf' = bf.
Proof.
  assert (A: forall id co co',
             tge.(genv_cenv)!id = Some co -> ce!id = Some co' ->
             co' = co /\ complete_members ce (co_members co) = true).
  { intros. rewrite comp_env_preserved in H.
    assert (ge.(Csem.genv_cenv) ! id = Some co') by (apply LINKORDER; auto).
    replace co' with co in * by congruence.
    split; auto. apply co_consistent_complete.
    eapply build_composite_env_consistent. eapply prog_comp_env_eq. eauto.
  } 
  induction 1; simpl; auto.
- rewrite H0. intros (co' & delta' & E1 & E2). rewrite comp_env_preserved in H2.
  exploit A; eauto. intros (E3 & E4). subst co'.
  assert (field_offset ge i (co_members co) = field_offset ce i (co_members co)).
  { apply field_offset_stable. apply LINKORDER. auto. }
  congruence.
- rewrite H0. intros (co' & delta' & E1 & E2). rewrite comp_env_preserved in H2.
  exploit A; eauto. intros (E3 & E4). subst co'.
  assert (union_field_offset ge i (co_members co) = union_field_offset ce i (co_members co)).
  { apply union_field_offset_stable. apply LINKORDER. auto. }
  congruence.
Qed.

Lemma make_assign_value_sound:
  forall ty m b ofs bf v t m' v',
  Csem.assign_loc ge ty m b ofs bf v t m' v' ->
  forall tge e le m'' r,
  typeof r = ty ->
  eval_expr tge e le m'' r v ->
  eval_expr tge e le m'' (make_assign_value bf r) v'.
Proof.
  unfold make_assign_value; destruct 1; intros; auto.
  inv H. eapply eval_make_normalize; eauto; lia.
Qed.

Lemma typeof_make_assign_value: forall bf r,
  typeof (make_assign_value bf r) = typeof r.
Proof.
  intros. destruct bf; simpl; auto. unfold make_normalize.
  destruct (intsize_eq sz IBool || signedness_eq sg Unsigned); auto.
Qed.

(** Evaluation of simple expressions and of their translation *)

Lemma tr_simple:
 forall e m,
 (forall r v,
  eval_simple_rvalue ge e m r v ->
  forall le dst sl a tmps,
  tr_expr ce le dst r sl a tmps ->
  match dst with
  | For_val => sl = nil /\ Csyntax.typeof r = typeof a /\ eval_expr tge e le m a v
  | For_effects => sl = nil
  | For_set sd =>
      exists b, sl = do_set sd b
             /\ Csyntax.typeof r = typeof b
             /\ eval_expr tge e le m b v
  end)
/\
 (forall l b ofs bf,
  eval_simple_lvalue ge e m l b ofs bf ->
  forall le sl a tmps,
  tr_expr ce le For_val l sl a tmps ->
  sl = nil /\ Csyntax.typeof l = typeof a /\ eval_lvalue tge e le m a b ofs bf).
Proof.
Opaque makeif.
  intros e m.
  apply (eval_simple_rvalue_lvalue_ind ge e m); intros until tmps; intros TR; inv TR.
- (* value *)
  auto.
- auto.
- exists a0; auto.
- (* rvalof *)
  inv H7; try congruence.
  exploit H0; eauto. intros [A [B C]].
  subst sl1; simpl.
  assert (eval_expr tge e le m a v).
    eapply eval_Elvalue. eauto.
    rewrite <- B.
    exploit deref_loc_translated; eauto. unfold chunk_for_volatile_type; rewrite H2. tauto.
  destruct dst; auto.
  econstructor. split. simpl; eauto. auto.
- (* addrof *)
  exploit H0; eauto. intros [A [B C]].
  subst sl1; simpl.
  assert (eval_expr tge e le m (Eaddrof' a1 ty) (Vptr b ofs)) by (apply eval_Eaddrof'; auto).
  assert (typeof (Eaddrof' a1 ty) = ty) by (apply typeof_Eaddrof').
  destruct dst; auto. simpl; econstructor; eauto.  
- (* unop *)
  exploit H0; eauto. intros [A [B C]].
  subst sl1; simpl.
  assert (eval_expr tge e le m (Eunop op a1 ty) v). econstructor; eauto. congruence.
  destruct dst; auto. simpl; econstructor; eauto.
- (* binop *)
  exploit H0; eauto. intros [A [B C]].
  exploit H2; eauto. intros [D [E F]].
  subst sl1 sl2; simpl.
  assert (eval_expr tge e le m (Ebinop op a1 a2 ty) v). econstructor; eauto. rewrite comp_env_preserved; congruence.
  destruct dst; auto. simpl; econstructor; eauto.
- (* cast effects *)
  exploit H0; eauto.
- (* cast val *)
  exploit H0; eauto. intros [A [B C]].
  subst sl1; simpl.
  assert (eval_expr tge e le m (Ecast a1 ty) v). econstructor; eauto. congruence.
  destruct dst; auto. simpl; econstructor; eauto.
- (* sizeof *)
  rewrite <- comp_env_preserved.
  destruct dst.
  split; auto. split; auto. constructor.
  auto.
  exists (Esizeof ty1 ty). split. auto. split. auto. constructor.
- (* alignof *)
  rewrite <- comp_env_preserved.
  destruct dst.
  split; auto. split; auto. constructor.
  auto.
  exists (Ealignof ty1 ty). split. auto. split. auto. constructor.
- (* var local *)
  split; auto. split; auto. apply eval_Evar_local; auto.
- (* var global *)
  split; auto. split; auto. apply eval_Evar_global; auto.
    rewrite symbols_preserved; auto.
- (* deref *)
  exploit H0; eauto. intros [A [B C]]. subst sl1.
  split; auto. split. rewrite typeof_Ederef'; auto. apply eval_Ederef'; auto. 
- (* field struct *)
  rewrite <- comp_env_preserved in *.
  exploit H0; eauto. intros [A [B C]]. subst sl1.
  split; auto. split; auto. rewrite B in H1. eapply eval_Efield_struct; eauto.
- (* field union *)
  rewrite <- comp_env_preserved in *.
  exploit H0; eauto. intros [A [B C]]. subst sl1.
  split; auto. split; auto. rewrite B in H1. eapply eval_Efield_union; eauto.
Qed.

Lemma tr_simple_rvalue:
  forall e m r v,
  eval_simple_rvalue ge e m r v ->
  forall le dst sl a tmps,
  tr_expr ce le dst r sl a tmps ->
  match dst with
  | For_val => sl = nil /\ Csyntax.typeof r = typeof a /\ eval_expr tge e le m a v
  | For_effects => sl = nil
  | For_set sd =>
      exists b, sl = do_set sd b
             /\ Csyntax.typeof r = typeof b
             /\ eval_expr tge e le m b v
  end.
Proof.
  intros e m. exact (proj1 (tr_simple e m)).
Qed.

Lemma tr_simple_lvalue:
  forall e m l b ofs bf,
  eval_simple_lvalue ge e m l b ofs bf ->
  forall le sl a tmps,
  tr_expr ce le For_val l sl a tmps ->
  sl = nil /\ Csyntax.typeof l = typeof a /\ eval_lvalue tge e le m a b ofs bf.
Proof.
  intros e m. exact (proj2 (tr_simple e m)).
Qed.

Lemma tr_simple_exprlist:
  forall le rl sl al tmps,
  tr_exprlist ce le rl sl al tmps ->
  forall e m tyl vl,
  eval_simple_list ge e m rl tyl vl ->
  sl = nil /\ eval_exprlist tge e le m al tyl vl.
Proof.
  induction 1; intros.
  inv H. split. auto. constructor.
  inv H4.
  exploit tr_simple_rvalue; eauto. intros [A [B C]].
  exploit IHtr_exprlist; eauto. intros [D E].
  split. subst; auto. econstructor; eauto. congruence.
Qed.

(** Commutation between the translation of expressions and left contexts. *)

Lemma typeof_context:
  forall k1 k2 C, leftcontext k1 k2 C ->
  forall e1 e2, Csyntax.typeof e1 = Csyntax.typeof e2 ->
  Csyntax.typeof (C e1) = Csyntax.typeof (C e2).
Proof.
  induction 1; intros; auto.
Qed.

Scheme leftcontext_ind2 := Minimality for leftcontext Sort Prop
  with leftcontextlist_ind2 := Minimality for leftcontextlist Sort Prop.
Combined Scheme leftcontext_leftcontextlist_ind from leftcontext_ind2, leftcontextlist_ind2.

Lemma tr_expr_leftcontext_rec:
 (
  forall from to C, leftcontext from to C ->
  forall le e dst sl a tmps,
  tr_expr ce le dst (C e) sl a tmps ->
  exists dst', exists sl1, exists sl2, exists a', exists tmp',
  tr_expr ce le dst' e sl1 a' tmp'
  /\ sl = sl1 ++ sl2
  /\ incl tmp' tmps
  /\ (forall le' e' sl3,
        tr_expr ce le' dst' e' sl3 a' tmp' ->
        (forall id, ~In id tmp' -> le'!id = le!id) ->
        Csyntax.typeof e' = Csyntax.typeof e ->
        tr_expr ce le' dst (C e') (sl3 ++ sl2) a tmps)
 ) /\ (
  forall from C, leftcontextlist from C ->
  forall le e sl a tmps,
  tr_exprlist ce le (C e) sl a tmps ->
  exists dst', exists sl1, exists sl2, exists a', exists tmp',
  tr_expr ce le dst' e sl1 a' tmp'
  /\ sl = sl1 ++ sl2
  /\ incl tmp' tmps
  /\ (forall le' e' sl3,
        tr_expr ce le' dst' e' sl3 a' tmp' ->
        (forall id, ~In id tmp' -> le'!id = le!id) ->
        Csyntax.typeof e' = Csyntax.typeof e ->
        tr_exprlist ce le' (C e') (sl3 ++ sl2) a tmps)
).
Proof.

Ltac TR :=
  econstructor; econstructor; econstructor; econstructor; econstructor;
  split; [eauto | split; [idtac | split]].

Ltac NOTIN :=
  match goal with
  | [ H1: In ?x ?l, H2: list_disjoint ?l _ |- ~In ?x _ ] =>
        red; intro; elim (H2 x x); auto; fail
  | [ H1: In ?x ?l, H2: list_disjoint _ ?l |- ~In ?x _ ] =>
        red; intro; elim (H2 x x); auto; fail
  end.

Ltac UNCHANGED :=
  match goal with
  | [ H: (forall (id: ident), ~In id _ -> ?le' ! id = ?le ! id) |-
         (forall (id: ident), In id _ -> ?le' ! id = ?le ! id) ] =>
      intros; apply H; NOTIN
  end.

  (*generalize compat_dest_change; intro CDC.*)
  apply leftcontext_leftcontextlist_ind; intros.

- (* base *)
  TR. rewrite app_nil_r; auto. red; auto.
  intros. rewrite app_nil_r; auto.
- (* deref *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. auto.
  intros. rewrite <- app_ass. econstructor; eauto.
- (* field *)
  inv H1.
  exploit H0. eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. auto.
  intros. rewrite <- app_ass. econstructor; eauto.
- (* rvalof *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. red; eauto.
  intros. rewrite <- app_ass; econstructor; eauto.
  exploit typeof_context; eauto. congruence.
- (* addrof *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. auto.
  intros. rewrite <- app_ass. econstructor; eauto.
- (* unop *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. auto.
  intros. rewrite <- app_ass. econstructor; eauto.
- (* binop left *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor; eauto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
- (* binop right *)
  inv H2.
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl3 ++ sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor; eauto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
- (* cast *)
  inv H1.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. eauto. auto. 
  intros. econstructor; eauto.
+ (* generic *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto. auto. 
  intros. rewrite <- app_ass. econstructor; eauto.
- (* seqand *)
  inv H1.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto.
+ (* for set *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
- (* seqor *)
  inv H1.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto.
+ (* for set *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
- (* condition *)
  inv H1.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto. auto. auto.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. eapply tr_condition_effects. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto. auto.
+ (* for set *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. eapply tr_condition_set. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto. auto. auto.
- (* assign left *)
  inv H1.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto. auto. auto.
  eapply typeof_context. eauto. auto. eauto.
  auto.
- (* assign right *)
  inv H2.
+ (* for effects *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl3 ++ sl2') with (nil ++ (sl3 ++ sl2')). rewrite app_ass.
  econstructor.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. auto. auto. auto. auto.
+ (* for val *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl3 ++ sl2') with (nil ++ (sl3 ++ sl2')). rewrite app_ass.
  econstructor.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. auto. auto. auto. auto. auto. auto. auto.
  eapply typeof_context; eauto. auto.
- (* assignop left *)
  inv H1.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  symmetry; eapply typeof_context; eauto. eauto.
  auto. auto. auto. auto. auto. auto. auto.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  eauto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  eapply typeof_context; eauto. auto.
- (* assignop right *)
  inv H2.
+ (* for effects *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl0 ++ sl2') with (nil ++ sl0 ++ sl2'). rewrite app_ass. econstructor.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. auto. eauto. auto. auto. auto. auto. auto. auto. auto.
+ (* for val *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl0 ++ sl2') with (nil ++ sl0 ++ sl2'). rewrite app_ass. econstructor.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. eauto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
- (* postincr *)
  inv H1.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto.
  intros. rewrite <- app_ass. econstructor; eauto.
  symmetry; eapply typeof_context; eauto.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto.
  intros. rewrite <- app_ass. econstructor; eauto.
  eapply typeof_context; eauto.
- (* call left *)
  inv H1.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_exprlist_invariant; eauto. UNCHANGED.
  auto. auto. auto.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto.
  intros. rewrite <- app_ass. econstructor. auto. apply S; auto.
  eapply tr_exprlist_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
- (* call right *)
  inv H2.
+ (* for effects *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto.
  (*destruct dst'; constructor||contradiction.*)
  red; auto.
  intros. rewrite <- app_ass. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. auto. auto. auto.
+ (* for val *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto.
  (*destruct dst'; constructor||contradiction.*)
  red; auto.
  intros. rewrite <- app_ass. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor.
  auto. eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto.
  auto. auto. auto. auto.
- (* builtin *)
  inv H1.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor.
  apply S; auto. auto.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor.
  auto. apply S; auto. auto. auto.
- (* comma *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto.
- (* paren *)
  inv H1.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q. eauto. red; auto.
  intros. econstructor; eauto.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q. eauto. auto.
  intros. econstructor; eauto.
+ (* for set *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q. eauto. auto.
  intros. econstructor; eauto.
- (* cons left *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_exprlist_invariant; eauto.  UNCHANGED.
  auto. auto. auto.
- (* cons right *)
  inv H2.
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. eauto.
  red; auto.
  intros. change sl3 with (nil ++ sl3). rewrite app_ass. econstructor.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto.
  auto. auto. auto.
Qed.

Theorem tr_expr_leftcontext:
  forall C le r dst sl a tmps,
  leftcontext RV RV C ->
  tr_expr ce le dst (C r) sl a tmps ->
  exists dst', exists sl1, exists sl2, exists a', exists tmp',
  tr_expr ce le dst' r sl1 a' tmp'
  /\ sl = sl1 ++ sl2
  /\ incl tmp' tmps
  /\ (forall le' r' sl3,
        tr_expr ce le' dst' r' sl3 a' tmp' ->
        (forall id, ~In id tmp' -> le'!id = le!id) ->
        Csyntax.typeof r' = Csyntax.typeof r ->
        tr_expr ce le' dst (C r') (sl3 ++ sl2) a tmps).
Proof.
  intros. eapply (proj1 tr_expr_leftcontext_rec); eauto.
Qed.

Theorem tr_top_leftcontext:
  forall e le m dst rtop sl a tmps,
  tr_top ce tge e le m dst rtop sl a tmps ->
  forall r C,
  rtop = C r ->
  leftcontext RV RV C ->
  exists dst', exists sl1, exists sl2, exists a', exists tmp',
  tr_top ce tge e le m dst' r sl1 a' tmp'
  /\ sl = sl1 ++ sl2
  /\ incl tmp' tmps
  /\ (forall le' m' r' sl3,
        tr_expr ce le' dst' r' sl3 a' tmp' ->
        (forall id, ~In id tmp' -> le'!id = le!id) ->
        Csyntax.typeof r' = Csyntax.typeof r ->
        tr_top ce tge e le' m' dst (C r') (sl3 ++ sl2) a tmps).
Proof.
  induction 1; intros.
(* val for val *)
  inv H2; inv H1.
  exists For_val; econstructor; econstructor; econstructor; econstructor.
  split. apply tr_top_val_val; eauto.
  split. instantiate (1 := nil); auto.
  split. apply incl_refl.
  intros. rewrite app_nil_r. constructor; auto.
(* base *)
  subst r. exploit tr_expr_leftcontext; eauto.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  exists dst'; exists sl1; exists sl2; exists a'; exists tmp'.
  split. apply tr_top_base; auto.
  split. auto. split. auto.
  intros. apply tr_top_base. apply S; auto.
Qed.
 *)

(** Semantics of smart constructors *)

Remark sem_cast_deterministic:
  forall v ty ty' m1 v1 m2 v2,
  sem_cast v ty ty' m1 = Some v1 ->
  sem_cast v ty ty' m2 = Some v2 ->
  v1 = v2.
Proof.
  unfold sem_cast; intros. destruct (classify_cast ty ty'); try congruence.
- destruct v; try congruence.
  destruct Archi.ptr64; try discriminate.
  destruct (Mem.weak_valid_pointer m1 b (Ptrofs.unsigned i)); inv H.
  destruct (Mem.weak_valid_pointer m2 b (Ptrofs.unsigned i)); inv H0.
  auto.
- destruct v; try congruence. 
  destruct (negb Archi.ptr64); try discriminate.
  destruct (Mem.weak_valid_pointer m1 b (Ptrofs.unsigned i)); inv H.
  destruct (Mem.weak_valid_pointer m2 b (Ptrofs.unsigned i)); inv H0.
  auto.
Qed.


Lemma eval_simpl_expr_sound:
  forall e le m a v, eval_expr tge e le m a v ->
  match eval_simpl_expr a with Some v' => v' = v | None => True end.
Proof.
  induction 1; simpl; auto.
  destruct (eval_simpl_expr a); auto. subst.
  destruct (sem_cast v1 (typeof a) ty Mem.empty) as [v'|] eqn:C; auto.
  eapply sem_cast_deterministic; eauto.
  inv H; simpl; auto.
Qed.

Lemma static_bool_val_sound:
  forall v t m b, bool_val v t Mem.empty = Some b -> bool_val v t m = Some b.
Proof.
  intros until b; unfold bool_val.
  destruct (classify_bool t); destruct v; destruct Archi.ptr64 eqn:SF; auto;
  simpl; congruence.
Qed.

Lemma step_makeif:
  forall f a s1 s2 k e le m v1 b,
  eval_expr tge e le m a v1 ->
  bool_val v1 (typeof a) m = Some b ->
  star step1 tge (State f (makeif a s1 s2) k e le m)
             E0 (State f (if b then s1 else s2) k e le m).
Proof.
  intros. functional induction (makeif a s1 s2).
- exploit eval_simpl_expr_sound; eauto. rewrite e0. intro EQ; subst v.
  assert (bool_val v1 (typeof a) m = Some true) by (apply static_bool_val_sound; auto).
  replace b with true by congruence. constructor.
- exploit eval_simpl_expr_sound; eauto. rewrite e0. intro EQ; subst v.
  assert (bool_val v1 (typeof a) m = Some false) by (apply static_bool_val_sound; auto).
  replace b with false by congruence. constructor.
- apply star_one. eapply step_ifthenelse; eauto.
- apply star_one. eapply step_ifthenelse; eauto.
Qed.

(*
Lemma step_make_set:
  forall id a ty m b ofs bf t v e le f k,
  Csem.deref_loc ge ty m b ofs bf t v ->
  eval_lvalue tge e le m a b ofs bf ->
  typeof a = ty ->
  step1 tge (State f (make_set bf id a) k e le m)
          t (State f Sskip k e (PTree.set id v le) m).
Proof.
  intros. exploit deref_loc_translated; eauto. rewrite <- H1.
  unfold make_set. destruct (chunk_for_volatile_type (typeof a) bf) as [chunk|].
(* volatile case *)
  intros [A B]. subst bf.
  change (PTree.set id v le) with (set_opttemp (Some id) v le). econstructor.
  econstructor. constructor. eauto.
  simpl. unfold sem_cast. simpl. eauto. constructor.
  simpl. econstructor; eauto.
(* nonvolatile case *)
  intros [A B]. subst t. constructor. eapply eval_Elvalue; eauto.
Qed.

Lemma step_make_assign:
  forall a1 a2 ty m b ofs bf t v m' v' v2 e le f k,
  Csem.assign_loc ge ty m b ofs bf v t m' v' ->
  eval_lvalue tge e le m a1 b ofs bf ->
  eval_expr tge e le m a2 v2 ->
  sem_cast v2 (typeof a2) ty m = Some v ->
  typeof a1 = ty ->
  step1 tge (State f (make_assign bf a1 a2) k e le m)
          t (State f Sskip k e le m').
Proof.
  intros. exploit assign_loc_translated; eauto. rewrite <- H3.
  unfold make_assign. destruct (chunk_for_volatile_type (typeof a1) bf) as [chunk|].
(* volatile case *)
  intros [A B]. subst bf. change le with (set_opttemp None Vundef le) at 2. econstructor.
  econstructor. constructor. eauto.
  simpl. unfold sem_cast. simpl. eauto.
  econstructor; eauto. rewrite H3; eauto. constructor.
  simpl. econstructor; eauto.
(* nonvolatile case *)
  intros [A B]. subst t. econstructor; eauto. congruence.
Qed.
*)

Fixpoint Kseqlist (sl: list statement) (k: cont) :=
  match sl with
  | nil => k
  | s :: l => Kseq s (Kseqlist l k)
  end.

Remark Kseqlist_app:
  forall sl1 sl2 k,
  Kseqlist (sl1 ++ sl2) k = Kseqlist sl1 (Kseqlist sl2 k).
Proof.
  induction sl1; simpl; congruence.
Qed.

Lemma push_seq:
  forall f sl k e le m,
  star step1 tge (State f (makeseq sl) k e le m)
              E0 (State f Sskip (Kseqlist sl k) e le m).
Proof.
  intros. unfold makeseq. generalize Sskip. revert sl k.
  induction sl; simpl; intros.
  apply star_refl.
  eapply star_right. apply IHsl. constructor. traceEq.
Qed.

(*
Lemma step_tr_rvalof:
  forall ty m b ofs bf t v e le a sl a' tmp f k,
  Csem.deref_loc ge ty m b ofs bf t v ->
  eval_lvalue tge e le m a b ofs bf ->
  tr_rvalof ce ty a sl a' tmp ->
  typeof a = ty ->
  exists le',
    star step1 tge (State f Sskip (Kseqlist sl k) e le m)
                 t (State f Sskip k e le' m)
  /\ eval_expr tge e le' m a' v
  /\ typeof a' = typeof a
  /\ forall x, ~In x tmp -> le'!x = le!x.
Proof.
  intros. inv H1.
  (* not volatile *)
  exploit deref_loc_translated; eauto. unfold chunk_for_volatile_type; rewrite H3.
  intros [A B]. subst t.
  exists le; split. apply star_refl.
  split. eapply eval_Elvalue; eauto.
  auto.
  (* volatile *)
  intros.
  exploit is_bitfield_access_sound; eauto. intros EQ; subst bf0. 
  exists (PTree.set t0 v le); split.
  simpl. eapply star_two. econstructor. eapply step_make_set; eauto. traceEq.
  split. constructor. apply PTree.gss.
  split. auto.
  intros. apply PTree.gso. congruence.
Qed.
 *)

End TRANSLATION.


(** Matching between continuations *)
Definition  match_temp (fr: ident) (t t':temp_env) : Prop :=
  (forall x v, t ! x = Some v -> t' ! x = Some v ) /\
    (forall x, Ple fr x ->  t ! x = None).

Definition all_fresh (fr:ident) (l:list ident) :=
  forall x, In x l -> Ple fr x.

Definition all_below (fr:ident) (l:list ident) :=
  forall x, In x l -> Plt x fr.

Definition Pltopt  (o:option ident)  (fr:ident) :=
  match o with
  | None => True
  | Some i => Plt i fr
  end.


Inductive match_cont : ident -> ClightCe.cont -> cont -> Prop :=
  | match_Kstop: forall fr,
      match_cont fr ClightCe.Kstop Kstop
  | match_Kseq: forall fr s k ts tk tmp,
      all_fresh fr tmp ->
      all_below fr (temps_of_stmt s) ->
      tr_stmt s ts tmp ->
      match_cont fr k tk ->
      match_cont fr (ClightCe.Kseq s k) (Kseq ts tk)
  | match_Kswitch: forall fr k tk,
      match_cont fr k tk ->
      match_cont  fr (ClightCe.Kswitch k) (Kswitch tk)
  | match_Kcall: forall fr f tf i e le le' k tk ,
      transl_function  f = OK tf ->
      match_temp (fresh_id f) le le' ->
      match_cont  (fresh_id f) k tk ->
      Pltopt i (fresh_id f) ->
      match_cont fr (ClightCe.Kcall i f e le k)
        (Kcall i  tf e le' tk)
| match_Kloop1 : forall fr s1 s2 k ts1 ts2 tk tmp1 tmp2,
    match_cont fr k tk ->
    all_fresh fr tmp1 ->
    all_fresh fr tmp2 ->
    all_below fr (temps_of_stmt s1) ->
    all_below fr (temps_of_stmt s2) ->
    tr_stmt s1 ts1 tmp1 ->
    tr_stmt s2 ts2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    match_cont fr (ClightCe.Kloop1 s1 s2 k) (Kloop1 ts1 ts2 tk)
| match_Kloop2 : forall fr s1 s2 k ts1 ts2 tk tmp1 tmp2,
    match_cont fr k tk ->
    all_fresh fr tmp1 ->
    all_fresh fr tmp2 ->
    all_below fr (temps_of_stmt s1) ->
    all_below fr (temps_of_stmt s2) ->
    tr_stmt s1 ts1 tmp1 ->
    tr_stmt s2 ts2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    match_cont fr (ClightCe.Kloop2 s1 s2 k) (Kloop2 ts1 ts2 tk)
.





(*Lemma match_cont_is_call_cont:
  forall k tk,
  match_cont k tk -> ClightCe.is_call_cont k ->
  forall ce', match_cont ce' k tk.
Proof.
  destruct 1; simpl; intros; try contradiction; econstructor; eauto.
Qed. 

Lemma match_cont_call_cont:
  forall ce k tk,
  match_cont ce k tk ->
  forall ce', match_cont ce' (ClightCe.call_cont k) (call_cont tk).
Proof.
  induction 1; simpl; auto; intros; econstructor; eauto.
Qed.
*)
(** Matching between states *)
Inductive fresh_of_fundef : ClightCe.fundef -> ident -> Prop :=
| fresh_internal : forall f,
    fresh_of_fundef (Internal f) (fresh_id f)
| fresh_external : forall f lt t cc fr,
    fresh_of_fundef (External f lt  t cc) fr.





Inductive match_states: ClightCe.state -> state -> Prop :=
  | match_state: forall f s k e m tf ts tk le le' tmp
      (TRF: transl_function  f = OK tf)
      (fr := fresh_id f)
      (TEMPS : all_below fr (temps_of_stmt s))
      (ME : match_temp fr le le')
      (TR: tr_stmt s ts tmp)
      (DIS : all_fresh fr tmp)
      (MK: match_cont fr k tk),
      match_states (ClightCe.State f s k e le m)
                   (State tf ts tk e le' m)
| match_callstates: forall fr fd args k m tfd tk
                           (TR: transl_fundef fd = OK tfd)
                           (FR : fresh_of_fundef fd fr)
                           (MK: match_cont fr k tk),
      match_states (ClightCe.Callstate fd args k m)
        (Callstate tfd args tk m)
| match_returnstates: forall fr res k m tk
                             (MK: match_cont fr k tk),
    match_states (ClightCe.Returnstate res k m)
      (Returnstate res tk m).

(** Additional results on translation of statements *)

(*Lemma tr_select_switch:
  forall ce n ls tls,
  tr_lblstmts ce ls tls ->
  tr_lblstmts ce (ClightCe.select_switch n ls) (select_switch n tls).
Proof.
  intros ce.
  assert (DFL: forall ls tls,
      tr_lblstmts ce ls tls ->
      tr_lblstmts ce (ClightCe.select_switch_default ls) (select_switch_default tls)).
  { induction 1; simpl. constructor. destruct c; auto. constructor; auto. }
  assert (CASE: forall n ls tls,
      tr_lblstmts ce ls tls ->
      match ClightCe.select_switch_case n ls with
      | None =>
          select_switch_case n tls = None
      | Some ls' =>
          exists tls', select_switch_case n tls = Some tls' /\ tr_lblstmts ce ls' tls'
      end).
  { induction 1; simpl; intros.
    auto.
    destruct c; auto. destruct (zeq z n); auto.
    econstructor; split; eauto. constructor; auto. }
  intros. unfold ClightCe.select_switch, select_switch.
  specialize (CASE n ls tls H).
  destruct (ClightCe.select_switch_case n ls) as [ls'|].
  destruct CASE as [tls' [P Q]]. rewrite P. auto.
  rewrite CASE. apply DFL; auto.
Qed.

Lemma tr_seq_of_labeled_statement:
  forall ce ls tls,
  tr_lblstmts ce ls tls ->
  tr_stmt ce (ClightCe.seq_of_labeled_statement ls) (seq_of_labeled_statement tls).
Proof.
  induction 1; simpl; constructor; auto.
Qed.
 *)

(** Commutation between translation and the "find label" operation. *)

Section FIND_LABEL.

Variable ce: composite_env.
Variable lbl: label.

Definition nolabel (s: statement) : Prop :=
  forall k, find_label lbl s k = None.

Fixpoint nolabel_list (sl: list statement) : Prop :=
  match sl with
  | nil => True
  | s1 :: sl' => nolabel s1 /\ nolabel_list sl'
  end.

Lemma nolabel_list_app:
  forall sl2 sl1, nolabel_list sl1 -> nolabel_list sl2 -> nolabel_list (sl1 ++ sl2).
Proof.
  induction sl1; simpl; intros. auto. tauto.
Qed.

Lemma makeseq_nolabel:
  forall sl, nolabel_list sl -> nolabel (makeseq sl).
Proof.
  assert (forall sl s, nolabel s -> nolabel_list sl -> nolabel (makeseq_rec s sl)).
  induction sl; simpl; intros. auto. destruct H0. apply IHsl; auto.
  red. intros; simpl. rewrite H. apply H0.
  intros. unfold makeseq. apply H; auto. red. auto.
Qed.

Lemma makeif_nolabel:
  forall a s1 s2, nolabel s1 -> nolabel s2 -> nolabel (makeif a s1 s2).
Proof.
  intros. functional induction (makeif a s1 s2); auto.
  red; simpl; intros. rewrite H; auto.
  red; simpl; intros. rewrite H; auto.
Qed.

Lemma nolabel_seq : forall s1 s2,
    nolabel s1 ->
    nolabel s2 ->
    nolabel (Ssequence s1 s2).
Proof.
  unfold nolabel.
  simpl. intros.
  rewrite H. auto.
Qed.

(*Lemma make_set_nolabel:
  forall bf t a, nolabel (make_set bf t a).
Proof.
  unfold make_set; intros; red; intros.
  destruct (chunk_for_volatile_type (typeof a) bf); auto.
Qed.
 *)

(*Lemma make_assign_nolabel:
  forall bf l r, nolabel (make_assign bf l r).
Proof.
  unfold make_assign; intros; red; intros.
  destruct (chunk_for_volatile_type (typeof l) bf); auto.
Qed.
*)
(*Lemma tr_rvalof_nolabel:
  forall ce ty a sl a' tmp, tr_rvalof ce ty a sl a' tmp -> nolabel_list sl.
Proof.
  destruct 1; simpl; intuition. apply make_set_nolabel.
Qed.

Lemma nolabel_do_set:
  forall sd a, nolabel_list (do_set sd a).
Proof.
  induction sd; intros; simpl; split; auto; red; auto.
Qed.

Lemma nolabel_final:
  forall dst a, nolabel_list (final dst a).
Proof.
  destruct dst; simpl; intros. auto. auto. apply nolabel_do_set.
Qed.
 *)

Ltac NoLabelTac :=
  match goal with
  | [ |- nolabel_list nil ] => exact I
(*  | [ |- nolabel_list (final _ _) ] => apply nolabel_final (*; NoLabelTac*)*)
  | [ |- nolabel_list (_ :: _) ] => simpl; split; NoLabelTac
  | [ |- nolabel_list (_ ++ _) ] => apply nolabel_list_app; NoLabelTac
  | [ H: _ -> nolabel_list ?x |- nolabel_list ?x ] => apply H; NoLabelTac
  | [ |- nolabel (makeseq _) ] => apply makeseq_nolabel; NoLabelTac
  | [ |- nolabel (makeif _ _ _) ] => apply makeif_nolabel; NoLabelTac
(*  | [ |- nolabel (make_set _ _ _) ] => apply make_set_nolabel*)
(*  | [ |- nolabel (make_assign _ _ _) ] => apply make_assign_nolabel*)
  | [ |- nolabel _ ] => red; intros; simpl; auto
  | [ |- _ /\ _ ] => split; NoLabelTac
  | _ => auto
  end.

(*
Lemma tr_find_label_expr:
  (forall le dst r sl a tmps, tr_expr ce le dst r sl a tmps -> nolabel_list sl)
/\(forall le rl sl al tmps, tr_exprlist ce le rl sl al tmps -> nolabel_list sl).
Proof.
  apply tr_expr_exprlist; intros; NoLabelTac.
  apply nolabel_do_set.
  eapply tr_rvalof_nolabel; eauto.
  apply nolabel_do_set.
  apply nolabel_do_set.
  eapply tr_rvalof_nolabel; eauto.
  eapply tr_rvalof_nolabel; eauto.
  eapply tr_rvalof_nolabel; eauto.
Qed.

Lemma tr_find_label_top:
  forall e le m dst r sl a tmps,
  tr_top ce tge e le m dst r sl a tmps -> nolabel_list sl.
Proof.
  induction 1; intros; NoLabelTac.
  eapply (proj1 tr_find_label_expr); eauto.
Qed.

Lemma tr_find_label_expression:
  forall r s a, tr_expression ce r s a -> forall k, find_label lbl s k = None.
Proof.
  intros. inv H.
  assert (nolabel (makeseq sl)). apply makeseq_nolabel.
  eapply tr_find_label_top with (e := empty_env) (le := PTree.empty val) (m := Mem.empty).
  eauto. apply H.
Qed.

Lemma tr_find_label_expr_stmt:
  forall r s, tr_expr_stmt ce r s -> forall k, find_label lbl s k = None.
Proof.
  intros. inv H.
  assert (nolabel (makeseq sl)). apply makeseq_nolabel.
  eapply tr_find_label_top with (e := empty_env) (le := PTree.empty val) (m := Mem.empty).
  eauto. apply H.
Qed.

Lemma tr_find_label_if:
  forall r s,
  tr_if ce r Sskip Sbreak s ->
  forall k, find_label lbl s k = None.
Proof.
  intros. inv H.
  assert (nolabel (makeseq (sl ++ makeif a Sskip Sbreak :: nil))).
  apply makeseq_nolabel.
  apply nolabel_list_app.
  eapply tr_find_label_top with (e := empty_env) (le := PTree.empty val) (m := Mem.empty).
  eauto.
  simpl; split; auto. apply makeif_nolabel. red; simpl; auto. red; simpl; auto.
  apply H.
Qed.
 *)
(*
Lemma tr_find_label:
  forall s k ts tk
    (TR: tr_stmt s ts)
    (MC: match_cont k tk),
  match ClightCe.find_label lbl s k with
  | None =>
      find_label lbl ts tk = None
  | Some (s', k') =>
      exists ts', exists tk',
          find_label lbl ts tk = Some (ts', tk')
       /\ tr_stmt s' ts'
       /\ match_cont k' tk'
  end
with tr_find_label_ls:
  forall s k ts tk
    (TR: tr_lblstmts s ts)
    (MC: match_cont k tk),
  match ClightCe.find_label_ls lbl s k with
  | None =>
      find_label_ls lbl ts tk = None
  | Some (s', k') =>
      exists ts', exists tk',
          find_label_ls lbl ts tk = Some (ts', tk')
       /\ tr_stmt s' ts'
       /\ match_cont k' tk'
  end.
Proof.
  induction s; intros; inversion TR; subst; clear TR; simpl; auto.

  exploit IHs1; eauto.



  auto.
  eapply tr_find_label_expr_stmt; eauto.
(* seq *)
  exploit (IHs1 (ClightCe.Kseq s2 k)); eauto. constructor; eauto.
  destruct (ClightCe.find_label lbl s1 (ClightCe.Kseq s2 k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; auto.
  intro EQ. rewrite EQ. eapply IHs2; eauto.
(* if empty *)
  rename s' into sr.
  rewrite (tr_find_label_expression _ _ _ H3).
  auto.
(* if not empty *)
  rename s' into sr.
  rewrite (tr_find_label_expression _ _ _ H2).
  exploit (IHs1 k); eauto.
  destruct (ClightCe.find_label lbl s1 k) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ. rewrite EQ. eapply IHs2; eauto.
(* while *)
  rename s' into sr.
  rewrite (tr_find_label_if _ _ H1); auto.
  exploit (IHs (Kwhile2 e s k)); eauto. econstructor; eauto.
  destruct (ClightCe.find_label lbl s (Kwhile2 e s k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ. rewrite EQ. auto.
(* dowhile *)
  rename s' into sr.
  rewrite (tr_find_label_if _ _ H1); auto.
  exploit (IHs (Kdowhile1 e s k)); eauto. econstructor; eauto.
  destruct (ClightCe.find_label lbl s (Kdowhile1 e s k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ. rewrite EQ. auto.
(* for skip *)
  rename s' into sr.
  rewrite (tr_find_label_if _ _ H4); auto.
  exploit (IHs3 (ClightCe.Kfor3 e s2 s3 k)); eauto. econstructor; eauto.
  destruct (ClightCe.find_label lbl s3 (ClightCe.Kfor3 e s2 s3 k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ. rewrite EQ.
  exploit (IHs2 (ClightCe.Kfor4 e s2 s3 k)); eauto. econstructor; eauto.
(* for not skip *)
  rename s' into sr.
  rewrite (tr_find_label_if _ _ H3); auto.
  exploit (IHs1 (ClightCe.Kseq (Csyntax.Sfor Csyntax.Sskip e s2 s3) k)); eauto.
    econstructor; eauto. econstructor; eauto.
  destruct (ClightCe.find_label lbl s1
               (ClightCe.Kseq (Csyntax.Sfor Csyntax.Sskip e s2 s3) k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ; rewrite EQ.
  exploit (IHs3 (ClightCe.Kfor3 e s2 s3 k)); eauto. econstructor; eauto.
  destruct (ClightCe.find_label lbl s3 (ClightCe.Kfor3 e s2 s3 k)) as [[s'' k''] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ'. rewrite EQ'.
  exploit (IHs2 (ClightCe.Kfor4 e s2 s3 k)); eauto. econstructor; eauto.
(* break, continue, return 0 *)
  auto. auto. auto.
(* return 1 *)
  rewrite (tr_find_label_expression _ _ _ H0). auto.
(* switch *)
  rewrite (tr_find_label_expression _ _ _ H1). apply tr_find_label_ls. auto. constructor; auto.
(* labeled stmt *)
  destruct (ident_eq lbl l). exists ts0; exists tk; auto. apply IHs; auto.
(* goto *)
  auto.

  induction s; intros; inversion TR; subst; clear TR; simpl.
(* nil *)
  auto.
(* case *)
  exploit (tr_find_label s (ClightCe.Kseq (ClightCe.seq_of_labeled_statement s0) k)); eauto.
  econstructor; eauto. apply tr_seq_of_labeled_statement; eauto.
  destruct (ClightCe.find_label lbl s
    (ClightCe.Kseq (ClightCe.seq_of_labeled_statement s0) k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; auto.
  intro EQ. rewrite EQ. eapply IHs; eauto.
Qed.
*)
End FIND_LABEL.

(** Anti-stuttering measure *)

(** There are some stuttering steps in the translation:
- The execution of [Sdo a] where [a] is side-effect free,
  which is three transitions in the source:
<<
    Sdo a, k  --->  a, Kdo k ---> rval v, Kdo k ---> Sskip, k
>>
  but the translation, which is [Sskip], makes no transitions.
- The reduction [Ecomma (Eval v) r2 --> r2].
- The reduction [Eparen (Eval v) --> Eval v] in a [For_effects] context.

The following measure decreases for these stuttering steps. *)

(*Fixpoint esize (a: Csyntax.expr) : nat :=
  match a with
  | Csyntax.Eloc _ _ _ _ => 1%nat
  | Csyntax.Evar _ _ => 1%nat
  | Csyntax.Ederef r1 _ => S(esize r1)
  | Csyntax.Efield l1 _ _ => S(esize l1)
  | Csyntax.Eval _ _ => O
  | Csyntax.Evalof l1 _ => S(esize l1)
  | Csyntax.Eaddrof l1 _ => S(esize l1)
  | Csyntax.Eunop _ r1 _ => S(esize r1)
  | Csyntax.Ebinop _ r1 r2 _ => S(esize r1 + esize r2)%nat
  | Csyntax.Ecast r1 _ => S(esize r1)
  | Csyntax.Eseqand r1 _ _ => S(esize r1)
  | Csyntax.Eseqor r1 _ _ => S(esize r1)
  | Csyntax.Econdition r1 _ _ _ => S(esize r1)
  | Csyntax.Esizeof _ _ => 1%nat
  | Csyntax.Ealignof _ _ => 1%nat
  | Csyntax.Eassign l1 r2 _ => S(esize l1 + esize r2)%nat
  | Csyntax.Eassignop _ l1 r2 _ _ => S(esize l1 + esize r2)%nat
  | Csyntax.Epostincr _ l1 _ => S(esize l1)
  | Csyntax.Ecomma r1 r2 _ => S(esize r1 + esize r2)%nat
  | Csyntax.Ecall r1 rl2 _ => S(esize r1 + esizelist rl2)%nat
  | Csyntax.Ebuiltin ef _ rl _ => S(esizelist rl)%nat
  | Csyntax.Eparen r1 _ _ => S(esize r1)
  end

with esizelist (el: Csyntax.exprlist) : nat :=
  match el with
  | Csyntax.Enil => O
  | Csyntax.Econs r1 rl2 => (esize r1 + esizelist rl2)%nat
  end.
 *)

Definition measure (st: ClightCe.state) : nat := 0.
(*  match st with
  | ClightCe.ExprState _ r _ _ _ => (esize r + 1)%nat
  | ClightCe.State _ Csyntax.Sskip _ _ _ => 0%nat
  | ClightCe.State _ (Csyntax.Sdo r) _ _ _ => (esize r + 2)%nat
  | ClightCe.State _ (Csyntax.Sifthenelse r _ _) _ _ _ => (esize r + 2)%nat
  | _ => 0%nat
  end.

Lemma leftcontext_size:
  forall from to C,
  leftcontext from to C ->
  forall e1 e2,
  (esize e1 < esize e2)%nat ->
  (esize (C e1) < esize (C e2))%nat
with leftcontextlist_size:
  forall from C,
  leftcontextlist from C ->
  forall e1 e2,
  (esize e1 < esize e2)%nat ->
  (esizelist (C e1) < esizelist (C e2))%nat.
Proof.
  induction 1; intros; simpl; auto with arith.
  exploit leftcontextlist_size; eauto. auto with arith.
  exploit leftcontextlist_size; eauto. auto with arith.
  induction 1; intros; simpl; auto with arith. exploit leftcontext_size; eauto. auto with arith.
Qed.
*)
(** Forward simulation for expressions. *)
(*
Lemma tr_val_gen:
  forall ce le dst v ty a tmp,
  typeof a = ty ->
  (forall tge e le' m,
      (forall id, In id tmp -> le'!id = le!id) ->
      eval_expr tge e le' m a v) ->
  tr_expr ce le dst (Csyntax.Eval v ty) (final dst a) a tmp.
Proof.
  intros. destruct dst; simpl; econstructor; auto.
Qed.
 *)


Lemma sem_binary_operation : forall op v1 t1 v2 t2 m,
    sem_binary_operation ge op v1 t1 v2 t2 m =
      sem_binary_operation tge op v1 t1 v2 t2 m.
Proof.
  generalize comp_env_preserved.
  congruence.
Qed.

Lemma size_of_same : forall ty,
    sizeof ge ty = sizeof tge ty.
Proof.
  induction ty; try reflexivity.
  - unfold sizeof; fold sizeof.
    congruence.
  - unfold sizeof; fold sizeof.
    rewrite comp_env_preserved.
    reflexivity.
  - unfold sizeof; fold sizeof.
    rewrite comp_env_preserved.
    reflexivity.
Qed.

Lemma alignof_same : forall ty,
    alignof ge ty = alignof tge ty.
Proof.
  induction ty; try reflexivity.
  - unfold alignof; fold alignof.
    congruence.
  - unfold alignof; fold alignof.
    rewrite comp_env_preserved.
    reflexivity.
  - unfold alignof; fold alignof.
    rewrite comp_env_preserved.
    reflexivity.
Qed.


Lemma eval_expr_same : forall e le m,
    (forall (a:ClightCe.expr) v,
        ClightCe.eval_expr ge e le m a v ->
        forall tmp le' (MT: match_temp tmp le le'),
                    eval_expr tge e le' m a v) /\
      (forall (a:ClightCe.expr) loc ofs bf,
          ClightCe.eval_lvalue ge e le m a loc ofs bf ->
          forall tmp le' (MT : match_temp tmp le le'),
                      eval_lvalue tge e le' m a loc ofs bf).
Proof.
  intros.
  apply ClightCe.eval_expr_lvalue_ind; intros ; try (econstructor; eauto; fail).
  - econstructor ; eauto. destruct MT as (MT1 & M2). eauto.
  - intros.
    econstructor;eauto.
    generalize comp_env_preserved. congruence.
  - intros.
    rewrite size_of_same.
    apply eval_Esizeof.
  - intros.
    rewrite alignof_same.
    apply eval_Ealignof.
  - intros.
    eapply eval_Evar_global;eauto.
    rewrite symbols_preserved;auto.
  - intros.
    eapply eval_Efield_struct; eauto.
    rewrite comp_env_preserved;auto. eauto.
    rewrite comp_env_preserved.
    auto.
  - intros.
    eapply eval_Efield_union; eauto.
    rewrite comp_env_preserved. eauto.
    rewrite comp_env_preserved. eauto.
Qed.

Lemma eval_exprlist_same : forall e le le' tmp m al ty v,
    ClightCe.eval_exprlist ge e le m al ty v ->
    match_temp tmp le le' ->
    eval_exprlist tge e le' m al ty v.
Proof.
  intros.
  induction H.
  constructor.
  econstructor;eauto.
  eapply eval_expr_same;eauto.
Qed.

Lemma blocks_of_env_same : forall e,
    blocks_of_env tge e   =  (ClightCe.blocks_of_env ge e).
Proof.
  unfold blocks_of_env,ClightCe.blocks_of_env.
  unfold block_of_binding,ClightCe.block_of_binding.
  intros. induction  (PTree.elements e);auto.
  unfold map; fold map.
  destruct a. destruct p0.
  rewrite size_of_same.
  f_equal;auto.
Qed.

Lemma match_call_cont : forall fr k tk,
    match_cont fr k tk ->
    match_cont fr (ClightCe.call_cont k) (call_cont tk).
Proof.
  intros.
  induction H; simpl;auto.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma match_cont_is_call_cont : forall fr k tk ,
    ClightCe.is_call_cont k ->
    match_cont fr k tk ->
    is_call_cont tk.
Proof.
  intros.
  inv H0; simpl in *; auto.
Qed.


Lemma transl_function_fn_return : forall f tf,
    transl_function f = OK tf ->
    (fn_return tf) = ClightCe.fn_return f.
Proof.
  intros.
  unfold transl_function in H.
  revert H.
  destr_if ; try discriminate.
  destruct (transl_stmt (ClightCe.fn_body f) (make_generator (fresh_id f))); try discriminate.
  intros.
  inv H; simpl; reflexivity.
Qed.

Lemma tr_seq_of_labeled_statement : forall lb tlb tmp,
    tr_lblstmts lb tlb tmp ->
    tr_stmt
    (ClightCe.seq_of_labeled_statement lb)
    (seq_of_labeled_statement tlb) tmp.
Proof.
  intros.
  induction H; simpl.
  - constructor.
  - econstructor;eauto.
Qed.

Fixpoint tr_stmt_mono (s:ClightCe.statement) :
  forall s' tmp1 tmp2,
         tr_stmt s s' tmp1 ->
         incl tmp1 tmp2 ->
         tr_stmt s s' tmp2
         with tr_lblstmts_mono (s:ClightCe.labeled_statements) :
  forall s' tmp1 tmp2,
         tr_lblstmts s s' tmp1 ->
         incl tmp1 tmp2 ->
         tr_lblstmts s s' tmp2.
Proof.
  intros.
  { destruct s; inv H; try (econstructor; eauto ; repeat (eapply incl_tran; eauto);fail).
  }
  {
    destruct s; intros; inv H.
    constructor.
    econstructor; eauto.
    eapply incl_tran; eauto.
    eapply incl_tran; eauto.
  }
Qed.

Lemma tr_lblstmts_select_switch_case : forall ce sl tls n tmp s,
    tr_lblstmts sl tls tmp->
    ClightCe.select_switch_case ce n sl = OK s ->
    exists s', select_switch_case ce n tls = OK s' /\
                  option_rel (fun sl1 sl2 => tr_lblstmts sl1 sl2 tmp) s s'.
Proof.
  intros.
  revert s H0.
  induction H.
  - simpl. intros. inv H0. eexists. split; eauto.
    constructor.
  - simpl.
    destruct c;auto.
    destruct (eval_switch_val ce s0) eqn:ES; try discriminate.
    + destruct (zeq z n);auto.
      * intros. inv H4.
        econstructor. split. econstructor.
        econstructor.
        econstructor ;eauto.
      * intros.
        destruct (IHtr_lblstmts _ H4) as (s' & SSC & R).
        eexists; split; eauto.
        inv R. constructor.
        constructor. eapply tr_lblstmts_mono;eauto.
    + intros.
        destruct (IHtr_lblstmts _ H4) as (s' & SSC & R).
        eexists; split; eauto.
        inv R. constructor.
        constructor. eapply tr_lblstmts_mono;eauto.
Qed.

Lemma tr_lblstmts_select_switch_default : forall sl tls tmp,
    tr_lblstmts sl tls  tmp ->
    tr_lblstmts (ClightCe.select_switch_default sl)
               (select_switch_default tls) tmp.
Proof.
  intros.
  induction H.
  - simpl. constructor.
  - simpl.
    destruct c;auto.
    eapply tr_lblstmts_mono; eauto.
    econstructor ;eauto.
Qed.


Lemma tr_lblstmts_select_switch : forall ce sl tls n tmp s,
    tr_lblstmts sl tls tmp->
    ClightCe.select_switch ce n sl = OK s ->
    exists s', select_switch ce n tls = OK s' /\
                  tr_lblstmts s s' tmp.
Proof.
  intros.
  unfold ClightCe.select_switch in H0.
  monadInv H0.
  exploit tr_lblstmts_select_switch_case;eauto.
  intros (s' & SC & R).
  destruct x ; inv EQ0.
  - inv R.
    unfold select_switch.
    rewrite SC. simpl.
    eexists ; split; eauto.
  - inv R.
    unfold select_switch.
    rewrite SC. simpl.
    eexists; split; eauto.
    eapply tr_lblstmts_select_switch_default    ; eauto.
Qed.


Lemma tr_expression_nolabel : forall c s a tmp,
    tr_expression c s a tmp -> forall lb, nolabel lb s.
Proof.
  intros.
  inv H.
  apply makeseq_nolabel.
  specialize (H0 (PTree.empty _ )).
  induction H0.
  - constructor.
  - apply nolabel_list_app; auto.
    constructor.
    apply makeif_nolabel;auto.
    apply nolabel_seq.
    apply makeseq_nolabel.
    auto.
    constructor. constructor.
    constructor.
  - apply nolabel_list_app; auto.
    constructor.
    apply makeif_nolabel;auto.
    constructor.
    apply nolabel_seq.
    apply makeseq_nolabel; auto.
    constructor. constructor.
  - auto.
Qed.


Lemma nolabel_ite : forall lbl c e1 e2,
    nolabel lbl e1 ->
    nolabel lbl e2 ->
    nolabel lbl (Sifthenelse c e1 e2).
Proof.
  unfold nolabel.
  simpl.
  intros.
  rewrite H. auto.
Qed.

Lemma nolabel_loop : forall lbl s1 s2,
    nolabel lbl s1 ->
    nolabel lbl s2 ->
    nolabel lbl (Sloop s1 s2).
Proof.
  unfold nolabel.
  simpl.
  intros.
  rewrite H. auto.
Qed.


Fixpoint tr_find_label_stmt_None (lbl:label) (b:ClightCe.statement) : forall tb k tmp,
    ClightCe.find_label lbl b k = None ->
    tr_stmt b tb tmp ->
    nolabel lbl tb
  with tr_find_label_stmts_None (lbl:label) (b:ClightCe.labeled_statements) : forall tb k tmp,
      ClightCe.find_label_ls lbl b k = None ->
      tr_lblstmts b tb tmp->
      forall tk, find_label_ls lbl tb tk = None.
Proof.
  destruct b; intros; inv H0; try constructor.
  -
    simpl in H.
    destruct (ClightCe.find_label lbl b1 (ClightCe.Kseq b2 k)) eqn:FD ; try discriminate.
    apply nolabel_seq.
    eapply tr_find_label_stmt_None in FD; eauto.
    eapply tr_find_label_stmt_None in H; eauto.
  - apply nolabel_seq.
    eapply tr_expression_nolabel; eauto.
    simpl in H.
    destruct (ClightCe.find_label lbl b1 k) eqn:FL;
      try discriminate.
    apply nolabel_ite;auto.
    eapply tr_find_label_stmt_None in FL ;eauto.
    eapply tr_find_label_stmt_None in H ;eauto.
  - simpl in H.
    destruct (ClightCe.find_label lbl b1 (ClightCe.Kloop1 b1 b2 k)) eqn:FD ; try discriminate.
    apply nolabel_loop;auto.
    eapply tr_find_label_stmt_None in FD ;eauto.
    eapply tr_find_label_stmt_None in H ;eauto.
  -  simpl in H.
     unfold nolabel.
     simpl.
     intros.
     eapply tr_find_label_stmts_None;eauto.
  -  simpl in H.
     destruct (ident_eq lbl l); try discriminate.
     apply tr_find_label_stmt_None with (2:= H5) in H.
     unfold nolabel in *.
     simpl. intros.
     destruct (ident_eq lbl l); try congruence.
  - intros.
    destruct b; simpl in H.
    inv H0. reflexivity.
    destruct (ClightCe.find_label lbl s
                (ClightCe.Kseq (ClightCe.seq_of_labeled_statement b) k)) eqn:FD ; try discriminate.
    inv H0.
    simpl.
    erewrite tr_find_label_stmt_None.
    eapply tr_find_label_stmts_None;eauto.
    eapply FD; auto.
    eauto.
Qed.

Lemma all_fresh_incl : forall l1 l2 fr,
    incl l1 l2 ->
    all_fresh fr l2 ->
    all_fresh fr l1.
Proof.
  unfold all_fresh,incl.
  intros.
  apply H in H1. apply H0 in H1.
  auto.
Qed.

Lemma all_below_app : forall fr l1 l2,
    all_below fr (l1 ++ l2) <-> all_below fr l1 /\ all_below fr l2.
Proof.
  unfold all_below.
  intros.
  split; intros.
  - split; intros;
      apply H; rewrite in_app_iff; tauto.
  - rewrite in_app_iff in H0.
    destruct H0; intuition auto.
Qed.

Lemma all_below_incl : forall fr l1 l2,
    all_below fr l1 ->
    incl l2 l1 ->
    all_below fr l2.
Proof.
  unfold all_below.
  intros.
  apply H. eapply H0;auto.
Qed.


Lemma all_fresh_app : forall fr l1 l2,
    all_fresh fr (l1 ++ l2) <-> all_fresh fr l1 /\ all_fresh fr l2.
Proof.
  unfold all_fresh.
  intros.
  split; intros.
  - split; intros;
      apply H; rewrite in_app_iff; tauto.
  - rewrite in_app_iff in H0.
    destruct H0; intuition auto.
Qed.



Lemma all_below_optid_list : forall fr optid,
    all_below fr (optid_list optid) ->
    Pltopt optid fr.
Proof.
  unfold all_below,Pltopt.
  destruct optid; auto.
  simpl. auto.
Qed.

Lemma seq_of_labeled_statement_eq :
  forall b,
    temps_of_stmt (ClightCe.seq_of_labeled_statement b) = temps_of_lbstmts b.
Proof.
  induction b.
  - simpl. reflexivity.
  - simpl. f_equal. auto.
Qed.

Fixpoint tr_find_label (lbl:label) (b:ClightCe.statement) : forall fr tb k tk s' k' tmp,
    ClightCe.find_label lbl b k = Some (s', k') ->
    match_cont fr k tk ->
    tr_stmt b tb tmp ->
    all_fresh fr tmp ->
    all_below fr (temps_of_stmt b) ->
    exists ts' tk',
      find_label lbl tb tk = Some (ts', tk') /\
        tr_stmt s' ts' tmp /\ match_cont fr k' tk' /\
        all_below fr (temps_of_stmt s')
  with tr_find_labels (lbl:label) (b:ClightCe.labeled_statements) : forall fr tb k tk s' k' tmp,
      ClightCe.find_label_ls lbl b k = Some (s', k') ->
      match_cont fr k tk ->
      tr_lblstmts b tb tmp ->
      all_fresh fr tmp ->
      all_below fr (temps_of_lbstmts b) ->
      exists ts' tk',
        find_label_ls lbl tb tk = Some (ts', tk') /\
          tr_stmt s' ts' tmp /\ match_cont fr k' tk' /\
          all_below fr (temps_of_stmt s').
Proof.
  destruct b; simpl; try discriminate.
  - intros.
    destruct (ClightCe.find_label lbl b1 (ClightCe.Kseq b2 k)) eqn:FL;
      try discriminate.
    inv H.
    inv H1.
    exploit tr_find_label ; eauto.
    econstructor. apply H2.
    apply all_below_app in H3.
    tauto.
    eapply tr_stmt_mono;eauto.
    eauto. eapply all_fresh_incl; eauto.
    apply all_below_app in H3.
    tauto.
    intros (ts' & tk' & FD1 & TR1 & M1 & BL1).
    simpl.
    exists ts', tk'.
    rewrite FD1.
    repeat split; auto.
    eapply tr_stmt_mono;eauto.
    inv H1.
    exploit tr_find_label; eauto.
    eapply all_fresh_incl; eauto.
    apply all_below_app in H3.
    tauto.
    intros (ts' & tk' & FD & TR & M & BL).
    exists ts',tk'.
    simpl.
    rewrite tr_find_label_stmt_None.
    repeat split ; auto.
    eapply tr_stmt_mono;eauto. eapply FL.
    eauto.
  - intros.
    inv H1.
    destruct (ClightCe.find_label lbl b1 k)eqn:FD ; try congruence.
    + inv H.
    exploit tr_find_label; eauto.
    eapply all_fresh_incl;eauto.
    apply all_below_app in H3.
    destruct H3. apply all_below_app in H1. tauto.
    intros (ts' & tk' & FD' & TR' & MC' & BL').
    eexists ts',tk'.
    simpl.
    rewrite tr_expression_nolabel;eauto.
    rewrite FD'.
    repeat split; auto.
    eapply tr_stmt_mono;eauto.
    +     exploit tr_find_label; eauto.
          eapply all_fresh_incl;eauto.
          apply all_below_app in H3.
          destruct H3. apply all_below_app in H3. tauto.
          intros (ts' & tk' & FD' & TS' & MC' & BL').
    eexists ts',tk'.
    simpl.
    rewrite tr_expression_nolabel;eauto.
    rewrite tr_find_label_stmt_None.
    repeat split;auto.
    eapply tr_stmt_mono;eauto.
    eauto.
    eauto.
  - intros.
    inv H1.
    destruct (ClightCe.find_label lbl b1 (ClightCe.Kloop1 b1 b2 k))eqn:FD ; try congruence.
    + inv H.
    exploit tr_find_label. eauto.
    econstructor. eauto.
    eapply all_fresh_incl.  apply H9. auto.
    eapply all_fresh_incl.  apply H12. auto.
    apply all_below_app in H3. tauto.
    apply all_below_app in H3. tauto.
    eauto. eauto. auto.
    eauto.
    eapply all_fresh_incl;eauto.
    apply all_below_app in H3.
    tauto.
    intros (ts' & tk' & FD' & TR' & MC' & BL').
    eexists ts',tk'.
    simpl.
    rewrite FD'.
    repeat split; auto.
    eapply tr_stmt_mono;eauto.
    +  exploit tr_find_label; eauto.
    econstructor. eauto.
    eapply all_fresh_incl.  apply H9. auto.
    eapply all_fresh_incl.  apply H12. auto.
    apply all_below_app in H3. tauto.
    apply all_below_app in H3. tauto.
    eauto. eauto. auto.
    eauto.
    eapply all_fresh_incl;eauto.
    apply all_below_app in H3.
    tauto.
       intros (ts' & tk' & FD' & TR' & MC' & BL').
    eexists ts',tk'.
    simpl.
    rewrite tr_find_label_stmt_None.
    repeat split; auto.
    eapply tr_stmt_mono;eauto.
    eauto. eauto.
  - intros.
    inv H1.
    exploit tr_find_labels;eauto.
    constructor ;auto. eauto.
    eapply all_fresh_incl;eauto.
    apply all_below_app in H3. tauto.
    intros (ts' & tk' & FD' & TS' & MC' &BL').
    do 2 eexists ; repeat split; eauto.
    eapply tr_stmt_mono;eauto.
  - intros.
    destruct (ident_eq lbl l); try discriminate.
    inv H1.
    inv H.
    exists ts,tk.
    simpl. destruct (ident_eq l l); try discriminate.
    split; auto.
    tauto.
    inv H1.
    exploit tr_find_label; eauto.
    intros (ts'&tk'&FD).
    exists ts',tk'.
    simpl. destruct (ident_eq lbl l); try congruence.
  - intros.
    destruct b; simpl in H.
    + discriminate.
    + inv H1.
      destruct (ClightCe.find_label lbl s
                  (ClightCe.Kseq (ClightCe.seq_of_labeled_statement b) k)) eqn:FD;
        try discriminate.
      inv H.
      exploit tr_find_label;eauto.
      econstructor; eauto.
      simpl in H3. apply all_below_app in H3.
      rewrite seq_of_labeled_statement_eq. tauto.
      apply tr_seq_of_labeled_statement.
      eauto. eapply tr_lblstmts_mono;eauto.
      eapply all_fresh_incl;eauto.
      simpl in H3. apply all_below_app in H3.
      tauto.
      intros (ts' & tk' & FD' & TS' & MC' &BL').
      exists ts',tk'.
      repeat split; auto.
      simpl.
      rewrite FD'. reflexivity.
      eapply tr_stmt_mono;eauto.
      exploit tr_find_labels;eauto.
      eapply all_fresh_incl;eauto.
      simpl in H3. apply all_below_app in H3; tauto.
      intros (ts' & tk' & FD' & TS' & MC' &BL').
      exists ts',tk'.
      repeat split; auto.
      simpl.
      rewrite tr_find_label_stmt_None.
      auto.
      eauto.
      eauto.
      eapply tr_stmt_mono;eauto.
Qed.

Lemma tr_stmt_body : forall f tf,
    transl_function f = OK tf->
    exists tmps, tr_stmt (ClightCe.fn_body f) (fn_body tf) tmps
                /\
                  all_fresh (fresh_id f) tmps
                 /\ all_below (fresh_id f) (temps_of_stmt (ClightCe.fn_body f)).
Proof.
  unfold transl_function.
  intros.
  destruct (forallb (fun x : positive => (x <? fresh_id f)%positive)
          (temps_of_stmt (ClightCe.fn_body f))) eqn:ALL; try discriminate.
  destruct (transl_stmt (ClightCe.fn_body f) (make_generator (fresh_id f))) eqn:TR;
    try discriminate.
  inv H.
  simpl.
  apply transl_stmt_meets_spec in TR.
  destruct TR as (tmps & TR & C).
  exists tmps ; split;auto.
  split.
  - intros. unfold contained in C.
    unfold all_fresh;intros.
    apply C in H. unfold within in H. destruct H; auto.
  - rewrite forallb_forall in ALL.
    unfold all_below. intros. apply ALL in H. unfold Plt.
    rewrite Pos.ltb_lt in H. lia.
Qed.

Lemma alloc_variables_preserved : forall ev m v e m',
    ClightCe.alloc_variables ge ev m v e m' ->
    alloc_variables tge ev m v e m'.
Proof.
  intros. induction H.
  constructor.
  econstructor; eauto.
  rewrite size_of_same in H. auto.
Qed.

Lemma bind_parameters_preserved : forall e m v vargs m1,
    ClightCe.bind_parameters ge e m v vargs m1 ->
    bind_parameters tge e m v vargs m1.
Proof.
  intros. induction H.
  constructor.
  econstructor; eauto.
  rewrite comp_env_preserved.
  auto.
Qed.

Lemma create_undef_spec : forall x l, (create_undef_temps l) ! x = if In_dec peq x (List.map fst l) then Some Vundef else None.
Proof.
  induction l.
  - simpl. rewrite PTree.gempty.
    reflexivity.
  - unfold create_undef_temps;fold create_undef_temps.
    destruct a.
    rewrite PTree.gsspec.
    simpl.
    destruct (peq x i); destruct (peq i x); try congruence.
    rewrite IHl; auto.
    destruct (in_dec peq x (map fst l)); auto.
Qed.

Lemma match_temp_create_undef :
  forall l1 l2 (fr:ident)
    (FR : forall  x,
                     In x (map fst l1) -> Plt x fr),
    incl l1 l2 ->
    match_temp fr (create_undef_temps l1) (create_undef_temps l2).
Proof.
  intros.
  constructor.
  - intros.
    rewrite create_undef_spec in *.
    unfold ident in *.
    destruct (in_dec peq x (map fst l1)).
    inv H0.
    destruct (in_dec peq x (map fst l2)); auto.
    rewrite in_map_iff in i.
    destruct i. destruct H0; subst.
    apply H in H1. exfalso.
    apply n. rewrite in_map_iff.
    exists x0; tauto.
    discriminate.
  - intros.
    rewrite create_undef_spec.
    unfold ident in *.
    destruct (in_dec peq x (map fst l1)).
    eapply FR in i.  unfold Ple, Plt in *. lia.
    reflexivity.
Qed.


  
Lemma function_entry1_preserved : forall f tf vargs m e le m1,
    ClightCe.function_entry1 ge f vargs m e le m1 ->
    transl_function f = OK tf ->
    exists le', function_entry1 tge tf vargs m e le' m1 /\ match_temp (fresh_id f) le le' /\   all_below (fresh_id f) (temps_of_stmt (ClightCe.fn_body f)).
Proof.
  intros.
  inv H.
  eexists.
  split.
  econstructor; eauto.
  - erewrite function_params_preserved; eauto.
   erewrite function_vars_preserved; eauto.
  - erewrite function_params_preserved; eauto.
    erewrite function_vars_preserved; eauto.
    eapply alloc_variables_preserved  ;eauto.
  - erewrite function_params_preserved;eauto.
    apply bind_parameters_preserved; auto.
  - split.
    + apply match_temp_create_undef.
    { repeat intro.
      apply lt_temps_fresh_id in H. auto. }
    { unfold transl_function in H0.
      destruct (forallb (fun x : positive => (x <? fresh_id f)%positive)
           (temps_of_stmt (ClightCe.fn_body f))) eqn:ALL ; try discriminate.
      destruct (transl_stmt (ClightCe.fn_body f) (make_generator (fresh_id f))) eqn:F.
      congruence.
      inv H0. simpl.
      apply incl_appl.
      apply incl_refl.
    }
    + unfold transl_function in H0.
      destruct (forallb (fun x : positive => (x <? fresh_id f)%positive)
           (temps_of_stmt (ClightCe.fn_body f))) eqn:ALL ; try discriminate.
      destruct (transl_stmt (ClightCe.fn_body f) (make_generator (fresh_id f))) eqn:F.
      congruence.
      inv H0.
      rewrite forallb_forall in ALL.
      unfold all_below;intros.
      apply ALL in H.
      rewrite Pos.ltb_lt in H. unfold Plt; lia.
Qed.

Lemma match_temp_set : forall le le' fr id v
    (NOTFR:Plt id fr),
    match_temp fr le le' ->
    match_temp fr (PTree.set id v le) (PTree.set id v le').
Proof.
  unfold match_temp.
  intros.
  split ; intros.
  - rewrite PTree.gsspec in *.
    destruct (peq x id).
    congruence.
    apply H;auto.
  - rewrite PTree.gsspec in *.
    destruct (peq x id).
    subst. unfold Plt,Ple in *; lia.
    apply H;auto.
Qed.

Lemma match_temp_set_opt :
  forall le le' optid vres fr
         (FR : Pltopt optid fr),
    match_temp fr le le' ->
    match_temp fr (set_opttemp optid vres le) (set_opttemp optid vres le').
Proof.
  unfold set_opttemp.
  intros. destruct optid;auto.
  apply match_temp_set;auto.
Qed.

Lemma match_temp_fresh :
  forall fr le le' t v
         (LE : Ple fr t)
         (MT : match_temp fr le le'),
    match_temp fr le (PTree.set t v le').
Proof.
  intros.
  destruct MT; constructor.
  - intros.
    destruct (Pos.eq_dec x t); subst.
    rewrite H0 in H1.
    discriminate.
    auto.
    rewrite PTree.gso; auto.
  - intros.
    auto.
Qed.

Ltac split_and :=
  repeat match goal with
  | |- ?A /\ ?B => split
  end.

Lemma eval_cexpr_sound : forall e le m a b
                                (EVAL : eval_cexpr ge e le m a b)
                                le' sl a0 tmps tf s fr tk,
    tr_cexpr le' a sl a0 tmps ->
    all_fresh fr tmps ->
    match_temp fr le le' ->
    exists le'' v,
        plus step1 tge
        (State tf Sskip (Kseqlist sl (Kseq s tk)) e le' m)
        E0 (State tf s tk e le'' m) /\ eval_expr tge e le'' m a0  v
        /\ typeof a0 = type_bool /\ bool_val v type_bool m = Some b
        /\ match_temp fr le le'' /\
          forall x, ~ In x tmps -> le' ! x = le'' ! x.
Proof.
  intros until b.
  intro EVAL.
  induction EVAL; intros.
  - inv H1.
    exists le'. eexists.
    split_and; auto.
    + eapply plus_one.
      econstructor.
    + econstructor.
      eapply eval_expr_same; eauto.
      rewrite cast_bool_bool_val.
      rewrite H0. reflexivity.
    + destruct b; reflexivity.
  - inv H.
    rewrite Kseqlist_app.
    exploit IHEVAL.
    eauto. eapply all_fresh_incl;eauto.
    auto.
    intros (le'' & v & PL & E & TY & BV & MT & MOD).
    do 2 eexists.
    split_and.
    + eapply plus_star_trans.
    apply PL.
    eapply star_trans.
    eapply step_makeif.
    eauto. rewrite TY. eauto.
    simpl. eapply star_two.
    econstructor. econstructor.
    econstructor. reflexivity.
    reflexivity.
    reflexivity.
    + econstructor. rewrite PTree.gss. reflexivity.
    + simpl. reflexivity.
    + unfold bool_val. simpl. reflexivity.
    + apply match_temp_fresh ;auto.
    + intros.
      rewrite PTree.gsspec.
      destruct (peq x t). subst. tauto.
      apply MOD;auto.
  - inv H.
    rewrite Kseqlist_app.
    exploit IHEVAL1.
    eauto.
    eapply all_fresh_incl;eauto.
    auto.
    intros (le'' & v & PL & E & TY & BV & MT &MOD).
    clear H4.
    apply tr_cexpr_invariant with (le':=le'') in H5.
    exploit IHEVAL2.
    eauto.
    eapply all_fresh_incl;eauto. auto.
    intros (le3 & v2 & PL2 & E2 & TY2 & BV2 & MT2 & MOD2).
    do 2 eexists.
    split_and.
    + eapply plus_star_trans.
    apply PL.
    eapply star_trans.
    eapply step_makeif.
    eauto. rewrite TY. eauto.
    simpl.
    clear PL.
    eapply star_trans.
    eapply plus_star.
    eapply plus_one.
    econstructor.
    eapply star_trans.
    apply push_seq.
    eapply plus_star.
    eapply plus_star_trans.
    eapply PL2.
    eapply plus_star.
    eapply plus_two.
    econstructor. eauto.
    econstructor. 
    reflexivity.
    reflexivity. reflexivity.
    reflexivity.
    reflexivity. reflexivity.
    + econstructor.
      rewrite PTree.gss. reflexivity.
    + reflexivity.
    + auto.
    + apply match_temp_fresh ;auto.
    + intros.
      rewrite PTree.gsspec. destruct (peq x t).
      subst. tauto. rewrite MOD.
      apply MOD2.
      intro. apply H. apply H9. auto.
      intro. apply H. apply H7. auto.
    + intros.
      rewrite MOD; auto.
      intro.
      eapply H6; eauto.
  - inv H.
    rewrite Kseqlist_app.
    exploit IHEVAL.
    eauto. eapply all_fresh_incl;eauto.
    auto.
    intros (le'' & v & PL & E & TY & BV & MT & MOD).
    do 2 eexists.
    split_and.
    + eapply plus_star_trans.
    apply PL.
    eapply star_trans.
    eapply step_makeif.
    eauto. rewrite TY. eauto.
    simpl. eapply star_two.
    econstructor. econstructor.
    econstructor. reflexivity.
    reflexivity.
    reflexivity.
    + econstructor. rewrite PTree.gss. reflexivity.
    + simpl. reflexivity.
    + unfold bool_val. simpl. reflexivity.
    + apply match_temp_fresh ;auto.
    + intros.
      rewrite PTree.gsspec.
      destruct (peq x t). subst. tauto.
      apply MOD;auto.
  - inv H.
    rewrite Kseqlist_app.
    exploit IHEVAL1.
    eauto.
    eapply all_fresh_incl;eauto.
    auto.
    intros (le'' & v & PL & E & TY & BV & MT &MOD).
    clear H4.
    apply tr_cexpr_invariant with (le':=le'') in H5.
    exploit IHEVAL2.
    eauto.
    eapply all_fresh_incl;eauto. auto.
    intros (le3 & v2 & PL2 & E2 & TY2 & BV2 & MT2 & MOD2).
    do 2 eexists.
    split_and.
    + eapply plus_star_trans.
    apply PL.
    eapply star_trans.
    eapply step_makeif.
    eauto. rewrite TY. eauto.
    simpl.
    clear PL.
    eapply star_trans.
    eapply plus_star.
    eapply plus_one.
    econstructor.
    eapply star_trans.
    apply push_seq.
    eapply plus_star.
    eapply plus_star_trans.
    eapply PL2.
    eapply plus_star.
    eapply plus_two.
    econstructor. eauto.
    econstructor.
    reflexivity.
    reflexivity. reflexivity.
    reflexivity.
    reflexivity. reflexivity.
    + econstructor.
      rewrite PTree.gss. reflexivity.
    + reflexivity.
    + auto.
    + apply match_temp_fresh ;auto.
    + intros.
      rewrite PTree.gsspec. destruct (peq x t).
      subst. tauto. rewrite MOD.
      apply MOD2.
      intro. apply H. apply H9. auto.
      intro. apply H. apply H7. auto.
    + intros.
      rewrite MOD; auto.
      intro.
      eapply H6; eauto.
  - inv H.
    exploit IHEVAL.
    eauto. eapply all_fresh_incl;eauto.
    auto.
    intros (le'' & v & PL & E & TY & BV & MT & MOD).
    do 2 eexists.
    split_and.
    + eapply plus_star_trans.
    apply PL.
    apply star_refl.
    reflexivity.
    + econstructor. eauto.
      simpl. unfold sem_notbool. rewrite TY. rewrite BV.
      reflexivity.
    + simpl. reflexivity.
    + destruct b; reflexivity.
    + auto.
    + intros.
      apply MOD;auto.
Qed.


Lemma list_disjoint_nil_l : forall {A: Type} (l:list A),
  list_disjoint nil l.
Proof.
  intros.
  unfold list_disjoint; simpl; tauto.
Qed.

Lemma list_disjoint_appl : forall {A: Type} (l1 l2 r:list A),
    list_disjoint (l1 ++ l2) r -> list_disjoint l1 r.
Proof.
  unfold list_disjoint.
  intros.
  eapply H ; eauto.
  rewrite in_app_iff.
  tauto.
Qed.

(*Lemma list_disjoint_Inopt :
  forall oid l, list_disjoint (optid_list oid) l ->
                ~ Inopt oid l.
Proof.
  destruct oid.
  - simpl. intros.
    unfold list_disjoint in H.
    intro. apply (H i i); simpl; auto.
  - simpl.
    auto.
Qed.
 *)

Lemma all_fresh_nil : forall fr,  all_fresh fr nil.
Proof.
  unfold all_fresh.
  simpl. tauto.
Qed.

Lemma all_below_nil : forall fr,  all_below fr nil.
Proof.
  unfold all_below.
  simpl. tauto.
Qed.

Lemma temps_of_lbstmts_select_switch : forall ce n sl s,
    ClightCe.select_switch ce n sl = OK s ->
    incl (temps_of_lbstmts s)  (temps_of_lbstmts sl).
Proof.
  unfold ClightCe.select_switch.
  intros. unfold Errors.bind in H.
  destruct (ClightCe.select_switch_case ce n sl) eqn:SEL; try discriminate.
  destruct o. inv H.
  - revert s SEL.
    induction sl; simpl; try discriminate.
    destruct o. destruct (eval_switch_val ce s0) eqn:ES.
    destruct (zeq z n).
    intros. inv SEL.
    simpl. apply incl_refl.
    intros.
    apply IHsl in SEL.
    apply incl_appr. auto.
    intros. discriminate.
    intros.
    apply incl_appr. auto.
  - inv H.
    clear SEL. induction sl; simpl.
    apply incl_refl.
    destruct o.
    eapply incl_tran.
    apply incl_appr. eauto.
    apply incl_refl.
    simpl. apply incl_refl.
Qed.

Lemma estep_simulation:
  forall S1 t S2, ClightCe.step1 ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  exists S2',
     (plus step1 tge S1' t S2' \/
       (star step1 tge S1' t S2' /\ measure S2 < measure S1)%nat)
  /\ match_states S2 S2'.
Proof.

Ltac NOTIN :=
  match goal with
  | [ H1: In ?x ?l, H2: list_disjoint ?l _ |- ~In ?x _ ] =>
        red; intro; elim (H2 x x); auto; fail
  | [ H1: In ?x ?l, H2: list_disjoint _ ?l |- ~In ?x _ ] =>
        red; intro; elim (H2 x x); auto; fail
  end.
intros.
inv H; inv MS.
- (* Sassign *)
  inv TR.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;eauto.
  eapply eval_expr_same;eauto.
  eapply eval_expr_same;eauto.
  rewrite comp_env_preserved. eauto.
  econstructor; eauto.
  simpl. apply all_below_nil.
  constructor.
- (* Sset *)
  inv TR.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;eauto.
  eapply eval_expr_same;eauto.
  econstructor; auto.
  simpl. apply all_below_nil.
  apply match_temp_set; eauto.
  apply TEMPS. simpl. tauto.
  constructor.
  + eauto.
- (* Scall *)
  inv TR.
  exploit functions_translated; eauto.
  intros (tvf & FIND & TRANS).
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;eauto.
  eapply eval_expr_same;eauto.
  eapply eval_exprlist_same;eauto.
  rewrite <- H4.
  apply type_of_fundef_preserved; auto.
  assert (FR : exists fr, (fresh_of_fundef fd fr)).
  { destruct fd. eexists. econstructor; eauto.
    eexists. econstructor. }
  destruct FR as (fr' & FR).
  econstructor. auto. eauto.
  econstructor. auto. auto.
  auto.
  simpl in TEMPS.
  rewrite all_below_app in TEMPS.
  destruct TEMPS.
  apply all_below_optid_list; auto.
- (* Sbuiltin *)
  inv TR.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;eauto.
  eapply eval_exprlist_same;eauto.
  eapply external_call_symbols_preserved; eauto.
  apply senv_preserved.
  econstructor; eauto.
  simpl. apply all_below_nil.
  eapply match_temp_set_opt  ; eauto.
  simpl in TEMPS.
  apply all_below_app in TEMPS.
  apply all_below_optid_list; tauto.
  constructor.
- inv TR.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;eauto.
  econstructor; eauto.
  simpl in TEMPS.
  apply all_below_app in TEMPS. tauto.
  eapply all_fresh_incl;eauto.
  econstructor; eauto.
  simpl in TEMPS.
  apply all_below_app in TEMPS; tauto.
  eapply tr_stmt_mono;eauto.
- inv TR.
  inv MK.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;eauto.
  econstructor;auto.
  eapply tr_stmt_mono;eauto.
  apply incl_refl.
  auto.
- inv TR.
  inv MK.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;eauto.
  econstructor; eauto.
  constructor.
- inv TR.
  inv MK.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;eauto.
  econstructor; eauto.
  constructor.
- (* Sif *)
  inv TR. inv H3.
  specialize (H le').
  exploit eval_cexpr_sound; eauto.
  eapply all_fresh_incl;eauto.
  intros (le'' & v & EX & EV & TY & VAL & MT & MOD).
  eexists.
  split.
  left.
  eapply plus_trans.
  eapply plus_left.
  econstructor.
  eapply push_seq.
  reflexivity.
  eapply plus_trans.
  eapply EX.
  apply plus_one.
  econstructor.
  eauto. rewrite TY. rewrite VAL. reflexivity.
  reflexivity. reflexivity.
  destruct b.
  + econstructor; auto.
    simpl in TEMPS.
    rewrite! all_below_app in TEMPS.
    tauto.
    eauto.
    eapply all_fresh_incl;eauto.
  + econstructor; auto.
    simpl in TEMPS.
    rewrite! all_below_app in TEMPS.
    tauto.
    eauto.
    eapply all_fresh_incl;eauto.
- inv TR.
    eexists.
  split.
  left.
  eapply plus_one.
  econstructor;eauto.
  econstructor; auto.
  simpl in TEMPS. apply all_below_app in TEMPS. tauto.
  eauto.
  eapply all_fresh_incl ; eauto.
  econstructor; auto.
  eapply all_fresh_incl. apply H4.
  auto.
  eapply all_fresh_incl. apply H7.
  auto.
  simpl in TEMPS.
  apply all_below_app in TEMPS. tauto.
  simpl in TEMPS.
  apply all_below_app in TEMPS. tauto.
  auto. auto. auto.
- inv MK.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;eauto.
  destruct H0; subst ; inv TR; intuition congruence.
  econstructor; eauto.
  econstructor; auto.
  apply H4. apply H5.
  auto. auto. auto.
- inv TR.
  inv MK.
  eexists.
  split.
  left.
  eapply plus_one.
  eapply step_break_loop1.
  econstructor;eauto.
  constructor.
- inv TR.
  inv MK.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;auto.
  econstructor;auto.
  simpl.
  rewrite all_below_app. tauto.
  econstructor; eauto.
  apply incl_appl. apply incl_refl.
  apply incl_appr. apply incl_refl.
  rewrite all_fresh_app. tauto.
- inv TR.
  inv MK.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;auto.
  econstructor;auto.
  constructor;auto.
  eauto.
- inv TR.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;auto.
  rewrite blocks_of_env_same.
  eauto.
  econstructor ; eauto.
  apply match_call_cont;auto.
  eauto.
- inv TR.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;auto.
  eapply eval_expr_same;eauto.
  erewrite transl_function_fn_return; eauto.
  rewrite blocks_of_env_same.
  eauto.
  econstructor.
  apply match_call_cont;auto. eauto.
- inv TR.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;auto.
  eapply match_cont_is_call_cont  ; eauto.
  rewrite blocks_of_env_same.
  eauto.
  econstructor ;auto. eauto.
- inv TR.
  exploit tr_lblstmts_select_switch; eauto.
  intros (s'& SSW' & R).
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;auto.
  eapply eval_expr_same;eauto.
  eauto.
  rewrite comp_env_preserved. eauto.
  econstructor; eauto.
  rewrite seq_of_labeled_statement_eq. simpl in TEMPS.
  eapply all_below_incl.
  rewrite all_below_app in TEMPS.
  destruct TEMPS. eauto.
  eapply temps_of_lbstmts_select_switch; eauto.
  apply tr_seq_of_labeled_statement .
  eapply tr_lblstmts_mono;eauto.
  constructor;auto.
-  inv MK.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor;auto.
  destruct H0 ; subst ; inv TR; intuition congruence.
  econstructor ;eauto.
  simpl. apply all_below_nil.
  constructor.
- inv TR.
  inv MK.
  eexists.
  split.
  left.
  eapply plus_one.
  apply step_continue_switch.
  econstructor; auto.
  constructor.
  eauto.
- inv TR.
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor; eauto.
  econstructor ;eauto.
- inv TR.
  exploit tr_stmt_body  ; eauto.
  intros (tmps & TB & FR & BL).
  exploit tr_find_label; eauto.
  apply match_call_cont; eauto.
  intros (ts' & tk' & FD & TR & MC &BL').
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor; eauto.
  econstructor ;eauto.
- simpl in TR.
  monadInv TR. inv FR.
  exploit function_entry1_preserved;eauto.
  intros (le' & ENTRY & MT &BL).
  exploit tr_stmt_body;eauto.
  intros (tmps & TR & FR' & BL').
  eexists.
  split.
  left.
  eapply plus_one.
  econstructor; eauto.
  econstructor;auto.
  eauto.
  auto.
- simpl in TR.
  monadInv TR.
  eexists.
  split.
  left. eapply plus_one.
  econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor ; eauto.
- inv MK.
  eexists.
  split.
  left. eapply plus_one.
  econstructor; eauto.
  econstructor ; eauto.
  simpl. apply all_below_nil.
  eapply match_temp_set_opt; eauto.
  constructor.
  apply all_fresh_nil.
Unshelve.
exact xH.
Qed.


(** Semantic preservation *)

Theorem simulation:
  forall S1 t S2, ClightCe.step1 ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  exists S2',
     (plus step1 tge S1' t S2' \/
       (star step1 tge S1' t S2' /\ measure S2 < measure S1)%nat)
  /\ match_states S2 S2'.
Proof.
  intros S1 t S2 STEP.
  apply estep_simulation; auto.
Qed.

Lemma transl_initial_states:
  forall S,
  ClightCe.initial_state prog S ->
  exists S', Clight.initial_state tprog S' /\ match_states S S'.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros (tf & FIND & TR).
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_match (proj1 TRANSL)); eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto. 
  destruct TRANSL. destruct H as (A & B & C). simpl in B. auto. 
  eexact FIND.
  rewrite <- H3. eapply type_of_fundef_preserved; eauto.
  assert (exists fr, fresh_of_fundef f fr ).
  { destruct f. eexists; econstructor;eauto.
    eexists; econstructor;eauto.
  }
  destruct H.
  econstructor; eauto.
  constructor.
  Unshelve.  exact xH.
Qed.

Lemma transl_final_states:
  forall S S' r,
  match_states S S' -> ClightCe.final_state S r -> Clight.final_state S' r.
Proof.
  intros. inv H0. inv H. inv MK. constructor.
Qed.

Theorem transl_program_correct:
  forward_simulation (ClightCe.semantics1 prog) (Clight.semantics1 tprog).
Proof.
  eapply forward_simulation_star_wf with (order := ltof _ measure).
  eapply senv_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  apply well_founded_ltof.
  exact simulation.
Qed.

End PRESERVATION.

(** ** Commutation with linking *)

Global Instance TransfFromCeLink : TransfLink match_prog.
Proof.
  red; intros. eapply Ctypes.link_match_program; eauto.
- intros.
Local Transparent Linker_fundef.
  simpl in *; unfold link_fundef in *.
  destruct f1; monadInv H3; destruct f2; monadInv H4; try discriminate.
  destruct e; inv H2. exists (Internal x); split; auto. simpl; rewrite EQ; auto.
  destruct e; inv H2. exists (Internal x); split; auto. simpl; rewrite EQ; auto.
  destruct andb; inv H2. econstructor; split; eauto.
Qed.
