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

(** Relational specification of expression simplification. *)

Require Import Coqlib Maps Errors Integers Floats.
Require Import AST Linking Memory.
Require Import Ctypes Cop ClightCe Clight ClightFromCe.

Section SPEC.

(*Variable ce: composite_env.*)

Local Open Scope gensym_monad_scope.

(** * Relational specification of the translation. *)

(** ** Translation of expressions *)

(** This specification covers:
- all cases of [transl_lvalue] and [transl_rvalue];
- two additional cases for [Csyntax.Eparen], so that reductions of [Csyntax.Econdition]
  expressions are properly tracked;
- three additional cases allowing [Csyntax.Eval v] C expressions to match
  any Clight expression [a] that evaluates to [v] in any environment
  matching the given temporary environment [le].
*)

(*Definition final (dst: destination) (a: expr) : list statement :=
  match dst with
  | For_val => nil
  | For_effects => nil
  | For_set sd => do_set sd a
  end.

Definition tr_is_bitfield_access (l: expr) (bf: bitfield) : Prop :=
  match l with
  | Efield r f _ =>
      exists co ofs,
      match typeof r with
      | Tstruct id _ =>
          ce!id = Some co /\ field_offset ce f (co_members co) = OK (ofs, bf)
      | Tunion id _ =>
          ce!id = Some co /\ union_field_offset ce f (co_members co) = OK (ofs, bf)
      | _ => False
      end
  | _ => bf = Full
  end.

Inductive tr_rvalof: type -> expr -> list statement -> expr -> list ident -> Prop :=
  | tr_rvalof_nonvol: forall ty a tmp,
      type_is_volatile ty = false ->
      tr_rvalof ty a nil a tmp
  | tr_rvalof_vol: forall ty a t bf tmp,
      type_is_volatile ty = true -> In t tmp ->
      tr_is_bitfield_access a bf ->
      tr_rvalof ty a (make_set bf t a :: nil) (Etempvar t ty) tmp.
 *)



Inductive tr_cexpr: temp_env -> ClightCe.cexpr -> list statement -> expr -> list ident -> Prop :=
| tr_expr : forall le tmp e,
    tr_cexpr le (CE_expr e) nil (Ecast e type_bool) tmp
| tr_and  : forall le e1 sl1 a1 t tmp tmp1 e2 sl2 a2 tmp2,
  tr_cexpr le e1 sl1 a1 tmp1 ->
  tr_cexpr le  e2 sl2 a2 tmp2 ->
  list_disjoint tmp1 tmp2 ->
  incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
  tr_cexpr le  (ClightCe.CE_and e1 e2)
        (sl1 ++ makeif a1 (Ssequence (makeseq sl2) (Sset t a2 ))
           (Sset t (Econst_int Int.zero type_bool)) :: nil)
        (Etempvar t type_bool) tmp
| tr_or : forall le e1 e2 sl1 a1 tmp1 t sl2 a2 tmp2 tmp,
      tr_cexpr le e1 sl1 a1 tmp1 ->
      tr_cexpr le  e2 sl2 a2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp -> In t tmp ->
      tr_cexpr le  (ClightCe.CE_or e1 e2)
                    (sl1 ++ makeif a1 (Sset t (Econst_int Int.one type_bool))
                                      (Ssequence (makeseq sl2) (Sset t a2)) :: nil)
                    (Etempvar t type_bool) tmp
| tr_not : forall le e a sl1 tmp1 tmp,
    tr_cexpr le e sl1 a tmp1 ->
    incl tmp1 tmp ->
    tr_cexpr le (ClightCe.CE_not e) sl1  (Eunop Onotbool a type_bool) tmp.

(** Useful invariance properties. *)

Lemma tr_cexpr_invariant:
  forall le r sl a tmps, tr_cexpr le r sl a tmps ->
  forall le', (forall x, In x tmps -> le'!x = le!x) ->
  tr_cexpr le' r sl a tmps.
Proof.
  induction 1; intros; econstructor; eauto.
Qed.

(*Lemma tr_rvalof_monotone:
  forall ty a sl b tmps, tr_rvalof ty a sl b tmps ->
  forall tmps', incl tmps tmps' -> tr_rvalof ty a sl b tmps'.
Proof.
  induction 1; intros; econstructor; unfold incl in *; eauto.
Qed.
 *)

Lemma tr_cexpr_monotone:
  forall le r sl a tmps, tr_cexpr le r sl a tmps ->
  forall tmps', incl tmps tmps' -> tr_cexpr le r sl a tmps'.
Proof.
  induction 1; intros ;econstructor; unfold incl in *; eauto.
Qed.

(** ** Top-level translation *)

(** The "top-level" translation is equivalent to [tr_expr] above
  for source terms.  It brings additional flexibility in the matching
  between Csyntax values and Cminor expressions: in the case of
  [tr_expr], the Cminor expression must not depend on memory,
  while in the case of [tr_top] it can depend on the current memory
  state. *)

Section TR_TOP.

Variable ge: genv.
Variable e: env.
Variable le: temp_env.
Variable m: mem.

(*Inductive tr_top: ClightCe.expr -> list statement -> expr -> list ident -> Prop :=
  | tr_top_val_val: forall v ty a tmp,
      typeof a = ty -> eval_expr ge e le m a v ->
      tr_top For_val (ClightCe.Eval v ty) nil a tmp
  | tr_top_base: forall r sl a tmp,
      tr_expr le r sl a tmp ->
      tr_top r sl a tmp.
*)
End TR_TOP.

(** ** Translation of statements *)

Inductive tr_expression: ClightCe.cexpr -> statement -> expr -> list ident -> Prop :=
  | tr_expression_intro: forall r sl a tmps,
      (forall le , tr_cexpr le r sl a tmps) ->
      tr_expression r (makeseq sl) a tmps.
(*
Inductive tr_expr_stmt: ClightCe.expr -> statement -> Prop :=
  | tr_expr_stmt_intro: forall r sl a tmps,
      (forall ge e le m, tr_top ge e le m For_effects r sl a tmps) ->
      tr_expr_stmt r (makeseq sl).

Inductive tr_if: ClightCe.expr -> statement -> statement -> statement -> Prop :=
  | tr_if_intro: forall r s1 s2 sl a tmps,
      (forall ge e le m, tr_top ge e le m For_val r sl a tmps) ->
      tr_if r s1 s2 (makeseq (sl ++ makeif a s1 s2 :: nil)).
 *)

Inductive tr_stmt: ClightCe.statement -> statement -> list ident -> Prop :=
| tr_skip: forall tmp,
      tr_stmt ClightCe.Sskip Sskip tmp
| tr_assign  : forall e1 e2 tmp, tr_stmt (ClightCe.Sassign e1 e2) (Sassign e1 e2) tmp
| tr_set     : forall i e tmp, tr_stmt (ClightCe.Sset i e) (Sset i e) tmp
| tr_call    : forall i e l tmp, tr_stmt (ClightCe.Scall i e l) (Scall i e l) tmp
| tr_builtin : forall i ef l e tmp, tr_stmt (ClightCe.Sbuiltin i ef l e) (Sbuiltin i ef l e) tmp
| tr_seq: forall s1 s2 ts1 ts2  tmp1 tmp2 tmp,
      tr_stmt s1 ts1 tmp1 -> tr_stmt s2 ts2 tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_stmt (ClightCe.Ssequence s1 s2) (Ssequence ts1 ts2) tmp
| tr_ifthenelse: forall r s1 s2 s' a ts1 ts2 tmp1 tmp2 tmp3 tmp,
      tr_expression r s' a tmp1 ->
      tr_stmt s1 ts1 tmp2 -> tr_stmt s2 ts2 tmp3 ->
      list_disjoint tmp1 tmp2 -> list_disjoint tmp1 tmp3 ->
      list_disjoint tmp2 tmp3 ->
      incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp ->
      tr_stmt (ClightCe.Sifthenelse r s1 s2) (Ssequence s' (Sifthenelse a ts1 ts2)) tmp
| tr_loop: forall s1 ts1 s2 ts2 tmp1 tmp2 tmp,
    tr_stmt s1 ts1 tmp1 ->
    tr_stmt s2 ts2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    incl tmp1 tmp -> incl tmp2 tmp ->
    tr_stmt (ClightCe.Sloop s1 s2) (Sloop ts1 ts2) tmp
| tr_break: forall tmp,
      tr_stmt ClightCe.Sbreak Sbreak tmp
  | tr_continue: forall tmp,
      tr_stmt ClightCe.Scontinue Scontinue tmp
  | tr_return: forall e tmp,
      tr_stmt (ClightCe.Sreturn e) (Sreturn e) tmp
  | tr_switch: forall r ls tls tmp1 tmp,
      tr_lblstmts ls tls tmp1 ->
      incl tmp1 tmp ->
      tr_stmt (ClightCe.Sswitch r ls) (Sswitch r tls) tmp
  | tr_label: forall lbl s ts tmp,
      tr_stmt s ts tmp ->
      tr_stmt (ClightCe.Slabel lbl s) (Slabel lbl ts) tmp
  | tr_goto: forall lbl tmp,
      tr_stmt (ClightCe.Sgoto lbl) (Sgoto lbl) tmp

with tr_lblstmts: ClightCe.labeled_statements -> labeled_statements -> list ident -> Prop :=
  | tr_ls_nil: forall tmp,
      tr_lblstmts ClightCe.LSnil LSnil tmp
  | tr_ls_cons: forall c s ls ts tls tmp1 tmp2 tmp,
      tr_stmt s ts tmp1 ->
      tr_lblstmts ls tls tmp2 ->
      list_disjoint tmp1 tmp2 ->
      incl tmp1 tmp -> incl tmp2 tmp ->
      tr_lblstmts (ClightCe.LScons c s ls) (LScons c ts tls) tmp.

(** * Correctness proof with respect to the specification. *)

(** ** Properties of the monad *)

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B) (y: B) (z1 z3: generator) I,
  bind f g z1 = Res y z3 I ->
  exists x, exists z2, exists I1, exists I2,
  f z1 = Res x z2 I1 /\ g x z2 = Res y z3 I2.
Proof.
  intros until I. unfold bind. destruct (f z1).
  congruence.
  caseEq (g a g'); intros; inv H0.
  econstructor; econstructor; econstructor; econstructor; eauto.
Qed.

Remark bind2_inversion:
  forall (A B Csyntax: Type) (f: mon (A*B)) (g: A -> B -> mon Csyntax) (y: Csyntax) (z1 z3: generator) I,
  bind2 f g z1 = Res y z3 I ->
  exists x1, exists x2, exists z2, exists I1, exists I2,
  f z1 = Res (x1,x2) z2 I1 /\ g x1 x2 z2 = Res y z3 I2.
Proof.
  unfold bind2. intros.
  exploit bind_inversion; eauto.
  intros [[x1 x2] [z2 [I1 [I2 [P Q]]]]]. simpl in Q.
  exists x1; exists x2; exists z2; exists I1; exists I2; auto.
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (Res _ _ _ = Res _ _ _) =>
      inversion H; clear H; try subst
  | (@ret _ _ _ = Res _ _ _) =>
      inversion H; clear H; try subst
  | (@error _ _ _ = Res _ _ _) =>
      inversion H
  | (bind ?F ?G ?Z = Res ?X ?Z' ?I) =>
      let x := fresh "x" in (
      let z := fresh "z" in (
      let I1 := fresh "I" in (
      let I2 := fresh "I" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X Z Z' I H) as [x [z [I1 [I2 [EQ1 EQ2]]]]];
      clear H;
      try (monadInv1 EQ2)))))))
   | (bind2 ?F ?G ?Z = Res ?X ?Z' ?I) =>
      let x := fresh "x" in (
      let y := fresh "y" in (
      let z := fresh "z" in (
      let I1 := fresh "I" in (
      let I2 := fresh "I" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion _ _ _ F G X Z Z' I H) as [x [y [z [I1 [I2 [EQ1 EQ2]]]]]];
      clear H;
      try (monadInv1 EQ2))))))))
 end.

Ltac monadInv H :=
  match type of H with
  | (@ret _ _ _ = Res _ _ _) => monadInv1 H
  | (@error _ _ _ = Res _ _ _) => monadInv1 H
  | (bind ?F ?G ?Z = Res ?X ?Z' ?I) => monadInv1 H
  | (bind2 ?F ?G ?Z = Res ?X ?Z' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ = Res _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

(** ** Freshness and separation properties. *)

Definition within (id: ident) (g1 g2: generator) : Prop :=
  Ple (gen_next g1) id /\ Plt id (gen_next g2).

Lemma gensym_within:
  forall ty g1 id g2 I,
  gensym ty g1 = Res id g2 I -> within id g1 g2.
Proof.
  intros. monadInv H. split. apply Ple_refl. apply Plt_succ.
Qed.

Lemma within_widen:
  forall id g1 g2 g1' g2',
  within id g1 g2 ->
  Ple (gen_next g1') (gen_next g1) ->
  Ple (gen_next g2) (gen_next g2') ->
  within id g1' g2'.
Proof.
  intros. destruct H. split.
  eapply Ple_trans; eauto.
  eapply Plt_Ple_trans; eauto.
Qed.

Definition contained (l: list ident) (g1 g2: generator) : Prop :=
  forall id, In id l -> within id g1 g2.

Lemma contained_nil:
  forall g1 g2, contained nil g1 g2.
Proof.
  intros; red; intros; contradiction.
Qed.

Lemma contained_widen:
  forall l g1 g2 g1' g2',
  contained l g1 g2 ->
  Ple (gen_next g1') (gen_next g1) ->
  Ple (gen_next g2) (gen_next g2') ->
  contained l g1' g2'.
Proof.
  intros; red; intros. eapply within_widen; eauto.
Qed.

Lemma contained_cons:
  forall id l g1 g2,
  within id g1 g2 -> contained l g1 g2 -> contained (id :: l) g1 g2.
Proof.
  intros; red; intros. simpl in H1; destruct H1. subst id0. auto. auto.
Qed.

Lemma contained_app:
  forall l1 l2 g1 g2,
  contained l1 g1 g2 -> contained l2 g1 g2 -> contained (l1 ++ l2) g1 g2.
Proof.
  intros; red; intros. destruct (in_app_or _ _ _ H1); auto.
Qed.

Lemma contained_disjoint:
  forall g1 l1 g2 l2 g3,
  contained l1 g1 g2 -> contained l2 g2 g3 -> list_disjoint l1 l2.
Proof.
  intros; red; intros. red; intro; subst y.
  exploit H; eauto. intros [A B]. exploit H0; eauto. intros [C D].
  elim (Plt_strict x). apply Plt_Ple_trans with (gen_next g2); auto.
Qed.

Lemma contained_notin:
  forall g1 l g2 id g3,
  contained l g1 g2 -> within id g2 g3 -> ~In id l.
Proof.
  intros; red; intros. exploit H; eauto. intros [C D]. destruct H0 as [A B].
  elim (Plt_strict id). apply Plt_Ple_trans with (gen_next g2); auto.
Qed.

Hint Resolve gensym_within within_widen contained_widen
             contained_cons contained_app contained_disjoint
             contained_notin contained_nil
             incl_refl incl_tl incl_app incl_appl incl_appr incl_same_head incl_cons
             in_eq in_cons in_or_app
             Ple_trans Ple_refl: gensym.

(** ** Properties of destinations *)

(*Definition dest_below (dst: destination) (g: generator) : Prop :=
  match with
  | For_set sd => Plt (sd_temp sd) g.(gen_next)
  | _ => True
  end.

Lemma dest_below_le:
  forall g1 g2,
  dest_below g1 -> Ple g1.(gen_next) g2.(gen_next) -> dest_below g2.
Proof.
  intros. destruct dst; simpl in *; eauto using Plt_Ple_trans.
Qed.

Remark dest_for_val_below: forall g, dest_below For_val g.
Proof. intros; simpl; auto. Qed.

Remark dest_for_effect_below: forall g, dest_below For_effects g.
Proof. intros; simpl; auto. Qed.

Lemma dest_for_set_base_below: forall tmp tycast ty g1 g2,
  within tmp g1 g2 -> dest_below (For_set (SDbase tycast ty tmp)) g2.
Proof.
  intros. destruct H. auto.
Qed.

Hint Resolve dest_below_le dest_for_set_base_below : gensym.
Local Hint Resolve dest_for_val_below dest_for_effect_below : core.

(** ** Properties of [temp_for_sd] *)

Definition good_temp_for_sd (ty: type) (tmp: ident) (sd: set_destination) (g1 g2 g3: generator) : Prop :=
     Plt (sd_temp sd) g1.(gen_next)
  /\ Ple g1.(gen_next) g2.(gen_next)
  /\ Ple g2.(gen_next) g3.(gen_next)
  /\ if type_eq ty (sd_head_type sd) then tmp = sd_temp sd else within tmp g2 g3.

Lemma temp_for_sd_charact: forall ty tmp sd g1 g2 g3 I,
  dest_below (For_set sd) g1 ->
  temp_for_sd ty sd g2 = Res tmp g3 I ->
  Ple g1.(gen_next) g2.(gen_next) ->
  good_temp_for_sd ty tmp sd g1 g2 g3.
Proof.
  unfold temp_for_sd, good_temp_for_sd; intros. destruct type_eq.
- inv H0. tauto.
- eauto with gensym.
Qed.

Lemma dest_for_set_cons_below: forall tycast ty tmp sd g1 g2 g3,
  good_temp_for_sd ty tmp sd g1 g2 g3 ->
  dest_below (For_set (SDcons tycast ty tmp sd)) g3.
Proof.
  intros until g3; intros (P & Q & R & S). simpl. destruct type_eq.
- subst tmp. unfold Ple, Plt in *; lia.
- destruct S; auto.
Qed.

Lemma sd_temp_notin:
  forall sd g1 g2 l, dest_below (For_set sd) g1 -> contained l g1 g2 -> ~In (sd_temp sd) l.
Proof.
  intros. simpl in H. red; intros. exploit H0; eauto. intros [A B].
  elim (Plt_strict (sd_temp sd)). apply Plt_Ple_trans with (gen_next g1); auto.
Qed.

Definition used_temp_for_sd (ty: type) (tmp: ident) (sd: set_destination) : list ident :=
  if type_eq ty (sd_head_type sd) then nil else tmp :: nil.

Lemma temp_for_sd_disj: forall tmp1 tmp2 ty t sd g1 g2 g3 g4,
  good_temp_for_sd ty t sd g1 g2 g3 ->
  contained tmp1 g1 g2 ->
  contained tmp2 g3 g4 ->
  list_disjoint tmp1 (t :: tmp2).
Proof.
  intros. destruct H as (P & Q & R & S).
  apply list_disjoint_cons_r; eauto with gensym.
  destruct type_eq.
- subst t. eapply sd_temp_notin; eauto.
- eauto with gensym.
Qed.

Lemma temp_for_sd_in: forall tmp ty t sd g1 g2 g3,
  good_temp_for_sd ty t sd g1 g2 g3 ->
  In t (sd_temp sd :: used_temp_for_sd ty t sd ++ tmp).
Proof.
  intros. destruct H as (P & Q & R & S). unfold used_temp_for_sd. destruct type_eq.
- subst t. auto with coqlib.
- simpl; auto.
Qed.

Lemma temp_for_sd_contained: forall ty t sd g1 g2 g3,
  good_temp_for_sd ty t sd g1 g2 g3 ->
  contained (used_temp_for_sd ty t sd) g2 g3.
Proof.
  intros. destruct H as (P & Q & R & S). unfold used_temp_for_sd.
  destruct type_eq; eauto with gensym.
Qed.

Hint Resolve temp_for_sd_charact dest_for_set_cons_below
             sd_temp_notin temp_for_sd_disj temp_for_sd_in temp_for_sd_contained: gensym.
*)
(** ** Correctness of the translation functions *)
(*
Lemma finish_meets_spec_1:
  forall sl a sl' a',
  finish sl a = (sl', a') -> sl' = sl ++ final a.
Proof.
  intros. destruct dst; simpl in *; inv H; rewrite ? app_nil_r; auto.
Qed.

Lemma finish_meets_spec_2:
  forall sl a sl' a',
  finish sl a = (sl', a') -> a' = a.
Proof.
  intros. destruct dst; simpl in *; inv H; auto.
Qed.

Ltac UseFinish :=
  match goal with
  | [ H: finish _ _ _ = (_, _) |- _ ] =>
      try (rewrite (finish_meets_spec_2 _ _ _ _ _ H));
      try (rewrite (finish_meets_spec_1 _ _ _ _ _ H));
      repeat rewrite app_ass
  end.

Definition add_dest (dst: destination) (tmps: list ident) :=
  match with
  | For_set sd => sd_temp sd :: tmps
  | _ => tmps
  end.

Lemma add_dest_incl:
  forall tmps, incl tmps (add_dest tmps).
Proof.
  intros. destruct dst; simpl; eauto with coqlib.
Qed.

Lemma tr_expr_add_dest:
  forall le r sl a tmps,
  tr_expr le r sl a tmps ->
  tr_expr le r sl a (add_dest tmps).
Proof.
  intros. apply tr_expr_monotone with tmps; auto. apply add_dest_incl.
Qed.


Lemma is_bitfield_access_meets_spec: forall l g bf g' I,
  is_bitfield_access ce l g = Res bf g' I ->
  tr_is_bitfield_access l bf.
Proof.
  unfold is_bitfield_access; intros; red. destruct l; try (monadInv H; auto).
  assert (AUX: forall fn id,
               is_bitfield_access_aux ce fn id i g = Res bf g' I ->
               exists co ofs,
               ce!id = Some co /\ fn ce i (co_members co) = OK (ofs, bf)).
  { unfold is_bitfield_access_aux; intros.
    destruct ce!id as [co|]; try discriminate.
    destruct (fn ce i (co_members co)) as [[ofs1 bf1]|] eqn:FN; inv H0.
    exists co, ofs1; auto. }
  destruct (typeof l); try discriminate; apply AUX; auto.
Qed.

Lemma transl_valof_meets_spec:
  forall ty a g sl b g' I,
  transl_valof ce ty a g = Res (sl, b) g' I ->
  exists tmps, tr_rvalof ty a sl b tmps /\ contained tmps g g'.
Proof.
  unfold transl_valof; intros.
  destruct (type_is_volatile ty) eqn:?; monadInv H.
  exists (x :: nil); split; eauto with gensym.
  econstructor; eauto using is_bitfield_access_meets_spec with coqlib.
  exists (@nil ident); split; eauto with gensym. constructor; auto.
Qed.

Scheme expr_ind2 := Induction for ClightCe.expr Sort Prop
  with exprlist_ind2 := Induction for ClightCe.exprlist Sort Prop.
Combined Scheme expr_exprlist_ind from expr_ind2, exprlist_ind2.
 *)



Lemma transl_meets_spec:
   (forall r g sl a g' I,
    transl_cexpr r g = Res (sl, a) g' I ->
    exists tmps, (forall le, tr_cexpr le r sl a tmps) /\ contained tmps g g').
Proof.
  induction r;intros.
  - (* expr *) simpl in H.
    monadInv H.
    exists nil.
    split;auto with gensym.
    constructor.
  - (* and *)
    simpl in H. monadInv H.
    exploit IHr1;eauto.
    intros (tmps1 & TE1 & C1).
    exploit IHr2;eauto.
    intros (tmps2 & TE2 & C2).
    exists (x0 :: tmps1 ++ tmps2); split.
    intros; econstructor; eauto with gensym.
    apply contained_cons. eauto with gensym.
    apply contained_app; eauto with gensym.
  - (* or *)
    simpl in H. monadInv H.
    exploit IHr1;eauto.
    intros (tmps1 & TE1 & C1).
    exploit IHr2;eauto.
    intros (tmps2 & TE2 & C2).
    exists (x0 :: tmps1 ++ tmps2); split.
    intros; econstructor; eauto with gensym.
    apply contained_cons. eauto with gensym.
    apply contained_app; eauto with gensym.
  - (* not *)
    simpl in H. monadInv H.
    exploit IHr;eauto.
    intros (tmps1 & TE1 & C1).
    exists (tmps1); split.
    intros.
    econstructor. eauto.
    apply incl_refl. auto.
Qed.

(*Lemma transl_expr_meets_spec:
   forall r g sl a g' I,
   transl_expr ce r g = Res (sl, a) g' I ->
   dest_below g ->
   exists tmps, forall ge e le m, tr_top ge e le m r sl a tmps.
Proof.
  intros. exploit (proj1 transl_meets_spec); eauto. intros [tmps [A B]].
  exists (add_dest tmps); intros. apply tr_top_base. auto.
Qed.

Lemma transl_expression_meets_spec:
  forall r g s a g' I,
  transl_expression ce r g = Res (s, a) g' I ->
  tr_expression r s a.
Proof.
  intros. monadInv H. exploit transl_expr_meets_spec; eauto.
  intros [tmps A]. econstructor; eauto.
Qed.

Lemma transl_expr_stmt_meets_spec:
  forall r g s g' I,
  transl_expr_stmt ce r g = Res s g' I ->
  tr_expr_stmt r s.
Proof.
  intros. monadInv H. exploit transl_expr_meets_spec; eauto.
  intros [tmps A]. econstructor; eauto.
Qed.

Lemma transl_if_meets_spec:
  forall r s1 s2 g s g' I,
  transl_if ce r s1 s2 g = Res s g' I ->
  tr_if r s1 s2 s.
Proof.
  intros. monadInv H. exploit transl_expr_meets_spec; eauto.
  intros [tmps A]. econstructor; eauto.
Qed.
 *)

Ltac split_and :=
  repeat match goal with
    | |- _ /\ _ => split
    end.

Lemma list_disjoint_nil_r : forall {A: Type} (l:list A),
    list_disjoint l nil.
Proof.
  unfold list_disjoint. simpl. tauto.
Qed.

Hint Resolve list_disjoint_nil_r : gensym.

(*Lemma list_disjoint_app : forall {A: Type} (s1 s2 tmp1 tmp2:list A),
    list_disjoint s1 tmp1 ->
    list_disjoint s2 tmp2 ->
    list_disjoint tmp1 tmp2 ->
    list_disjoint (s1 ++  s2) (tmp1 ++ tmp2).
Proof.
  unfold list_disjoint.
  intros.
  rewrite in_app_iff in *.
  intro ; subst.
  destruct H2;destruct H3.
  specialize (H _ _ H2 H3); tauto.
*)

Definition lt_gen (l:list ident) (g:generator) :=
  forall x, In x l -> Plt x (gen_next g).

Lemma lt_gen_app : forall l1 l2 g,
    lt_gen l1 g ->
    lt_gen l2 g ->
    lt_gen (l1 ++ l2) g.
Proof.
  intros.
  unfold lt_gen in *.
  intros. rewrite in_app_iff in H1.
  destruct H1.
  apply H;auto.
  apply H0;auto.
Qed.


Lemma lt_gen_appl : forall l1 l2 g,
    lt_gen (l1 ++ l2) g ->
    lt_gen l1 g.
Proof.
  intros.
  unfold lt_gen in *.
  intros. apply H.
  rewrite in_app_iff.
  tauto.
Qed.

Lemma lt_gen_appr : forall l1 l2 g,
    lt_gen (l1 ++ l2) g ->
    lt_gen l2 g.
Proof.
  intros.
  unfold lt_gen in *.
  intros. apply H.
  rewrite in_app_iff.
  tauto.
Qed.

Lemma lt_gen_le : forall l1 g g',
    lt_gen l1 g ->
    Ple (gen_next g) (gen_next g') ->
    lt_gen l1 g'.
Proof.
  unfold lt_gen.
  intros.
  apply H in H1.
  unfold Plt,Ple in *. lia.
Qed.


Hint Resolve lt_gen_appl lt_gen_appr lt_gen_le: gensym.


Lemma transl_stmt_meets_spec:
  forall s g ts g' I, transl_stmt s g = Res ts g' I ->
                      exists tmps, tr_stmt s ts tmps /\ contained tmps g g'
with transl_lblstmt_meets_spec:
  forall s g ts g' I, transl_lblstmt s g = Res ts g' I ->
                      exists tmps, tr_lblstmts s ts tmps /\ contained tmps g g'.
Proof.
(*  generalize transl_expression_meets_spec transl_expr_stmt_meets_spec transl_if_meets_spec; intros T1 T2 T3.*)
(*Opaque transl_expression transl_expr_stmt. *)
  clear transl_stmt_meets_spec.
  { induction s; simpl; intros until I; intros TR;
  try (monadInv TR).
    - (* Skip *)
      exists nil; split_and.
      + constructor.
      + auto with gensym.
    - (* Sassign *)
      exists nil; split_and.
      + constructor.
      + auto with gensym.
    - (* Sset *)
      exists nil; split_and.
      + constructor.
      + auto with gensym.
    -  (* Call *)
      exists nil; split_and.
      + constructor.
      + auto with gensym.
    - (* Builtin *)
      exists nil; split_and.
      + constructor.
      + auto with gensym.
    - (* Sequence *)
      exploit IHs1; eauto with gensym.
      intros (tmp1 & TR1 & C1).
    exploit IHs2; eauto with gensym.
    intros (tmp2 & Tr2 & C2).
    eexists; split_and.
    + econstructor. eauto. eauto.
      eauto with gensym.
      apply incl_appl.
      apply incl_refl.
      apply incl_appr.
      apply incl_refl.
    + eauto with gensym.
    - (* Sifthenelse *)
    exploit IHs1; eauto.
    intros (tmp1 & TS1 & C1).
    exploit IHs2; eauto.
    intros (tmp2 & TS2 & C2).
    exploit transl_meets_spec; eauto.
    intros (tmps3 & (TR3 & C3)).
    eexists. split.
    econstructor; eauto.
    econstructor;eauto.
    eauto with gensym.
    eauto with gensym.
    eauto with gensym.
    eapply incl_appr.
    eapply incl_appr.
    eapply incl_refl.
    eapply incl_appl.
    eapply incl_refl.
    eapply incl_appr.
    eapply incl_appl.
    eapply incl_refl.
    apply contained_app.
    eauto with gensym.
    apply contained_app.
    eauto with gensym.
    eauto with gensym.
  - exploit IHs1; eauto.
    intros (tmp1 & TR1 & C1).
    exploit IHs2; eauto.
    intros (tmp2 & Tr2 & C2).
    eexists; split.
    econstructor. eauto. eauto.
    eauto with gensym.
    apply incl_appl.
    apply incl_refl.
    apply incl_appr.
    apply incl_refl.
    eauto with gensym.
  - (* Break *)
      exists nil; split_and.
      + constructor.
      + auto with gensym.
  - (* Continue *)
      exists nil; split_and.
      + constructor.
      + auto with gensym.
  -  (* Return *)
      exists nil; split_and.
      + constructor.
      + auto with gensym.
  - exploit transl_lblstmt_meets_spec; eauto.
    intros (tmp1 & TR1 & C1).
    eexists; split.
    econstructor. eauto.
    eauto with gensym.
    eauto with gensym.
  - exploit IHs; eauto.
    intros (tmp1 & TR1 & C1).
    eexists; split.
    econstructor. eauto. eauto.
  - (* Goto *)
      exists nil; split_and.
      + constructor.
      + auto with gensym.
  }
  { clear transl_lblstmt_meets_spec.
    induction s; simpl; intros until I; intros TR;
      monadInv TR.
    - eexists ; split.
      econstructor. eauto with gensym.
    - exploit IHs; eauto.
      intros (tmp1 & T1 & C1).
      exploit transl_stmt_meets_spec; eauto.
      intros (tmp2 & T2 & C2).
      eexists; split.
      econstructor; eauto.
      eauto with gensym.
      apply incl_appl.
      apply incl_refl.
      apply incl_appr.
      apply incl_refl.
      eauto with gensym.
  }
Qed.



(** Relational presentation for the transformation of functions, fundefs, and variables. *)

Inductive tr_function: ClightCe.function -> Clight.function -> Prop :=
  | tr_function_intro: forall f tf tmp,
      tr_stmt f.(ClightCe.fn_body) tf.(fn_body) tmp ->
      fn_return tf = ClightCe.fn_return f ->
      fn_callconv tf = ClightCe.fn_callconv f ->
      fn_params tf = ClightCe.fn_params f ->
      fn_vars tf = ClightCe.fn_vars f ->
      list_disjoint (List.map fst (ClightCe.fn_temps f)) tmp ->
      tr_function f tf.

Lemma list_disjoint_lt : forall x l1 l2,
    (forall v, In v l1 -> Plt v x) ->
    (forall v, In v l2 -> Ple x v) ->
    list_disjoint l1 l2.
Proof.
  unfold list_disjoint.
  repeat intro. subst.
  apply H in H1.
  apply H0 in H2. unfold Plt,Ple in *.
  lia.
Qed.

Lemma max_ident_init : forall l x y,
    Ple x y ->
    Ple x (max_ident y l).
Proof.
  unfold max_ident, Ple.
  induction l; simpl.
  - lia.
  - intros.
    apply IHl.
    lia.
Qed.

Lemma max_ident_list : forall l x t y,
    In (x,t) l ->
    Ple x (max_ident y l).
Proof.
  unfold max_ident, Ple.
  induction l; simpl.
  - lia.
  - intros.
    destruct H; subst.
    simpl.
    apply max_ident_init. unfold Ple; lia.
    eapply IHl. eauto.
Qed.


Lemma lt_temps_fresh_id :
  forall f (v : positive), In v (map fst (ClightCe.fn_temps f)) -> Plt v (fresh_id f).
Proof.
  unfold fresh_id.
  intros.
  unfold Plt.
  assert ((v <=    max_ident
     (max_ident (max_ident 1 (ClightCe.fn_params f)) (ClightCe.fn_vars f))
     (ClightCe.fn_temps f))%positive).
  {
    rewrite in_map_iff in H.
    destruct H as ((v1,t1) & EQ & IN).
    simpl in EQ. subst.
    eapply max_ident_list. eauto.
  }
  lia.
Qed.

Lemma transl_function_spec:
  forall f tf,
  transl_function f = OK tf ->
  tr_function f tf.
Proof.
  unfold transl_function; intros.
  destruct (forallb (fun x : positive => (x <? fresh_id f)%positive)
              (temps_of_stmt (ClightCe.fn_body f))) eqn:ALL; try discriminate.
  destruct (transl_stmt (ClightCe.fn_body f) (make_generator (fresh_id f))) eqn:T; inv H.
  exploit transl_stmt_meets_spec;eauto.
  intros (tmp & TR & C).
  econstructor; eauto.
  apply list_disjoint_lt with (x:= fresh_id f).
  intros.
  eapply lt_temps_fresh_id ; eauto.
  unfold contained in C.
  intros.
  apply C in H. unfold within in H. simpl in H. tauto.
Qed.

End SPEC.

Inductive tr_fundef (p: ClightCe.program): ClightCe.fundef -> Clight.fundef -> Prop :=
  | tr_internal: forall f tf,
      tr_function  f tf ->
      tr_fundef p (Internal f) (Internal tf)
  | tr_external: forall ef targs tres cconv,
      tr_fundef p (External ef targs tres cconv) (External ef targs tres cconv).

Lemma transl_fundef_spec:
  forall p fd tfd,
  transl_fundef  fd = OK tfd ->
  tr_fundef p fd tfd.
Proof.
  unfold transl_fundef; intros.
  destruct fd; Errors.monadInv H.
+ constructor. eapply transl_function_spec; eauto.
+ constructor.
Qed.
