(* ============================================================
   Completeness of the deduction system over fuzzy relations
   ============================================================ *)

(** Completeness of the full (infinitary) system, following Section 5 of
    Mio, Sarkis and Vignudelli, "Universal Quantitative Algebra for Fuzzy
    Relations and Generalised Metric Spaces" ([27] in the paper on compact
    quantitative theories).  Fix a theory [E] and a context [X].  The term
    model [F(X)] has as carrier the terms over [X] modulo provable equality,
    and as fuzzy relation the infimum of the derivable bounds.  It is a model
    of [E], and a judgement over [X] holds in it under the interpretation of
    the generators exactly when the judgement is derivable. *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssralg ssrnum reals fintype preorder.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import numfield.

From Template Require Import Signature FuzzyRelation FRelDeduction.

Import preorder.Order.PreorderTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** The witness chosen by [cid] depends only on the predicate. *)
Lemma cid_irrelevance (T : Type) (P Q : T -> Prop)
    (p : exists x, P x) (q : exists x, Q x) :
  P = Q -> sval (cid p) = sval (cid q).
Proof.
  move => HPQ.
  subst Q.
  by rewrite (Prop_irrelevance p q).
Qed.

Section TermModel.

Context {R : realType} {sig : signature}.
Variable E : fuzzy_theory R sig.
Variable X : fuzzy_space R.

Local Notation tm := (term sig (fcarrier X)).

(* ------------------------------------------------------------
   Provable equality and canonical representatives (Def 5.2)
   ------------------------------------------------------------ *)

Definition tm_equiv (s t : tm) : Prop :=
  @derives_full R sig E X (EqJ s t).

Lemma tm_equiv_refl s : tm_equiv s s.
Proof. exact: FD_EqRefl. Qed.

Lemma tm_equiv_sym s t : tm_equiv s t -> tm_equiv t s.
Proof. exact: FD_EqSym. Qed.

Lemma tm_equiv_trans s t u : tm_equiv s t -> tm_equiv t u -> tm_equiv s u.
Proof. exact: FD_EqTrans. Qed.

Lemma tm_equiv_ex s : exists t, tm_equiv s t.
Proof. exists s; exact: tm_equiv_refl. Qed.

(** A representative of the class of [s], the same for every member of the
    class.  This plays the role of the choice function [c] of Lemma 5.7. *)
Definition tm_repr (s : tm) : tm := sval (cid (tm_equiv_ex s)).

Lemma tm_reprP s : tm_equiv s (tm_repr s).
Proof. exact: (svalP (cid (tm_equiv_ex s))). Qed.

Lemma tm_repr_eq s t : tm_equiv s t -> tm_repr s = tm_repr t.
Proof.
  move => Hst.
  apply: cid_irrelevance.
  apply: funext => u.
  apply: propext; split => H.
  - exact: tm_equiv_trans (tm_equiv_sym Hst) H.
  - exact: tm_equiv_trans Hst H.
Qed.

Lemma tm_repr_idem s : tm_repr (tm_repr s) = tm_repr s.
Proof.
  apply: tm_repr_eq.
  exact: tm_equiv_sym (tm_reprP s).
Qed.

(** The quotient of the terms by provable equality, as the type of the
    canonical representatives. *)
Definition tm_class : Type := {s : tm | tm_repr s = s}.

Definition tm_cls (s : tm) : tm_class := exist _ (tm_repr s) (tm_repr_idem s).

Lemma tm_class_eq (c c' : tm_class) :
  tm_equiv (sval c) (sval c') -> c = c'.
Proof.
  case: c c' => [s Hs] [t Ht] /= Hst.
  have Heq : s = t by rewrite -Hs -Ht; exact: tm_repr_eq.
  subst t.
  by rewrite (Prop_irrelevance Hs Ht).
Qed.

(* ------------------------------------------------------------
   The fuzzy relation on terms (Def 5.2, Lemma 5.3)
   ------------------------------------------------------------ *)

Definition tm_bounds (s t : tm) : set R :=
  [set eps | @derives_full R sig E X (QEqJ eps s t)].

Definition tm_dist (s t : tm) : R := inf (tm_bounds s t).

Lemma tm_bounds_nonempty s t : tm_bounds s t !=set0.
Proof. exists 1; exact: FD_Max. Qed.

Hypothesis Hnonneg : fuzzy_theory_nonneg E.

Lemma tm_bounds_lbound s t : lbound (tm_bounds s t) 0.
Proof.
  move => eps Heps.
  exact: (frel_derives_nonneg Hnonneg Heps).
Qed.

Lemma tm_bounds_has_lbound s t : has_lbound (tm_bounds s t).
Proof. exists 0; exact: tm_bounds_lbound. Qed.

Lemma tm_dist_range s t : 0 <= tm_dist s t <= 1.
Proof.
  apply/andP; split.
  - apply: lb_le_inf (tm_bounds_nonempty s t) _.
    exact: tm_bounds_lbound.
  - apply: (ge_inf (tm_bounds_has_lbound s t)).
    exact: FD_Max.
Qed.

(** Lemma 5.3: a bound is derivable exactly when it dominates the infimum
    of the derivable bounds.  The converse direction is where the infinitary
    rule [FD_OrderComplete] is needed. *)
Lemma tm_distP eps s t :
  @derives_full R sig E X (QEqJ eps s t) <-> tm_dist s t <= eps.
Proof.
  split => [Hderive | Hle].
  - exact: (ge_inf (tm_bounds_has_lbound s t)).
  - apply: FD_Up Hle _.
    apply: FD_OrderComplete => delta Hdelta.
    have [eps' Heps' Hlt] := inf_lt (tm_bounds_nonempty s t) Hdelta.
    exact: FD_Up (ltW Hlt) Heps'.
Qed.

(* ------------------------------------------------------------
   The term model F(X) (Def 5.4 - Def 5.6)
   ------------------------------------------------------------ *)

Definition tm_space : fuzzy_space R :=
  {| fcarrier := tm_class;
     frel := fun c c' => tm_dist (sval c) (sval c');
     frel_range := fun c c' => tm_dist_range (sval c) (sval c') |}.

Definition tm_ops : algebra_ops sig tm_class :=
  fun f args => tm_cls (App f (fun i => sval (args i))).

Definition tm_algebra : FuzzyAlgebra R sig :=
  {| fa_space := tm_space; fa_ops := tm_ops |}.

Lemma subst_term_equiv (Y : Type) (sigma tau : Y -> tm) (s : term sig Y) :
  (forall y, tm_equiv (sigma y) (tau y)) ->
  tm_equiv (subst_term sigma s) (subst_term tau s).
Proof.
  move => Hst.
  elim: s => [y | f args IH] /=; first exact: Hst.
  apply: FD_EqCong => i.
  exact: IH.
Qed.

(** Lemma 5.7: evaluating a term in the term model amounts to substituting
    the representatives picked by the interpretation. *)
Lemma tm_evalP (Y : Type) (rho : Y -> tm_class) (s : term sig Y) :
  tm_equiv (sval (fuzzy_eval tm_algebra rho s))
    (subst_term (fun y => sval (rho y)) s).
Proof.
  elim: s => [y | f args IH] /=; first exact: tm_equiv_refl.
  apply: tm_equiv_trans (tm_equiv_sym (tm_reprP _)) _.
  apply: FD_EqCong => i.
  exact: IH.
Qed.

(** Lemma 5.8: the term model is a model of [E]. *)
Lemma tm_models : fuzzy_models tm_algebra E.
Proof.
  move => Y phi HE rho.
  pose sigma y := sval (rho y).
  have Hsubst : @derives_full R sig E X (subst_judgement sigma phi).
    apply: FD_Subst (FD_Init _ HE) _ => x y.
    apply/tm_distP.
    exact: (interpretation_nexp rho).
  case: phi HE Hsubst => [s t | eps s t] _ /= Hsubst.
  - apply: tm_class_eq.
    apply: tm_equiv_trans (tm_evalP rho s) _.
    apply: tm_equiv_trans Hsubst _.
    exact: tm_equiv_sym (tm_evalP rho t).
  - apply/tm_distP.
    apply: FD_QEqReplaceL (tm_evalP rho s) _.
    apply: FD_QEqReplaceR Hsubst _.
    exact: tm_equiv_sym (tm_evalP rho t).
Qed.

(* ------------------------------------------------------------
   The interpretation of the generators (Lemma 5.9, Lemma 5.12)
   ------------------------------------------------------------ *)

Lemma tm_var_nexp :
  frel_nonexpansive X tm_space (fun x => tm_cls (Var x)).
Proof.
  move => x y /=.
  apply/tm_distP.
  apply: FD_QEqReplaceL (tm_equiv_sym (tm_reprP (Var x))) _.
  apply: FD_QEqReplaceR (tm_reprP (Var y)).
  exact: FD_UseVariables.
Qed.

Definition tm_var : interpretation X tm_algebra :=
  @Build_interpretation R sig X tm_algebra _ tm_var_nexp.

Lemma tm_var_evalP s : tm_equiv (sval (fuzzy_eval tm_algebra tm_var s)) s.
Proof.
  apply: tm_equiv_trans (tm_evalP tm_var s) _.
  rewrite -[X in tm_equiv _ X]subst_term_var.
  apply: subst_term_equiv => x.
  exact: tm_equiv_sym (tm_reprP (Var x)).
Qed.

End TermModel.

(** Completeness of the full (infinitary) system, [27, Theorem 5.13]. *)
Theorem derives_full_complete
    {R : realType} {sig : signature}
    (E : fuzzy_theory R sig) (X : fuzzy_space R)
    (phi : @judgement R sig (fcarrier X)) :
  fuzzy_theory_nonneg E ->
  fuzzy_consequence E phi ->
  derives_full E phi.
Proof.
  move => Hnonneg Hcons.
  have Hsat := Hcons _ (@tm_models R sig E X Hnonneg)
    (@tm_var R sig E X Hnonneg).
  have Heval := @tm_var_evalP R sig E X Hnonneg.
  case: phi Hcons Hsat => [s t | eps s t] _ /= Hsat.
  - apply: FD_EqTrans (FD_EqSym (Heval s)) _.
    rewrite Hsat.
    exact: Heval.
  - apply: FD_QEqReplaceL (FD_EqSym (Heval s)) _.
    apply: FD_QEqReplaceR (Heval t).
    apply/(@tm_distP R sig E X Hnonneg).
    exact: Hsat.
Qed.

(** Together with [derives_full_sound]: derivability in the full system and
    semantic consequence coincide, [27, Corollary 5.14]. *)
Corollary derives_full_iff_consequence
    {R : realType} {sig : signature}
    (E : fuzzy_theory R sig) (X : fuzzy_space R)
    (phi : @judgement R sig (fcarrier X)) :
  fuzzy_theory_nonneg E ->
  derives_full E phi <-> fuzzy_consequence E phi.
Proof.
  move => Hnonneg; split.
  - exact: derives_full_consequence.
  - exact: derives_full_complete.
Qed.

Set Silent.
Print Assumptions derives_full_complete.
Unset Silent.
