From mathcomp Require Import ssreflect ssrfun ssrbool ssralg ssrnum reals fintype.
Import preorder.Order.PreorderTheory Num.Theory GRing.Theory.

From Template Require Import Signature FuzzyRelation FRelDeduction.
From Template Require Import ProbabilityDistribution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Record ica_weight (R : realType) := {
  ica_weight_val : R;
  ica_weight_open : (0 < ica_weight_val < 1)%R;
}.

Definition ica_probability_weight {R : realType}
    (p : ica_weight R) : probability_weight R.
Proof.
  refine {| weight := ica_weight_val p |}.
  have /andP [Hp0 Hp1] := ica_weight_open p.
  apply/andP; split.
  - apply: ltW Hp0.
  - apply: ltW Hp1.
Defined.

Inductive ica_sym (R : realType) : Type :=
  | ica_plus : ica_weight R -> ica_sym R.

Definition ica_arity {R : realType} (_ : ica_sym R) : nat := 2.

Definition ica_signature {R : realType} : signature :=
  {| sym := ica_sym R; arity := ica_arity |}.


Definition ica_op {R : realType} {X : Type} (p : ica_weight R)
    (x y : term ica_signature X) : term ica_signature X :=
  @App ica_signature X (ica_plus p)
    (fun i => if (Nat.eqb (i : nat) 0) then x else y).

Notation "x <+ p +> y" := (ica_op p x y)
  (at level 40, p at next level, left associativity).

Definition ica_weight_complement {R : realType} 
  (p : ica_weight R) : ica_weight R.
Proof.
  refine {| ica_weight_val := 1 - ica_weight_val p |}.
  have /andP [Hp0 Hp1] := ica_weight_open p.
  apply/andP; split.
    - rewrite subr_gt0; apply Hp1.
    - rewrite gtrBl; apply Hp0.
Defined. 

Definition ica_weight_product {R : realType}
  (p q : ica_weight R) : ica_weight R.
Proof.
  refine {| ica_weight_val := ica_weight_val p * ica_weight_val q |}.
  have /andP [Hp0 Hp1] := ica_weight_open p.
  have /andP [Hq0 Hq1] := ica_weight_open q.
  apply/andP; split.
  - by apply mulr_gt0. 
  - move: (ltW Hp0) => {}Hp0.
    move: (ltW Hq0) => {}Hq0.
    by apply mulr_ilt1.
Defined. 

Definition ica_weight_assoc_inner {R : realType}
  (p q : ica_weight R) : ica_weight R.
Proof.
  refine {| 
    ica_weight_val := 
      ((1 - ica_weight_val p) * ica_weight_val q) / 
      (1 - ica_weight_val p * ica_weight_val q) 
  |}.
  have /andP [Hpq_C0 Hpq_C1] := 
    ica_weight_open (ica_weight_complement (ica_weight_product p q)).
  rewrite /ica_weight_product /= in Hpq_C0 Hpq_C1.
  have /andP [HCpq0 HCpq1] := 
    ica_weight_open (ica_weight_product (ica_weight_complement p) q).
  rewrite /ica_weight_product /= in HCpq0 HCpq1.
  apply/andP; split.
  - by apply divr_gt0.
  - rewrite (ltr_pdivrMr _ _ Hpq_C0) mul1r.
    rewrite mulrBl mul1r.
    rewrite ltrBlDr subrK.
    have /andP [_ Hq1] := ica_weight_open q.
    apply: Hq1.
Qed.
