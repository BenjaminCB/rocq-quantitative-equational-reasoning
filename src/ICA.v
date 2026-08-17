From mathcomp Require Import ssreflect ssrfun ssrbool ssralg ssrnum reals fintype.
Import preorder.Order.PreorderTheory.

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
Qed.

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
