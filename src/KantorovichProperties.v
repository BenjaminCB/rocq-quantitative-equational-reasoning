From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp Require Import all_classical reals.

From Template Require Import ProbabilityDistribution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Lemma coupling_cost_ge0 {R : realType} {X Y : finType}
    (d : X -> Y -> R)
    {mu : probability_distribution R X}
    {nu : probability_distribution R Y}
    (gamma : coupling mu nu) :
  (forall x y, (0 <= d x y)%R) ->
  (0 <= coupling_cost d gamma)%R.
Proof.
  move=> Hd.
  rewrite /coupling_cost.
  apply: sumr_ge0 => x _.
  apply: sumr_ge0 => y _.
  exact: mulr_ge0
    (joint_probability_mass_ge0 (coupling_distribution gamma) x y) (Hd x y).
Qed.
