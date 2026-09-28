From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import all_classical reals.

From Template Require Import ProbabilityDistribution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope convex_scope.

(** [coupling_cost_ge0], [coupling_cost_le1], [kantorovich_le_coupling_cost],
    [kantorovich_almost_optimal] and [kantorovich_dirac_le] are now provided
    directly by [mathcomp.analysis.kantorovich] (re-exported via
    [ProbabilityDistribution.v]).  What's left here is restating
    [coupling_cost_conv]/[kantorovich_conv_le] in terms of this
    development's [weighted_sum]/[convex_mixture] names instead of the
    [<| p |>] convex-space notation they're stated with upstream. *)

Lemma coupling_cost_convex_mixture {R : realType} {X Y : finType}
    (d : X -> Y -> R)
    {mu1 mu2 : fdist R X}
    {nu1 nu2 : fdist R Y}
    (p : probability_weight R)
    (gamma1 : coupling mu1 nu1)
    (gamma2 : coupling mu2 nu2) :
  coupling_cost d (coupling_conv p gamma1 gamma2) =
  weighted_sum p (coupling_cost d gamma1) (coupling_cost d gamma2).
Proof. by rewrite weighted_sumE coupling_cost_conv. Qed.

Lemma kantorovich_convex_mixture {R : realType} {X : finType}
    (d : X -> X -> R)
    (p : probability_weight R)
    (mu1 mu2 nu1 nu2 : fdist R X) :
  (forall x y, (0 <= d x y <= 1)%R) ->
  (kantorovich_lifting d
      (convex_mixture p mu1 mu2)
      (convex_mixture p nu1 nu2) <=
  weighted_sum p
    (kantorovich_lifting d mu1 nu1)
    (kantorovich_lifting d mu2 nu2))%R.
Proof. move=> Hd; rewrite !weighted_sumE; exact: kantorovich_conv_le. Qed.
