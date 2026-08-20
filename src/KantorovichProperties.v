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

Lemma coupling_cost_le1 {R : realType} {X Y : finType}
    (d : X -> Y -> R)
    {mu : probability_distribution R X}
    {nu : probability_distribution R Y}
    (gamma : coupling mu nu) :
  (forall x y, (d x y <= 1)%R) ->
  (coupling_cost d gamma <= 1)%R.
Proof.
  move => Hd.
  rewrite /coupling_cost.
  apply: (@le_trans _ _ 
    (\sum_(x : X) \sum_(y : Y)
      coupling_distribution gamma x y * 1)).
  - apply: ler_sum => x _; apply: ler_sum => y _.
    apply: ler_wpM2l.
    - apply: (joint_probability_mass_ge0 (coupling_distribution gamma) x y).
    - apply: Hd.
  - under eq_bigr => x _ do under eq_bigr => y _
    do rewrite mulr1.
    rewrite joint_probability_mass_total.
    apply lexx.
Qed.

Lemma kantorovich_le_coupling_cost {R : realType} {X : finType}
    (d : X -> X -> R)
    (mu nu : probability_distribution R X)
    (gamma : coupling mu nu) :
  (forall x y, (0 <= d x y)%R) ->
  (kantorovich_lifting d mu nu <= coupling_cost d gamma)%R.
Proof.
  move=> Hd.
  rewrite /kantorovich_lifting.
  set costs : set R := fun r => exists g : coupling mu nu,
    r = coupling_cost d g.
  have Hlb : has_lbound costs.
  { exists 0; apply/lbP => r [g ->]; exact: coupling_cost_ge0 _ Hd. }
  apply: (ge_inf Hlb).
  by exists gamma.
Qed.

Lemma kantorovich_almost_optimal {R : realType} {X : finType}
    (d : X -> X -> R)
    (mu nu : probability_distribution R X)
    (eta : R) :
  (forall x y, (0 <= d x y)%R) ->
  (0 < eta)%R ->
  exists gamma : coupling mu nu,
    (coupling_cost d gamma <
    kantorovich_lifting d mu nu + eta)%R.
Proof.
  move=> Hd Heta.
  rewrite /kantorovich_lifting.
  set costs : set R := fun r => exists gamma : coupling mu nu,
    r = coupling_cost d gamma.
  have Hinf : has_inf costs.
  { split.
    - exists (coupling_cost d (independent_coupling mu nu)).
      by exists (independent_coupling mu nu).
    - exists 0; apply/lbP => r [g ->]; exact: coupling_cost_ge0 _ Hd. }
  have [r [gamma ->] Hr] := inf_adherent Heta Hinf.
  by exists gamma.
Qed.
