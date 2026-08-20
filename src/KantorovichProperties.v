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

(* Could maybe be written a little easier 
   With some of the lemmas in ProbabilityDistributions.v *)
Lemma coupling_cost_convex_mixture {R : realType} {X Y : finType}
    (d : X -> Y -> R)
    {mu1 mu2 : probability_distribution R X}
    {nu1 nu2 : probability_distribution R Y}
    (p : probability_weight R)
    (gamma1 : coupling mu1 nu1)
    (gamma2 : coupling mu2 nu2) :
  coupling_cost d (coupling_convex_mixture p gamma1 gamma2) =
  weighted_sum p (coupling_cost d gamma1) (coupling_cost d gamma2).
Proof.
  rewrite /weighted_sum /coupling_cost.
  rewrite !big_distrr -big_split /=.
  apply: eq_bigr => x _.
  rewrite !big_distrr -big_split /=.
  apply: eq_bigr => y _.
  rewrite /weighted_sum.
  by rewrite mulrDl !mulrA.
Qed. 

Lemma kantorovich_convex_mixture {R : realType} {X : finType}
    (d : X -> X -> R)
    (p : probability_weight R)
    (mu1 mu2 nu1 nu2 : probability_distribution R X) :
  (forall x y, (0 <= d x y <= 1)%R) ->
  (kantorovich_lifting d
      (convex_mixture p mu1 mu2)
      (convex_mixture p nu1 nu2) <=
  weighted_sum p
    (kantorovich_lifting d mu1 nu1)
    (kantorovich_lifting d mu2 nu2))%R.
Proof.
  move => Hd.
  apply /ler_addgt0Pr => eta Heta.
  have Hd0 : forall x y, (0 <= d x y)%R. {
    move => x y.
    have /andP [H _] := Hd x y.
    apply H.
  }
  have [gamma1 Hg1] := kantorovich_almost_optimal mu1 nu1 Hd0 Heta.
  have [gamma2 Hg2] := kantorovich_almost_optimal mu2 nu2 Hd0 Heta.
  apply: (le_trans
    (kantorovich_le_coupling_cost (coupling_convex_mixture p gamma1 gamma2) Hd0)).
  rewrite coupling_cost_convex_mixture -weighted_sum_addr.
  by apply: weighted_sum_le; apply: ltW.
Qed.

Lemma kantorovich_dirac_le {R : realType} {X : finType}
    (d : X -> X -> R) (x y : X) :
  (forall u v, (0 <= d u v <= 1)%R) ->
  (kantorovich_lifting d (dirac x) (dirac y) <= d x y)%R.
Proof.
  move => Hunit.
  have Hd0 : forall u v, (0 <= d u v)%R. {
    move => u v.
    have /andP [H _] := Hunit u v.
    apply H.
  }
  apply: (le_trans
    (kantorovich_le_coupling_cost (independent_coupling (dirac x) (dirac y)) Hd0)).
  rewrite /coupling_cost /=.
  have key : forall (F : X -> R) (u0 : X),
      \sum_(u : X) (if u == u0 then 1 else 0) * F u = F u0. { 
    move=> F u0.
    rewrite (bigD1 u0) //=.
    rewrite eqxx mul1r.
    rewrite big1 ?addr0 // => u Hu.
    by rewrite (negbTE Hu) mul0r. 
  }
  under eq_bigr => u _ do
    (under eq_bigr => v _ do rewrite -mulrA;
     rewrite -big_distrr /= key).
  by rewrite key.
Qed.