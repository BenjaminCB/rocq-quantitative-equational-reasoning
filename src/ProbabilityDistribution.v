From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import all_classical reals.
From mathcomp Require Import finmap.
From mathcomp Require Import interval_inference.
From mathcomp Require Import convex.
From mathcomp Require Export kantorovich.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope convex_scope.

(** [mathcomp.analysis.kantorovich] provides [fdist]/[dirac_fdist]/
    [joint_fdist]/[coupling]/[indep_fdist]/[indep_coupling]/[coupling_cost]/
    [kantorovich_lifting], plus [isConvexSpace] instances on [fdist R X] and
    [joint_fdist R X Y] pointwise on the underlying mass functions, and the
    lemmas [fdist_le1], [fdist_ext], [coupling_cost_ge0], [coupling_cost_le1],
    [coupling_cost_conv], [kantorovich_lifting_ge0], [kantorovich_lifting_le1],
    [kantorovich_le_coupling_cost], [kantorovich_almost_optimal],
    [kantorovich_conv_le], [kantorovich_dirac_le], [couplings_nonempty].  This
    file keeps only what has no upstream analogue. *)

(** [mathcomp.algebra.interval_inference]'s [{i01 R}] (real numbers
    canonically known to lie in [0, 1]) is a ready-made replacement for a
    hand-rolled unit-interval sigma type. *)
Definition probability_weight (R : realType) : Type := {i01 R}.

Definition weight {R : realType} (p : probability_weight R) : R := p%:num.

Lemma weight_unit {R : realType} (p : probability_weight R) :
  (0 <= weight p <= 1)%R.
Proof. by rewrite /weight; apply/andP; split; [exact: ge0 | exact: le1]. Qed.

Definition distribution_support {R : realType} {X : finType}
    (mu : fdist R X) : {set X} := [set x | mu x != 0].

(** The Kantorovich lifting is jointly convex on [fdist R X], via the
    [isConvexSpace] instance [kantorovich.v] equips it with; this names that
    convex combination the way the rest of this development already does. *)
Definition convex_mixture {R : realType} {X : finType}
    (p : probability_weight R) (mu nu : fdist R X) : fdist R X :=
  mu <| p |> nu.

(** The scalar convex combination underlying [conv] on [R^o]
    (`mathcomp/analysis/convex.v`'s [convRE]), named for readability at the
    many call sites that combine bare reals rather than [fdist]s. *)
Definition weighted_sum {R : realType}
    (p : probability_weight R) (x y : R) : R :=
  weight p * x + (1 - weight p) * y.

Lemma convex_mixtureE {R : realType} {X : finType}
    (p : probability_weight R) (mu nu : fdist R X) (x : X) :
  convex_mixture p mu nu x = weighted_sum p (mu x) (nu x).
Proof. by rewrite /convex_mixture fdist_convE convRE. Qed.

Lemma weighted_sumE {R : realType} (p : probability_weight R) (x y : R) :
  weighted_sum p x y = (x : R^o) <| p |> (y : R^o).
Proof. by rewrite convRE. Qed.

Lemma weighted_sum_ge0 {R : realType}
    (p : probability_weight R) (x y : R) :
  (0 <= x)%R -> (0 <= y)%R -> (0 <= weighted_sum p x y)%R.
Proof.
  move => Hx Hy.
  have /andP [Hp0 Hp1] := weight_unit p.
  rewrite /weighted_sum.
  apply: addr_ge0.
  - exact: mulr_ge0 Hp0 Hx.
  - apply: mulr_ge0; last exact Hy.
    by rewrite subr_ge0.
Qed.

Lemma sum_weighted_sum {R : realType} {X : finType}
    (p : probability_weight R) (f g : X -> R) :
  \sum_(x : X) weighted_sum p (f x) (g x) =
  weighted_sum p (\sum_(x : X) f x) (\sum_(x : X) g x).
Proof.
  by rewrite /weighted_sum big_split -!big_distrr.
Qed.

Lemma weighted_sum_one {R : realType} (p : probability_weight R) :
  weighted_sum p 1 1 = 1.
Proof.
  rewrite /weighted_sum.
  by rewrite -mulrDl addrC subrK mul1r.
Qed.

Lemma weighted_sum_le {R : realType} (p : probability_weight R)
    (a1 a2 b1 b2 : R) :
  (a1 <= a2)%R -> (b1 <= b2)%R ->
  (weighted_sum p a1 b1 <= weighted_sum p a2 b2)%R.
Proof.
  move => Ha Hb.
  rewrite /weighted_sum.
  have /andP [Hzero Hone] := weight_unit p.
  apply: lerD; apply: ler_wpM2l; by rewrite ?subr_ge0.
Qed.

Lemma weighted_sum_addr {R : realType} (p : probability_weight R)
    (a b e : R) :
  weighted_sum p (a + e) (b + e) = (weighted_sum p a b + e)%R.
Proof.
  rewrite /weighted_sum.
  rewrite !mulrDr.
  rewrite addrACA.
  rewrite -mulrDl.
  rewrite [weight p + (1 - weight p)]addrC subrK mul1r.
  reflexivity.
Qed.

(** [kantorovich_lifting_ge0] and [kantorovich_lifting_le1] packaged as one
    [andP], matching how this development already calls this fact. *)
Lemma fuzzy_kantorovich_lifting {R : realType} {X : finType}
    (d : X -> X -> R)
    (mu nu : fdist R X) :
  (forall x y, 0 <= d x y <= 1) -> 0 <= kantorovich_lifting d mu nu <= 1.
Proof.
  move=> Hd.
  have Hd0 : forall x y, 0 <= d x y by move=> x y; case/andP: (Hd x y).
  apply/andP; split.
  - exact: kantorovich_lifting_ge0.
  - exact: kantorovich_lifting_le1.
Qed.

(** Sum a real-valued function over an explicit finite support.  The type [A]
    is the finite subtype of elements belonging to the finite set [A]. *)
Definition fsum {R : realType} {X : choiceType}
    (A : {fset X}) (f : X -> R) : R :=
  \sum_(x : A) f (fsval x).

Lemma fsum_ext {R : realType} {X : choiceType}
    (A : {fset X}) (f g : X -> R) :
  (forall x, x \in A -> f x = g x) ->
  fsum A f = fsum A g.
Proof.
  move => H.
  apply: eq_bigr => x _.
  apply: H.
  apply: fsvalP.
Qed.

Lemma fsum_eq0 {R : realType} {X : choiceType}
    (A : {fset X}) (f : X -> R) :
  (forall x, x \in A -> f x = 0) ->
  fsum A f = 0.
Proof.
  move => H.
  apply: big1 => x _.
  apply: H.
  apply: fsvalP.
Qed.

Lemma fsum_support_widen {R : realType} {X : choiceType}
    (A B : {fset X}) (f : X -> R) :
  (A `<=` B)%fset ->
  (forall x, x \in B -> x \notin A -> f x = 0) ->
  fsum B f = fsum A f.
Proof.
  move => hAB h0.
  rewrite /fsum -(big_seq_fsetE _ B xpredT f) -(big_seq_fsetE _ A xpredT f).
  symmetry.
  apply: big_fset_incl.
  - exact: hAB.
  - exact: h0.
Qed.
