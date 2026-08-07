From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp Require Import all_classical reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Record probability_weight (R : realType) := {
  weight : R;
  weight_unit : (0 <= weight <= 1)%R;
}.

(** Definition 2.2.  The carrier is a [finType], so every distribution
    below is finitely supported automatically. *)
Record probability_distribution (R : realType) (X : finType) := {
  probability_mass :> X -> R;
  probability_mass_ge0 : forall x, (0 <= probability_mass x)%R;
  probability_mass_total : \sum_(x : X) probability_mass x = 1;
}.

Lemma probability_mass_le1 {R : realType} {X : finType}
    (mu : probability_distribution R X) (x : X) :
  (mu x <= 1)%R.
Proof.
  rewrite -(probability_mass_total mu) (bigD1 x) //=.
  rewrite lerDl.
  apply: sumr_ge0 => y _.
  exact: probability_mass_ge0.
Qed.

Lemma probability_distribution_ext {R : realType} {X : finType}
    (mu nu : probability_distribution R X) :
  (forall x, mu x = nu x) -> mu = nu.
Proof.
  case: mu => mu Hmu0 Hmu1.
  case: nu => nu Hnu0 Hnu1 /=.
  move=> H.
  have Hfun : mu = nu by apply functional_extensionality.
  subst nu.
  f_equal; apply proof_irrelevance.
Qed.

Definition distribution_support {R : realType} {X : finType}
    (mu : probability_distribution R X) : {set X} :=
  [set x | mu x != 0].

(** The Dirac distribution [delta_x]. *)
Definition dirac {R : realType} {X : finType} (x : X) :
    probability_distribution R X.
Proof.
  refine {| probability_mass := fun y => if y == x then 1 else 0 |}.
  - move => y.
    case: ifP => _; [exact: ler01 | exact: lexx].
  - rewrite (bigD1 x) //= eqxx.
    rewrite big1 ?addr0 //.
    move => y Hy.
    by rewrite (negbTE Hy).
Defined.

(** A distribution on a finite product, represented in curried form.
    The curried representation exposes the two marginal sums directly. *)
Record joint_probability_distribution
    (R : realType) (X Y : finType) := {
  joint_probability_mass :> X -> Y -> R;
  joint_probability_mass_ge0 :
    forall x y, (0 <= joint_probability_mass x y)%R;
  joint_probability_mass_total :
    \sum_(x : X) \sum_(y : Y) joint_probability_mass x y = 1;
}.

(** A coupling is a joint distribution whose first
    and second marginals are the specified distributions. *)
Record coupling {R : realType} {X Y : finType}
    (mu : probability_distribution R X)
    (nu : probability_distribution R Y) := {
  coupling_distribution : joint_probability_distribution R X Y;
  coupling_fst : forall x,
    \sum_(y : Y) coupling_distribution x y = mu x;
  coupling_snd : forall y,
    \sum_(x : X) coupling_distribution x y = nu y;
}.

(** The independent product distribution, with mass [mu x * nu y]. *)
Definition independent_product {R : realType} {X Y : finType}
    (mu : probability_distribution R X)
    (nu : probability_distribution R Y) :
    joint_probability_distribution R X Y.
Proof.
  refine {| joint_probability_mass := fun x y => mu x * nu y |}.
  - move=> x y.
    exact: mulr_ge0 (probability_mass_ge0 mu x)
                    (probability_mass_ge0 nu y).
  - under eq_bigr do
      rewrite -big_distrr probability_mass_total //=.
    have Hsum : (\sum_(x : X) mu x * 1) = \sum_(x : X) mu x.
    { apply: eq_bigr => x _.
      exact: mulr1. }
    by rewrite Hsum probability_mass_total.
Defined.

Definition independent_coupling {R : realType} {X Y : finType}
    (mu : probability_distribution R X)
    (nu : probability_distribution R Y) : coupling mu nu.
Proof.
  refine {| coupling_distribution := independent_product mu nu |}.
  - move=> x /=.
    rewrite -big_distrr probability_mass_total //=.
    exact: mulr1.
  - move=> y /=.
    rewrite -big_distrl probability_mass_total //=.
    exact: mul1r.
Defined.

(** non-emptiness part: the independent product is always
    a coupling.  Compactness is a topological result and belongs in a later
    finite-dimensional topology layer. *)
Lemma couplings_nonempty {R : realType} {X Y : finType}
    (mu : probability_distribution R X)
    (nu : probability_distribution R Y) :
  inhabited (coupling mu nu).
Proof.
  exact: inhabits (independent_coupling mu nu).
Qed.

Definition weighted_sum {R : realType}
    (p : probability_weight R) (x y : R) : R :=
  weight p * x + (1 - weight p) * y.

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

(** Definition 2.2's pointwise convex-algebra operation on distributions. *)
Definition convex_mixture {R : realType} {X : finType}
    (p : probability_weight R)
    (mu nu : probability_distribution R X) :
    probability_distribution R X.
Proof.
  refine {| probability_mass := fun x => weighted_sum p (mu x) (nu x) |}.
  - move=> x.
    exact: weighted_sum_ge0
      (probability_mass_ge0 mu x) (probability_mass_ge0 nu x).
  - by rewrite sum_weighted_sum
      !probability_mass_total weighted_sum_one.
Defined.

Definition joint_convex_mixture {R : realType} {X Y : finType}
    (p : probability_weight R)
    (gamma delta : joint_probability_distribution R X Y) :
    joint_probability_distribution R X Y.
Proof.
  refine {| joint_probability_mass :=
    fun x y => weighted_sum p (gamma x y) (delta x y) |}.
  - move=> x y.
    exact: weighted_sum_ge0
      (joint_probability_mass_ge0 gamma x y)
      (joint_probability_mass_ge0 delta x y).
  - under eq_bigr do rewrite sum_weighted_sum.
    by rewrite sum_weighted_sum
      !joint_probability_mass_total weighted_sum_one.
Defined.

(** Lemma 2.5: convex combinations preserve both marginals. *)
Lemma coupling_convex_mixture {R : realType} {X Y : finType}
    (p : probability_weight R)
    (mu1 mu2 : probability_distribution R X)
    (nu1 nu2 : probability_distribution R Y)
    (gamma1 : coupling mu1 nu1)
    (gamma2 : coupling mu2 nu2) :
  coupling (convex_mixture p mu1 mu2)
           (convex_mixture p nu1 nu2).
Proof.
  refine {| coupling_distribution :=
    joint_convex_mixture p (coupling_distribution gamma1)
                            (coupling_distribution gamma2) |}.
  - move=> x //=.
    by rewrite sum_weighted_sum
        (coupling_fst gamma1) (coupling_fst gamma2).
  - move=> y //=.
    by rewrite sum_weighted_sum
        (coupling_snd gamma1) (coupling_snd gamma2).
Defined.