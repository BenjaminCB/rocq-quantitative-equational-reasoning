From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp Require Import all_classical reals.
From mathcomp Require Import finmap.

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

(** The expected [d]-cost of a coupling.  This is [V_d] from
    Definition 4.2 of the compactness paper. *)
Definition coupling_cost {R : realType} {X Y : finType}
    (d : X -> Y -> R)
    {mu : probability_distribution R X}
    {nu : probability_distribution R Y}
    (gamma : coupling mu nu) : R :=
  \sum_(x : X) \sum_(y : Y)
    coupling_distribution gamma x y * d x y.

(** Definition 4.2: the Kantorovich lifting of [d], obtained by taking
    the infimum of coupling costs. *)
Definition kantorovich_lifting {R : realType} {X : finType}
    (d : X -> X -> R)
    (mu nu : probability_distribution R X) : R :=
  inf [set r : R | exists gamma : coupling mu nu,
    r = coupling_cost d gamma].

Lemma fuzzy_kantorovich_lifting {R : realType} {X : finType}
    (d : X -> X -> R)
    (mu nu : probability_distribution R X) :
  (forall x y, 0 <= d x y <= 1) -> 0 <= kantorovich_lifting d mu nu <= 1.
Proof.
  move=> Hd.
  rewrite /kantorovich_lifting.
  set costs : set R := fun r => exists gamma : coupling mu nu,
    r = coupling_cost d gamma.
  have Hne : (costs !=set0)%classic.
  { exists (coupling_cost d (independent_coupling mu nu)).
    rewrite /costs.
    exists (independent_coupling mu nu).
    reflexivity. }
  have Hlb : lbound costs 0.
  { apply/lbP => r.
    rewrite /costs.
    move=> [gamma ->].
    rewrite /coupling_cost.
    apply: sumr_ge0 => x _.
    apply: sumr_ge0 => y _.
    have /andP [Hd0 _] := Hd x y.
    exact: mulr_ge0
      (joint_probability_mass_ge0 (coupling_distribution gamma) x y) Hd0. }
  apply/andP; split.
  - exact: lb_le_inf Hne Hlb.
  - set gamma := independent_coupling mu nu.
    have Hinf_cost : inf costs <= coupling_cost d gamma.
    { have Hhaslb : has_lbound costs by exists 0.
      have Hinf := ge_inf Hhaslb.
      apply: Hinf.
      rewrite /costs.
      exists gamma.
      reflexivity. }
    apply: (le_trans Hinf_cost).
    rewrite /coupling_cost.
    rewrite -(joint_probability_mass_total (coupling_distribution gamma)).
    apply: ler_sum => x _.
    apply: ler_sum => y _.
    have /andP [_ Hd1] := Hd x y.
    have Hmass0 :=
      joint_probability_mass_ge0 (coupling_distribution gamma) x y.
    have Hmul :
        coupling_distribution gamma x y * d x y <=
        coupling_distribution gamma x y * 1 :=
      ler_wpM2l Hmass0 Hd1.
    by rewrite mulr1 in Hmul.
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

(****************************************
Trying to extend to finitely supported distributiotns. 
*****************************************)

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
  have subAB : {subset A <= B} by apply/fsubsetP.
  case hAeq: (A == fset0).
  { have eqA : A = fset0 by apply/eqP.
    have eqmem : A =i fset0 by apply/fsetP.
    rewrite /fsum.
    have -> : \sum_(x : B) f (fsval x) = 0.
    { apply: big1 => x _.
      have hxB : fsval x \in B := fsvalP x.
      have hxA : fsval x \notin A.
      { by rewrite (eqmem (fsval x)) in_fset0. }
      exact (h0 (fsval x) hxB hxA). }
    apply/esym/big1 => x _.
    by move: (fsvalP x); rewrite (eqmem (fsval x)) in_fset0. }
  have hA : A != fset0 by rewrite hAeq.
  rewrite /fsum (bigID (fun x : B => fsval x \in A)) /=.
  have -> : \sum_(x : B | fsval x \notin A) f (fsval x) = 0.
  { apply: big1 => x hx.
    exact: h0 _ (fsvalP x) hx. }
  rewrite addr0.
  have [x0 hx0] : exists x, x \in A by apply/fset0Pn.
  pose h (x : A) : B := Sub (fsval x) (subAB _ (fsvalP x)).
  pose a0 : A := Sub x0 hx0.
  pose h' (x : B) : A := insubd a0 (fsval x).
  have hbij : {on [pred x : B | fsval x \in A], bijective h}.
  { exists h'.
    - move => x _.
      apply: val_inj => /=.
      exact (insubdK a0 (fsvalP x)).
    - move => x hx.
      apply: val_inj => /=.
      exact (insubdK a0 hx). }
  transitivity
    (\sum_(x : A | fsval (h x) \in A) f (fsval (h x))).
  - exact (reindex h hbij).
  - apply: eq_big.
    + move => x.
      by rewrite /h /= fsvalP.
    + move => x _.
      reflexivity.
Qed.

Lemma fsum_disjoint_union {R : realType} {X : choiceType}
    (A B : {fset X}) (f : X -> R) :
  [disjoint A & B]%fset ->
  fsum (A `|` B)%fset f = fsum A f + fsum B f.
Proof.
Admitted.

Lemma fsum_union {R : realType} {X : choiceType}
    (A B : {fset X}) (f : X -> R) :
  fsum (A `|` B)%fset f =
  fsum A f + fsum (B `\` A)%fset f.
Proof.
  have hU : (A `|` B)%fset = (A `|` (B `\` A))%fset.
  - apply/fsetP => x.
    rewrite !in_fsetE.
    by case: (x \in A).
  rewrite hU.
  apply: fsum_disjoint_union.
  apply/fdisjointP => x.
  rewrite !in_fsetE.
  by case: (x \in A).
Qed.
