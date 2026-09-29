From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import all_classical reals.

From Template Require Import ProbabilityDistribution.

From mathcomp Require Import all_analysis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope convex_scope.

(** Proposition 4.12 (existence of an exact optimal coupling), the one
    analytic ingredient the roadmap flagged as genuinely missing upstream:
    [kantorovich.v] only provides [kantorovich_almost_optimal] (couplings
    with cost within any [eta] of the infimum), not an exact minimizer.

    For [finType] carriers, a coupling of [mu : fdist R X] and
    [nu : fdist R Y] is (via [rv_of_joint]/[joint_of_rv] below) the same
    data as a point of a closed, bounded -- hence compact, by
    [bounded_closed_compact] -- subset of the finite-dimensional space
    ['rV[R]_(#|X * Y|)], and [coupling_cost] is a continuous (in fact
    linear) function of that point. [compact_EVT_min] then gives an exact
    minimizer, which is exactly Proposition 4.12. *)

Section RowVectorEncoding.
Context {R : realType} {X Y : finType}.

(** The bijection between a curried mass function [X -> Y -> R] and a row
    vector indexed by [X * Y]'s own enumeration, underlying the whole
    development below: a coupling of [mu] and [nu] is nonneg + sums-to-1 +
    two marginal conditions, all of which are conditions on finitely many
    coordinates of such a vector. *)
Definition pair_card : nat := #|{: X * Y}|.

Definition rv_of_joint (g : X -> Y -> R) : 'rV[R]_pair_card :=
  \row_i g (enum_val i).1 (enum_val i).2.

Definition joint_of_rv (v : 'rV[R]_pair_card) : X -> Y -> R :=
  fun x y => v ord0 (enum_rank (x, y)).

Lemma joint_of_rv_of_joint (g : X -> Y -> R) : joint_of_rv (rv_of_joint g) =2 g.
Proof. by move=> x y; rewrite /joint_of_rv /rv_of_joint mxE enum_rankK. Qed.

Lemma rv_of_joint_of_rv (v : 'rV[R]_pair_card) : rv_of_joint (joint_of_rv v) = v.
Proof.
by apply/rowP => i; rewrite mxE /joint_of_rv -surjective_pairing enum_valK.
Qed.

Lemma sum_prod_enum (f : X -> Y -> R) :
  \sum_(x : X) \sum_(y : Y) f x y =
  \sum_(i : 'I_pair_card) f (enum_val i).1 (enum_val i).2.
Proof.
rewrite pair_bigA.
rewrite (reindex_onto enum_val enum_rank (fun p (_ : true) => enum_rankK p)).
by apply: eq_bigl => i; rewrite enum_valK eqxx andbT.
Qed.

(** Continuity, in the coordinates of an ['rV[R]_n], of a single coordinate
    projection and of a finite sum of such projections. Both are proved by
    the standard bigop induction, since ['rV[R]_n]'s own [coord_continuous]
    (from [mathcomp.analysis.matrix_normedtype]) only covers a single
    coordinate and the [cvgD]-based algebra of continuity needs its scalar
    target typed as [R^o] (the canonical [normedModType] structure on [R]
    as a module over itself), not the bare [R] that [coord_continuous]
    itself is stated for. *)
Lemma coord_continuous_o (i : 'I_pair_card) :
  continuous (fun v : 'rV[R]_pair_card => v ord0 i : R^o).
Proof. exact: coord_continuous. Qed.

Lemma continuous_sum_enum {S : finType} (idx : S -> 'I_pair_card) :
  continuous (fun v : 'rV[R]_pair_card => \sum_(s : S) v ord0 (idx s) : R^o).
Proof.
move=> x.
have : forall r : seq S,
    (fun v : 'rV[R]_pair_card => \sum_(s <- r) v ord0 (idx s) : R^o) @ x -->
    (\sum_(s <- r) x ord0 (idx s) : R^o).
  elim=> [|s r IH].
  - have -> : (fun v : 'rV[R]_pair_card =>
        \sum_(s <- [::]) v ord0 (idx s) : R^o) = fun=> 0.
      by apply/funext=> v; rewrite big_nil.
    rewrite big_nil.
    apply: cvg_cst; exact: nbhs_filter.
  - have E : (fun w : 'rV[R]_pair_card =>
        \sum_(s0 <- s :: r) w ord0 (idx s0) : R^o) =
        (fun w => (w ord0 (idx s) : R^o) +
                  (\sum_(s0 <- r) w ord0 (idx s0) : R^o)).
      by apply/funext=> w; rewrite big_cons.
    rewrite E big_cons.
    apply: cvgD.
    + exact: nbhs_filter.
    + exact: coord_continuous.
    + exact: IH.
move=> /(_ (index_enum S)) H.
exact: H.
Qed.

(** The set of row vectors encoding a coupling of [mu] and [nu]: nonneg
    entries (folded together with the derived bound [<= 1] into interval
    membership, so that closedness -- via [itv_closed] -- and boundedness
    come for free from the same conjunct) plus the two marginal conditions,
    stated directly as sums over [Y] (resp. [X]) rather than as conditioned
    sums over ['I_pair_card], mirroring [coupling_fst]/[coupling_snd]. *)
Definition coupling_rv_set (mu : fdist R X) (nu : fdist R Y) :
    set 'rV[R]_pair_card :=
  [set v : 'rV[R]_pair_card |
     (forall i, v ord0 i \in `[0, 1]%R) /\
     (forall x, \sum_(y : Y) v ord0 (enum_rank (x, y)) = mu x) /\
     (forall y, \sum_(x : X) v ord0 (enum_rank (x, y)) = nu y)].

Lemma coupling_rv_set_nonempty (mu : fdist R X) (nu : fdist R Y) :
  coupling_rv_set mu nu (rv_of_joint (indep_fdist mu nu)).
Proof.
split; [ | split].
- move=> i; rewrite /rv_of_joint mxE in_itv/=; apply/andP; split.
  + apply: mulr_ge0; exact: fdist_ge0.
  + rewrite -[leRHS]mulr1.
    by apply: ler_pM; [exact: fdist_ge0 | exact: fdist_ge0
                       | exact: fdist_le1 | exact: fdist_le1].
- move=> x; under eq_bigr do rewrite /rv_of_joint mxE enum_rankK.
  by rewrite /= -big_distrr/= fdist_1 mulr1.
- move=> y; under eq_bigr do rewrite /rv_of_joint mxE enum_rankK.
  by rewrite /= -big_distrl/= fdist_1 mul1r.
Qed.

Lemma coupling_rv_set_closed (mu : fdist R X) (nu : fdist R Y) :
  closed (coupling_rv_set mu nu).
Proof.
rewrite /coupling_rv_set.
have -> : [set v : 'rV[R]_pair_card |
      (forall i, v ord0 i \in `[0, 1]%R) /\
      (forall x, \sum_(y : Y) v ord0 (enum_rank (x, y)) = mu x) /\
      (forall y, \sum_(x : X) v ord0 (enum_rank (x, y)) = nu y)] =
    [set v : 'rV[R]_pair_card | forall i, v ord0 i \in `[0, 1]%R] `&`
    ([set v : 'rV[R]_pair_card |
        forall x, \sum_(y : Y) v ord0 (enum_rank (x, y)) = mu x] `&`
     [set v : 'rV[R]_pair_card |
        forall y, \sum_(x : X) v ord0 (enum_rank (x, y)) = nu y]).
  by apply/seteqP; split=> v [] // ? [] //.
apply: closedI; [ | apply: closedI].
- have -> : [set v : 'rV[R]_pair_card | forall i, v ord0 i \in `[0, 1]%R] =
      \bigcap_(i in [set: 'I_pair_card])
        [set v : 'rV[R]_pair_card | v ord0 i \in `[0, 1]%R].
    rewrite eqEsubset; split=> v H.
    - by move=> i _; exact: H.
    - move=> i; exact: (H i).
  apply: closed_bigI => i _.
  have -> : [set v : 'rV[R]_pair_card | v ord0 i \in `[0, 1]%R] =
            (fun v : 'rV[R]_pair_card => v ord0 i) @^-1` [set` `[0, 1]%R].
    by [].
  apply: (continuous_closedP _).1;
    [move=> v; exact: coord_continuous | exact: itv_closed].
- have -> : [set v : 'rV[R]_pair_card |
        forall x, \sum_(y : Y) v ord0 (enum_rank (x, y)) = mu x] =
      \bigcap_(x in [set: X]) [set v : 'rV[R]_pair_card |
        \sum_(y : Y) v ord0 (enum_rank (x, y)) = mu x].
    rewrite eqEsubset; split=> v H.
    - by move=> x _; exact: H.
    - by move=> x; exact: (H x).
  apply: closed_bigI => x _.
  have -> : [set v : 'rV[R]_pair_card |
        \sum_(y : Y) v ord0 (enum_rank (x, y)) = mu x] =
      (fun v : 'rV[R]_pair_card =>
         \sum_(y : Y) v ord0 (enum_rank (x, y)) : R^o)
        @^-1` [set r : R^o | r = mu x].
    by [].
  apply: (continuous_closedP _).1;
    [move=> v; exact: continuous_sum_enum | exact: closed_eq].
- have -> : [set v : 'rV[R]_pair_card |
        forall y, \sum_(x : X) v ord0 (enum_rank (x, y)) = nu y] =
      \bigcap_(y in [set: Y]) [set v : 'rV[R]_pair_card |
        \sum_(x : X) v ord0 (enum_rank (x, y)) = nu y].
    rewrite eqEsubset; split=> v H.
    - by move=> y _; exact: H.
    - by move=> y; exact: (H y).
  apply: closed_bigI => y _.
  have -> : [set v : 'rV[R]_pair_card |
        \sum_(x : X) v ord0 (enum_rank (x, y)) = nu y] =
      (fun v : 'rV[R]_pair_card =>
         \sum_(x : X) v ord0 (enum_rank (x, y)) : R^o)
        @^-1` [set r : R^o | r = nu y].
    by [].
  apply: (continuous_closedP _).1;
    [move=> v; exact: continuous_sum_enum | exact: closed_eq].
Qed.

Lemma coupling_rv_set_bounded (mu : fdist R X) (nu : fdist R Y) :
  bounded_set (coupling_rv_set mu nu).
Proof.
rewrite /bounded_set/bounded_near/=.
near=> M => v [Hnn _].
rewrite /Num.Def.normr/=.
apply: (le_trans (y := 1)).
- rewrite mx_normrE; apply/bigmax_leP; split; first exact: ler01.
  move=> [i0 j] _ /=; rewrite (ord1 i0).
  have := Hnn j; rewrite in_itv/= => /andP [Hge Hle].
  by rewrite ger0_norm.
- near: M; exact: nbhs_pinfty_ge.
Unshelve. all: end_near.
Qed.

Lemma coupling_rv_set_compact (mu : fdist R X) (nu : fdist R Y) :
  compact (coupling_rv_set mu nu).
Proof.
refine (bounded_closed_compact _ _).
- exact: coupling_rv_set_bounded.
- exact: coupling_rv_set_closed.
Qed.

(** The expected [d]-cost, as a continuous function of the encoding row
    vector; the same construction as [coupling_cost] but usable directly as
    a target for [compact_EVT_min]. *)
Definition coupling_rv_cost (d : X -> Y -> R) (v : 'rV[R]_pair_card) : R^o :=
  \sum_(i : 'I_pair_card) v ord0 i * d (enum_val i).1 (enum_val i).2.

Lemma coupling_rv_cost_continuous (d : X -> Y -> R) :
  continuous (coupling_rv_cost d).
Proof.
rewrite /coupling_rv_cost => x.
have : forall r : seq 'I_pair_card,
    (fun v : 'rV[R]_pair_card =>
       \sum_(i <- r) v ord0 i * d (enum_val i).1 (enum_val i).2 : R^o) @ x -->
    (\sum_(i <- r) x ord0 i * d (enum_val i).1 (enum_val i).2 : R^o).
  elim=> [|i0 r IH].
  - have -> : (fun v : 'rV[R]_pair_card =>
        \sum_(i <- [::]) v ord0 i * d (enum_val i).1 (enum_val i).2 : R^o) =
        fun=> 0.
      by apply/funext=> v; rewrite big_nil.
    rewrite big_nil.
    apply: cvg_cst; exact: nbhs_filter.
  - have E : (fun w : 'rV[R]_pair_card =>
        \sum_(j <- i0 :: r) w ord0 j * d (enum_val j).1 (enum_val j).2 : R^o) =
        (fun w => (w ord0 i0 * d (enum_val i0).1 (enum_val i0).2 : R^o) +
                  (\sum_(j <- r) w ord0 j * d (enum_val j).1 (enum_val j).2 : R^o)).
      by apply/funext=> w; rewrite big_cons.
    rewrite E big_cons.
    apply: cvgD.
    + exact: nbhs_filter.
    + apply: cvgMr_tmp.
      * exact: nbhs_filter.
      * exact: coord_continuous.
    + exact: IH.
move=> /(_ (index_enum 'I_pair_card)) H.
exact: H.
Qed.

(** Proposition 4.12's analytic core: a minimizer of the cost over the
    (compact, nonempty) set of encodings of couplings of [mu] and [nu]. *)
Lemma coupling_rv_min (mu : fdist R X) (nu : fdist R Y) (d : X -> Y -> R) :
  exists2 v0, coupling_rv_set mu nu v0 &
    forall v, coupling_rv_set mu nu v ->
      coupling_rv_cost d v0 <= coupling_rv_cost d v.
Proof.
have A0 : coupling_rv_set mu nu !=set0.
  by exists (rv_of_joint (indep_fdist mu nu)); exact: coupling_rv_set_nonempty.
have Hcont : {within coupling_rv_set mu nu, continuous (coupling_rv_cost d)}.
  apply: continuous_in_subspaceT => v _.
  exact: coupling_rv_cost_continuous.
have [v0 Hv0 Hmin] := @compact_EVT_min 'rV[R]_pair_card R (coupling_rv_cost d)
  (coupling_rv_set mu nu) A0 (@coupling_rv_set_compact mu nu) Hcont.
by exists v0; [exact: set_mem Hv0 | move=> v Hv; apply: Hmin; apply: mem_set].
Qed.

(** Packaging an encoding vector satisfying [coupling_rv_set mu nu] back up
    as an actual [coupling mu nu]. *)
Section Packaging.
Context (mu : fdist R X) (nu : fdist R Y) (v : 'rV[R]_pair_card)
        (Hv : coupling_rv_set mu nu v).

Definition jfdist_of_rv : joint_fdist R X Y.
apply: (@JointFdist R X Y (joint_of_rv v) _ _).
- move=> x y; move: Hv => [Hnn _].
  by have := Hnn (enum_rank (x, y)); rewrite /joint_of_rv in_itv/= => /andP [].
- move: Hv => [_ [Hx _]].
  rewrite /joint_of_rv.
  have -> : \sum_(x : X) \sum_(y : Y) v ord0 (enum_rank (x, y)) =
            \sum_(x : X) mu x.
    by apply: eq_bigr => x _; exact: Hx.
  exact: fdist_1.
Defined.

Definition coupling_of_rv : coupling mu nu.
apply: (@Coupling R X Y mu nu jfdist_of_rv).
- move=> x; move: Hv => [_ [Hx _]]; exact: Hx.
- move=> y; move: Hv => [_ [_ Hy]]; exact: Hy.
Defined.

Lemma coupling_cost_of_rv (d : X -> Y -> R) :
  coupling_cost d coupling_of_rv = coupling_rv_cost d v.
Proof.
rewrite /coupling_cost /coupling_rv_cost /= sum_prod_enum.
by apply: eq_bigr => i _; rewrite /joint_of_rv -surjective_pairing enum_valK.
Qed.

End Packaging.

Lemma coupling_rv_set_of_coupling (mu : fdist R X) (nu : fdist R Y)
    (gamma : coupling mu nu) : coupling_rv_set mu nu (rv_of_joint gamma).
Proof.
split; [ | split].
- move=> i; rewrite /rv_of_joint mxE in_itv/=; apply/andP; split.
  + exact: joint_ge0.
  + apply: (le_trans _ (fdist_le1 mu (enum_val i).1)).
    rewrite -(coupling_fst gamma (enum_val i).1).
    rewrite (bigD1 (enum_val i).2) //= lerDl sumr_ge0 // => y _.
    exact: joint_ge0.
- move=> x.
  have -> : \sum_(y : Y) rv_of_joint gamma ord0 (enum_rank (x, y)) =
            \sum_(y : Y) gamma x y.
    by apply: eq_bigr => y _; rewrite /rv_of_joint mxE enum_rankK.
  exact: coupling_fst.
- move=> y.
  have -> : \sum_(x : X) rv_of_joint gamma ord0 (enum_rank (x, y)) =
            \sum_(x : X) gamma x y.
    by apply: eq_bigr => x _; rewrite /rv_of_joint mxE enum_rankK.
  exact: coupling_snd.
Qed.

Lemma coupling_rv_cost_of_joint (g d : X -> Y -> R) :
  coupling_rv_cost d (rv_of_joint g) = \sum_(x : X) \sum_(y : Y) g x y * d x y.
Proof.
rewrite /coupling_rv_cost sum_prod_enum.
by apply: eq_bigr => i _; rewrite /rv_of_joint mxE.
Qed.

End RowVectorEncoding.

(** Proposition 4.12: for [finType] carriers, [kantorovich_lifting]'s
    defining infimum is attained by an actual coupling, not merely
    approached (as [kantorovich_almost_optimal] alone gives). *)
Theorem kantorovich_optimal_coupling {R : realType} {X : finType}
    (mu nu : fdist R X) (d : X -> X -> R) :
  (forall x y, 0 <= d x y) ->
  exists gamma : coupling mu nu, coupling_cost d gamma = kantorovich_lifting d mu nu.
Proof.
move=> Hd.
have [v0 Hv0 Hmin] := coupling_rv_min (Y := X) mu nu d.
exists (coupling_of_rv Hv0).
apply: le_anti; apply/andP; split.
- rewrite (coupling_cost_of_rv Hv0 d).
  apply: lb_le_inf.
  + by exists (coupling_cost d (indep_coupling mu nu)), (indep_coupling mu nu).
  + apply/lbP => r [gamma ->].
    have -> : coupling_cost d gamma = coupling_rv_cost d (rv_of_joint gamma).
      by rewrite (coupling_rv_cost_of_joint gamma d).
    apply: Hmin; exact: coupling_rv_set_of_coupling.
- exact: kantorovich_le_coupling_cost.
Qed.
