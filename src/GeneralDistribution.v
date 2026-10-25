(* ============================================================
   [D(A)]: finitely-supported distributions over an arbitrary
   [choiceType] carrier, and the well-definedness of the Kantorovich
   lifting on them independently of which finite ambient witness set
   computes it (docs/formalization-status.md, M1b).
   ============================================================ *)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import all_classical reals.
From mathcomp Require Import finmap.
From mathcomp Require Import interval_inference.
From mathcomp Require Import convex.
From mathcomp Require Export kantorovich.
From Template Require Import ProbabilityDistribution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope convex_scope.
Local Open Scope fset_scope.

(** If [a] is bounded above by every [delta] strictly greater than
    [eps], then [a <= eps].  (Duplicated from [FRelDeduction.v] to
    keep this file's dependencies to the distribution layer only.) *)
Lemma le_of_all_strict_upper_bounds
    {R : realType} (a eps : R) :
  (forall delta, (eps < delta)%R -> (a <= delta)%R) ->
  (a <= eps)%R.
Proof.
  move => H.
  apply /Num.Theory.ler_addgt0Pr => e He.
  apply: H.
  by rewrite Num.Theory.ltrDl.
Qed.

(* ============================================================
   Part 0: [gdist R A], finitely supported mass functions over an
   arbitrary [choiceType] [A] that are nonnegative and sum to [1] on
   their own (finite) support -- the arbitrary-carrier analogue of
   [fdist R X].
   ============================================================ *)

Section GDist.
Context {R : realType} {A : choiceType}.

Record gdist := GDist {
  gd_fun :> {fsfun A -> R with 0};
  gd_ge0 : forall x, 0 <= gd_fun x;
  gd_sum1 : fsum (finsupp gd_fun) gd_fun = 1;
}.

Lemma gdist_ext (mu nu : gdist) : (forall x, mu x = nu x) -> mu = nu.
Proof.
case: mu nu => [mu mu0 mu1] [nu nu0 nu1] /= muE.
have {}muE : mu = nu by apply/fsfunP.
subst nu; congr GDist; exact: Prop_irrelevance.
Qed.

(** Every [gdist] has nonempty support: an empty support would force
    its own sum to be [0], contradicting [gd_sum1]. *)
Lemma gdist_supp_neq0 (mu : gdist) : finsupp mu != fset0.
Proof.
apply/negP => /eqP Hempty.
have H0 : fsum (finsupp mu) mu = 0.
  rewrite Hempty; apply: fsum_eq0 => x; by rewrite in_fset0.
have H1 := gd_sum1 mu.
rewrite H0 in H1.
by move: (@oner_neq0 R); rewrite -H1 eqxx.
Qed.

Definition gdirac_fsfun (x : A) : {fsfun A -> R with 0} :=
  [fsfun a in [fset x] => 1 | 0].

Lemma gdirac_fsfunE (x a : A) : gdirac_fsfun x a = if a == x then 1 else 0.
Proof. rewrite /gdirac_fsfun fsfunE inE. by case: eqP. Qed.

Lemma finsupp_gdirac (x : A) : finsupp (gdirac_fsfun x) = [fset x].
Proof.
apply/fsetP => a; rewrite mem_finsupp gdirac_fsfunE inE.
by case: ifP; rewrite ?oner_neq0 ?eqxx.
Qed.

Definition gdirac (x : A) : gdist.
refine (@GDist (gdirac_fsfun x) _ _).
- move => a; rewrite gdirac_fsfunE; by case: ifP; rewrite ?ler01 ?lexx.
- rewrite /fsum finsupp_gdirac (big_fset1 +%R).
  by rewrite gdirac_fsfunE eqxx.
Defined.

(** Restricting [mu] to any finite [B] containing its support gives a
    genuine [fdist] over the finType coercion of [B]. *)
Definition gdist_restrict (B : {fset A}) (mu : gdist)
    (H : (finsupp mu `<=` B)%fset) : fdist R B.
refine (@Fdist R B (fun x : B => mu (fsval x)) _ _).
- move => x; exact: gd_ge0.
- rewrite -/(fsum B mu) (fsum_support_widen H) //.
  + move => x _ Hx; exact: fsfun_dflt Hx.
  + exact: (gd_sum1 mu).
Defined.

Lemma gdist_restrictE (B : {fset A}) (mu : gdist)
    (H : (finsupp mu `<=` B)%fset) (x : B) :
  gdist_restrict H x = mu (fsval x).
Proof. by []. Qed.

End GDist.
Arguments gdist R A : clear implicits.
Arguments gdirac {R A} x.
Arguments gdist_restrict {R A} B mu H.

(* ============================================================
   Part 1: transporting [fdist]/[coupling]/[kantorovich_lifting]
   along an injective map between finTypes.  This is generic
   finType infrastructure with no dependence on [choiceType]
   carriers; it is what lets the Kantorovich lifting computed on one
   finite ambient witness set agree with the lifting computed on
   any larger one.
   ============================================================ *)

Section Push.
Context {R : realType} {Y X : finType}.

(** The pushforward ("image measure") of [mu] along [f]. *)
Definition push_fdist (f : Y -> X) (mu : fdist R Y) : fdist R X.
refine {| fdist_val := fun x => \sum_(y : Y | f y == x) mu y;
          fdist_ge0 := _; fdist_1 := _ |}.
- move => x; apply: sumr_ge0 => y _; exact: fdist_ge0.
- by rewrite -(fdist_1 mu) (partition_big f xpredT).
Defined.

Lemma push_fdistE (f : Y -> X) (mu : fdist R Y) (x : X) :
  push_fdist f mu x = \sum_(y : Y | f y == x) mu y.
Proof. by []. Qed.

End Push.
Arguments push_fdist {R Y X} f mu.

Lemma push_fdist_comp {R : realType} {Z Y X : finType}
    (g : Y -> X) (h : Z -> Y) (mu : fdist R Z) :
  push_fdist g (push_fdist h mu) = push_fdist (g \o h) mu.
Proof.
apply: fdist_ext => x.
rewrite push_fdistE.
under eq_bigr => y _ do rewrite push_fdistE.
symmetry; rewrite push_fdistE.
rewrite (partition_big h (fun y => g y == x) (fun i Hi => Hi)).
apply: eq_bigr => y Hy.
apply: eq_bigl => z.
rewrite andb_idl //.
move => /eqP ->; exact: Hy.
Qed.

Lemma push_fdist_injE {R : realType} {Y X : finType} (f : Y -> X)
    (Hf : injective f) (mu : fdist R Y) (y : Y) :
  push_fdist f mu (f y) = mu y.
Proof.
rewrite push_fdistE (bigD1 y) //= big_pred0 ?addr0 //.
move => y1; apply/negbTE; apply/negP => /andP [/eqP Hy1 Hne].
by move/eqP: Hne; apply; apply: Hf.
Qed.

Lemma push_fdist_support {R : realType} {Y X : finType} (f : Y -> X)
    (mu : fdist R Y) (x : X) :
  push_fdist f mu x != 0 -> exists y, f y = x.
Proof.
rewrite push_fdistE => H.
have [y Hy] : exists y, f y == x.
  apply/existsP; move: H; apply: contraNT => /existsPn Hn.
  apply/eqP/big_pred0 => y; exact/negbTE/Hn.
exists y; exact/eqP.
Qed.

(** A sum over the whole codomain of [f] equals the corresponding sum
    over the domain, provided the summand vanishes off [f]'s image
    and [f] is injective -- the sum-level counterpart of
    [push_fdist]/[push_fdistE]. *)
Lemma sum_inj_vanish {R : realType} {Y X : finType} (f : Y -> X)
    (Hf : injective f) (G : X -> R)
    (Hvanish : forall x, (forall y, f y != x) -> G x = 0) :
  \sum_(x : X) G x = \sum_(y : Y) G (f y).
Proof.
rewrite (partition_big f xpredT (fun i _ => erefl _)) /=.
apply: eq_bigr => x _.
case: (boolP [exists y, f y == x]) => Hcase.
- move: Hcase => /existsP [y0 Hy0].
  rewrite (bigD1 y0) //= big_pred0 ?addr0.
  + move => y1; apply/negbTE; apply/negP => /andP [Hy1 /eqP Hne].
    apply: Hne; apply: Hf; by rewrite (eqP Hy1) (eqP Hy0).
  + by rewrite (eqP Hy0).
- rewrite big_pred0.
  + move => y; apply/negbTE; apply/negP => Hy.
    move/negP: Hcase; apply; apply/existsP; exists y; exact: Hy.
  + apply: Hvanish => y; apply/negP => /eqP Hfy.
    move/negP: Hcase; apply; apply/existsP; exists y; by rewrite Hfy.
Qed.

Section CouplingTransport.
Context {R : realType} {X Y : finType}.

(** The [(X*Y)]-fdist underlying a coupling, and its two marginals
    recovered via [push_fdist]. *)
Definition fdist_of_coupling {mu : fdist R X} {nu : fdist R Y}
    (gamma : coupling mu nu) : fdist R (X * Y)%type.
refine {| fdist_val := fun p => gamma p.1 p.2;
          fdist_ge0 := _; fdist_1 := _ |}.
- move => p; exact: joint_ge0.
- by rewrite -pair_bigA; exact: joint_1.
Defined.

Lemma fdist_of_couplingE {mu : fdist R X} {nu : fdist R Y}
    (gamma : coupling mu nu) (x : X) (y : Y) :
  fdist_of_coupling gamma (x, y) = gamma x y.
Proof. by []. Qed.

Lemma push_fdist_fst_of_coupling {mu : fdist R X} {nu : fdist R Y}
    (gamma : coupling mu nu) :
  push_fdist fst (fdist_of_coupling gamma) = mu.
Proof.
apply: fdist_ext => x.
rewrite push_fdistE.
have Hk : forall p : X * Y, p.1 == x -> (x, p.2) = p.
  move => [x' y'] /= /eqP ->; reflexivity.
rewrite (reindex_onto (fun y : Y => (x, y)) snd Hk) /=.
rewrite -(coupling_fst gamma x).
apply: eq_bigl => y; by rewrite !eqxx.
Qed.

Lemma push_fdist_snd_of_coupling {mu : fdist R X} {nu : fdist R Y}
    (gamma : coupling mu nu) :
  push_fdist snd (fdist_of_coupling gamma) = nu.
Proof.
apply: fdist_ext => y.
rewrite push_fdistE.
have Hk : forall p : X * Y, p.2 == y -> (p.1, y) = p.
  move => [x' y'] /= /eqP ->; reflexivity.
rewrite (reindex_onto (fun x : X => (x, y)) fst Hk) /=.
rewrite -(coupling_snd gamma y).
apply: eq_bigl => x; by rewrite !eqxx.
Qed.

(** Conversely, any [(X*Y)]-fdist with the right marginals is (the
    fdist underlying) a coupling.  The pieces are proved as standalone
    lemmas, rather than via [have] inside a single tactic-mode proof,
    so that [coupling_of_fdist] stays a transparent, directly
    reducible term application (a bare [have] would elaborate into an
    opaque-looking wrapper that blocks [simpl]/[reflexivity] later). *)
Lemma joint_of_fdist_ge0 (eta : fdist R (X * Y)%type) (x : X) (y : Y) :
  0 <= eta (x, y).
Proof. exact: fdist_ge0. Qed.

Lemma joint_of_fdist_sum1 (eta : fdist R (X * Y)%type) :
  \sum_(x : X) \sum_(y : Y) eta (x, y) = 1.
Proof.
rewrite pair_bigA.
under eq_bigr => p _ do rewrite -surjective_pairing.
exact: fdist_1.
Qed.

Definition joint_of_fdist (eta : fdist R (X * Y)%type) : joint_fdist R X Y :=
  @JointFdist R X Y (fun x y => eta (x, y))
    (joint_of_fdist_ge0 eta) (joint_of_fdist_sum1 eta).

Lemma joint_of_fdist_fst {mu : fdist R X} (eta : fdist R (X * Y)%type)
    (Hfst : push_fdist fst eta = mu) (x : X) :
  \sum_(y : Y) joint_of_fdist eta x y = mu x.
Proof.
rewrite -Hfst push_fdistE.
rewrite (reindex_onto (fun y : Y => (x, y)) snd) /=.
- by move => [x' y'] /= /eqP ->.
- apply: eq_bigl => y; by rewrite !eqxx.
Qed.

Lemma joint_of_fdist_snd {nu : fdist R Y} (eta : fdist R (X * Y)%type)
    (Hsnd : push_fdist snd eta = nu) (y : Y) :
  \sum_(x : X) joint_of_fdist eta x y = nu y.
Proof.
rewrite -Hsnd push_fdistE.
rewrite (reindex_onto (fun x : X => (x, y)) fst) /=.
- by move => [x' y'] /= /eqP ->.
- apply: eq_bigl => x; by rewrite !eqxx.
Qed.

Definition coupling_of_fdist {mu : fdist R X} {nu : fdist R Y}
    (eta : fdist R (X * Y)%type)
    (Hfst : push_fdist fst eta = mu) (Hsnd : push_fdist snd eta = nu) :
    coupling mu nu :=
  @Coupling R X Y mu nu (joint_of_fdist eta)
    (joint_of_fdist_fst (eta := eta) Hfst) (joint_of_fdist_snd (eta := eta) Hsnd).

Lemma fdist_of_coupling_of_fdist {mu : fdist R X} {nu : fdist R Y}
    (eta : fdist R (X * Y)%type)
    (Hfst : push_fdist fst eta = mu) (Hsnd : push_fdist snd eta = nu) :
  fdist_of_coupling (coupling_of_fdist (eta := eta) Hfst Hsnd) = eta.
Proof.
apply: fdist_ext => p.
rewrite [p]surjective_pairing fdist_of_couplingE.
reflexivity.
Qed.

(** Any coupling's mass at [(x,y)] is confined to the product of the
    marginals' supports: the "coupling support" fact the M1
    correction note in [BarycentricNormalization.v] identifies as
    the one genuinely new semantic ingredient this construction
    needs. *)
Lemma coupling_support {mu : fdist R X} {nu : fdist R Y}
    (gamma : coupling mu nu) (x : X) (y : Y) :
  gamma x y != 0 -> mu x != 0.
Proof.
move => Hxy; rewrite -(coupling_fst gamma x).
apply: contraNN Hxy => /eqP /psumr_eq0P H.
apply/eqP; apply: H => //.
move => y0 _; exact: joint_ge0.
Qed.

Lemma coupling_support2 {mu : fdist R X} {nu : fdist R Y}
    (gamma : coupling mu nu) (x : X) (y : Y) :
  gamma x y != 0 -> nu y != 0.
Proof.
move => Hxy; rewrite -(coupling_snd gamma y).
apply: contraNN Hxy => /eqP /psumr_eq0P H.
apply/eqP; apply: H => //.
move => x0 _; exact: joint_ge0.
Qed.

End CouplingTransport.

Definition pcost {R : realType} {X Y : finType}
    (d : X -> Y -> R) (eta : fdist R (X * Y)%type) : R :=
  \sum_(p : X * Y) eta p * d p.1 p.2.

Lemma coupling_cost_pcost {R : realType} {X Y : finType} (d : X -> Y -> R)
    {mu : fdist R X} {nu : fdist R Y} (gamma : coupling mu nu) :
  coupling_cost d gamma = pcost d (fdist_of_coupling gamma).
Proof. by rewrite /coupling_cost /pcost pair_bigA. Qed.

Lemma pcost_push {R : realType} {Y X : finType} (f : Y -> X)
    (d : X -> X -> R) (d0 : Y -> Y -> R)
    (Hd : forall y1 y2, d (f y1) (f y2) = d0 y1 y2) (eta : fdist R (Y * Y)%type) :
  pcost d (push_fdist (fun p => (f p.1, f p.2)) eta) = pcost d0 eta.
Proof.
rewrite /pcost.
symmetry.
under eq_bigr => q _ do rewrite -(Hd q.1 q.2) -[d _ _]/(d (f q.1, f q.2).1 (f q.1, f q.2).2).
rewrite (partition_big (fun p : Y * Y => (f p.1, f p.2)) xpredT (fun i _ => erefl _)).
apply: eq_bigr => p _.
rewrite push_fdistE big_distrl /=.
apply: eq_bigr => q Hq.
by move: Hq => /eqP <-.
Qed.

Section Pullback.
Context {R : realType} {Y X : finType} (f : Y -> X) (Hf : injective f).

Lemma pullback_row (mu nu : fdist R Y)
    (gamma' : coupling (push_fdist f mu) (push_fdist f nu)) (y1 : Y) :
  \sum_(y2 : Y) gamma' (f y1) (f y2) = mu y1.
Proof.
have Hvanish : forall x2, (forall y2, f y2 != x2) -> gamma' (f y1) x2 = 0.
  move => x2 Hx2.
  case: (eqVneq (gamma' (f y1) x2) 0) => [-> | Hne] //.
  exfalso.
  move: (coupling_support2 (gamma:=gamma') (x:=f y1) (y:=x2) Hne) => /push_fdist_support [y0 Hy0].
  by move: (Hx2 y0); rewrite Hy0 eqxx.
rewrite -(sum_inj_vanish Hf Hvanish) -(push_fdist_injE Hf mu y1).
exact: (coupling_fst gamma' (f y1)).
Qed.

Lemma pullback_col (mu nu : fdist R Y)
    (gamma' : coupling (push_fdist f mu) (push_fdist f nu)) (y2 : Y) :
  \sum_(y1 : Y) gamma' (f y1) (f y2) = nu y2.
Proof.
have Hvanish : forall x1, (forall y1, f y1 != x1) -> gamma' x1 (f y2) = 0.
  move => x1 Hx1.
  case: (eqVneq (gamma' x1 (f y2)) 0) => [-> | Hne] //.
  exfalso.
  move: (coupling_support (gamma:=gamma') (x:=x1) (y:=f y2) Hne) => /push_fdist_support [y0 Hy0].
  by move: (Hx1 y0); rewrite Hy0 eqxx.
rewrite -(sum_inj_vanish Hf Hvanish) -(push_fdist_injE Hf nu y2).
exact: (coupling_snd gamma' (f y2)).
Qed.

Lemma pullback_ge0 (mu nu : fdist R Y)
    (gamma' : coupling (push_fdist f mu) (push_fdist f nu)) (y1 y2 : Y) :
  0 <= gamma' (f y1) (f y2).
Proof. exact: joint_ge0. Qed.

Lemma pullback_sum1 (mu nu : fdist R Y)
    (gamma' : coupling (push_fdist f mu) (push_fdist f nu)) :
  \sum_(y1 : Y) \sum_(y2 : Y) gamma' (f y1) (f y2) = 1.
Proof.
under eq_bigr => y1 _ do rewrite pullback_row.
exact: fdist_1.
Qed.

Definition coupling_pullback (mu nu : fdist R Y)
    (gamma' : coupling (push_fdist f mu) (push_fdist f nu)) : coupling mu nu :=
  @Coupling R Y Y mu nu
    (@JointFdist R Y Y (fun y1 y2 => gamma' (f y1) (f y2))
      (pullback_ge0 gamma') (pullback_sum1 gamma'))
    (pullback_row gamma') (pullback_col gamma').

Lemma coupling_pullback_cost (d : X -> X -> R) (d0 : Y -> Y -> R)
    (Hd : forall y1 y2, d (f y1) (f y2) = d0 y1 y2)
    (mu nu : fdist R Y)
    (gamma' : coupling (push_fdist f mu) (push_fdist f nu)) :
  coupling_cost d0 (coupling_pullback gamma') = coupling_cost d gamma'.
Proof.
rewrite /coupling_cost /coupling_pullback /=.
have Hvanish_row : forall x : X, (forall y : Y, f y != x) ->
    \sum_(y : X) gamma' x y * d x y = 0.
  move => x Hx.
  apply: big1 => y _.
  suff -> : gamma' x y = 0 by rewrite mul0r.
  case: (eqVneq (gamma' x y) 0) => [-> | Hne] //.
  exfalso.
  move: (coupling_support (gamma:=gamma') (x:=x) (y:=y) Hne) => /push_fdist_support [y0 Hy0].
  by move: (Hx y0); rewrite Hy0 eqxx.
symmetry.
rewrite (sum_inj_vanish Hf Hvanish_row).
apply: eq_bigr => x1 _.
have Hvanish_col : forall y : X, (forall y0 : Y, f y0 != y) ->
    gamma' (f x1) y * d (f x1) y = 0.
  move => y Hy.
  suff -> : gamma' (f x1) y = 0 by rewrite mul0r.
  case: (eqVneq (gamma' (f x1) y) 0) => [-> | Hne] //.
  exfalso.
  move: (coupling_support2 (gamma:=gamma') (x:=f x1) (y:=y) Hne) => /push_fdist_support [y0 Hy0].
  by move: (Hy y0); rewrite Hy0 eqxx.
rewrite (sum_inj_vanish Hf Hvanish_col).
apply: eq_bigr => y1 _.
by rewrite Hd.
Qed.

End Pullback.

Section PushCoupling.
Context {R : realType} {Y X : finType} (f : Y -> X).

Lemma push_fdist_prod_fst (eta : fdist R (Y * Y)%type) :
  push_fdist fst (push_fdist (fun p => (f p.1, f p.2)) eta) =
  push_fdist f (push_fdist fst eta).
Proof.
rewrite !push_fdist_comp.
by congr push_fdist; apply: funext => p.
Qed.

Lemma push_fdist_prod_snd (eta : fdist R (Y * Y)%type) :
  push_fdist snd (push_fdist (fun p => (f p.1, f p.2)) eta) =
  push_fdist f (push_fdist snd eta).
Proof.
rewrite !push_fdist_comp.
by congr push_fdist; apply: funext => p.
Qed.

Definition coupling_push (mu nu : fdist R Y) (gamma : coupling mu nu) :
    coupling (push_fdist f mu) (push_fdist f nu) :=
  coupling_of_fdist
    (eta := push_fdist (fun p => (f p.1, f p.2)) (fdist_of_coupling gamma))
    (etrans (push_fdist_prod_fst (fdist_of_coupling gamma))
      (congr1 (push_fdist f) (push_fdist_fst_of_coupling gamma)))
    (etrans (push_fdist_prod_snd (fdist_of_coupling gamma))
      (congr1 (push_fdist f) (push_fdist_snd_of_coupling gamma))).

Lemma coupling_push_cost (d : X -> X -> R) (d0 : Y -> Y -> R)
    (Hd : forall y1 y2, d (f y1) (f y2) = d0 y1 y2)
    (mu nu : fdist R Y) (gamma : coupling mu nu) :
  coupling_cost d (coupling_push gamma) = coupling_cost d0 gamma.
Proof.
rewrite !coupling_cost_pcost /coupling_push fdist_of_coupling_of_fdist.
rewrite (pcost_push Hd).
by rewrite -coupling_cost_pcost.
Qed.

End PushCoupling.

(** The main transport theorem: the Kantorovich lifting of an
    isometric relabelling of [mu],[nu] along an injective map [f]
    computes the same value whether taken before or after the
    relabelling. This is what lets [gkantorovich] below be computed
    on any finite ambient witness set. *)
Theorem kantorovich_lifting_push {R : realType} {Y X : finType}
    (f : Y -> X) (Hf : injective f)
    (d : X -> X -> R) (d0 : Y -> Y -> R)
    (Hd : forall y1 y2, d (f y1) (f y2) = d0 y1 y2)
    (Hd_nonneg : forall x1 x2, 0 <= d x1 x2)
    (Hd0_nonneg : forall y1 y2, 0 <= d0 y1 y2) (mu nu : fdist R Y) :
  kantorovich_lifting d (push_fdist f mu) (push_fdist f nu) =
  kantorovich_lifting d0 mu nu.
Proof.
apply: le_anti; apply/andP; split.
- apply: le_of_all_strict_upper_bounds => delta Hdelta.
  have Heta : 0 < delta - kantorovich_lifting d0 mu nu by rewrite subr_gt0.
  have [gamma Hgamma] := kantorovich_almost_optimal (d:=d0) mu nu Hd0_nonneg Heta.
  apply: ltW.
  apply: (le_lt_trans (kantorovich_le_coupling_cost (coupling_push f gamma) Hd_nonneg)).
  rewrite (coupling_push_cost Hd).
  by move: Hgamma; rewrite addrC subrK.
- apply: le_of_all_strict_upper_bounds => delta Hdelta.
  have Heta : 0 < delta - kantorovich_lifting d (push_fdist f mu) (push_fdist f nu)
    by rewrite subr_gt0.
  have [gamma' Hgamma'] := kantorovich_almost_optimal
    (d:=d) (push_fdist f mu) (push_fdist f nu) Hd_nonneg Heta.
  apply: ltW.
  apply: (le_lt_trans (kantorovich_le_coupling_cost
    (coupling_pullback Hf gamma') Hd0_nonneg)).
  rewrite (coupling_pullback_cost Hf Hd).
  by move: Hgamma'; rewrite addrC subrK.
Qed.

(* ============================================================
   Part 2: [gkantorovich], the Kantorovich lifting on [gdist R A]
   itself -- computed via the canonical finite witness set
   [finsupp mu `|` finsupp nu], and shown independent of that choice
   ([gkantorovich_restrict]): computing it by restricting to *any*
   larger finite [B] gives the same answer.  This is the missing
   ingredient M1's correction note (in [BarycentricNormalization.v])
   identifies: [K(d_A)] as a genuine, well-defined binary operation
   on [D(A)], not just a formula relative to one fixed ambient
   finType.
   ============================================================ *)

Section GDistWiden.
Context {R : realType} {A : choiceType}.

(** The one semantic fact this file's header advertises: restricting
    [mu] to a larger finite ambient set [B'] is the same, as a
    distribution, as restricting to [B] and then relabelling via the
    inclusion [B -> B']. Combined with [kantorovich_lifting_push] this
    is exactly the "coupling support is confined to the marginals'
    supports" argument from the M1 correction note, specialized to
    [fincl]. *)
Lemma push_fdist_restrict_widen (mu : gdist R A) (B B' : {fset A})
    (H : (B `<=` B')%fset) (HB : (finsupp mu `<=` B)%fset) :
  push_fdist (fincl H) (gdist_restrict B mu HB) =
  gdist_restrict B' mu (fsubset_trans HB H).
Proof.
apply: fdist_ext => x'.
rewrite gdist_restrictE.
case: (boolP (fsval x' \in B)) => Hx'.
- suff -> : x' = fincl H (FSetSub Hx').
  + by rewrite (push_fdist_injE (fincl_inj (AsubB:=H))) gdist_restrictE.
  + by apply: val_inj.
- have Hmux' : mu (fsval x') = 0.
    apply: fsfun_dflt.
    apply: contra Hx' => Hin.
    exact: (fsubsetP HB _ Hin).
  rewrite Hmux' push_fdistE big_pred0 //.
  move => y; apply/negbTE; apply/negP => /eqP Hy.
  by move: Hx'; rewrite -Hy; case: (y) => /= v Hv; rewrite Hv.
Qed.

(** The Kantorovich lifting computed by restricting [mu],[nu] to a
    finite ambient set [B] agrees with the lifting computed on any
    larger ambient set [B']: instantiate the generic transport
    theorem [kantorovich_lifting_push] at the inclusion [fincl H]. *)
Theorem gdist_kantorovich_widen (d : A -> A -> R) (Hd : forall x y, 0 <= d x y)
    (mu nu : gdist R A) (B B' : {fset A}) (H : (B `<=` B')%fset)
    (HmuB : (finsupp mu `<=` B)%fset) (HnuB : (finsupp nu `<=` B)%fset) :
  kantorovich_lifting (fun x y : B => d (fsval x) (fsval y))
    (gdist_restrict B mu HmuB) (gdist_restrict B nu HnuB) =
  kantorovich_lifting (fun x y : B' => d (fsval x) (fsval y))
    (gdist_restrict B' mu (fsubset_trans HmuB H)) (gdist_restrict B' nu (fsubset_trans HnuB H)).
Proof.
rewrite -(push_fdist_restrict_widen (mu:=mu) H HmuB) -(push_fdist_restrict_widen (mu:=nu) H HnuB).
symmetry.
apply: (kantorovich_lifting_push (f:=fincl H)).
- exact: (fincl_inj (AsubB:=H)).
- by [].
- move => x1 x2; exact: Hd.
- move => y1 y2; exact: Hd.
Qed.

Lemma gdist_restrict_irrel (mu : gdist R A) (B : {fset A})
    (H1 H2 : (finsupp mu `<=` B)%fset) :
  gdist_restrict B mu H1 = gdist_restrict B mu H2.
Proof. apply: fdist_ext => x; by rewrite !gdist_restrictE. Qed.

(** [K(d_A)] as a genuine binary operation on [D(A) := gdist R A]:
    the Kantorovich lifting of [mu],[nu], computed via the canonical
    finite witness set [finsupp mu `|` finsupp nu]. *)
Definition gkantorovich (d : A -> A -> R) (mu nu : gdist R A) : R :=
  kantorovich_lifting
    (fun x y : (finsupp mu `|` finsupp nu)%fset => d (fsval x) (fsval y))
    (gdist_restrict _ mu (fsubsetUl _ _)) (gdist_restrict _ nu (fsubsetUr _ _)).

(** [gkantorovich] is well-defined independently of the finite
    witness set used to compute it: restricting to *any* finite [B]
    containing both supports gives the same value as the canonical
    one. This is the fact the M1 correction note identifies as the
    missing ingredient for an arbitrary-carrier Corollary 4.7. *)
Theorem gkantorovich_restrict (d : A -> A -> R) (Hd : forall x y, 0 <= d x y)
    (mu nu : gdist R A) (B : {fset A})
    (HmuB : (finsupp mu `<=` B)%fset) (HnuB : (finsupp nu `<=` B)%fset) :
  gkantorovich d mu nu =
  kantorovich_lifting (fun x y : B => d (fsval x) (fsval y))
    (gdist_restrict B mu HmuB) (gdist_restrict B nu HnuB).
Proof.
rewrite /gkantorovich.
pose B0 := (finsupp mu `|` finsupp nu)%fset.
pose Bu := (B `|` B0)%fset.
rewrite (gdist_kantorovich_widen Hd (B:=B0) (B':=Bu)
  (fsubsetUr _ _) (fsubsetUl _ _) (fsubsetUr _ _)).
symmetry.
rewrite (gdist_kantorovich_widen Hd (B:=B) (B':=Bu)
  (fsubsetUl _ _) HmuB HnuB).
congr kantorovich_lifting; exact: gdist_restrict_irrel.
Qed.

End GDistWiden.

