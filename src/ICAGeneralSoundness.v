(* ============================================================
   M1b: Corollary 4.7 (Kantorovich soundness) for an arbitrary
   [choiceType] carrier [A], via the finitely-supported-distribution
   type [gdist R A] built in [GeneralDistribution.v].

   This mirrors [ICAKantorovichSoundness.v]'s finType construction
   (the Dirac interpretation into the Kantorovich model, ICA
   modelhood, and soundness via [derives_full_sound]/
   [derives_fin_sound]) but with [fdist R X] (X : finType) replaced
   by [gdist R A] (A : choiceType) throughout, using
   [gkantorovich]/[gkantorovich_restrict] to reduce every fact needed
   to the already-proved finType statements at a suitably large
   finite witness set.
   ============================================================ *)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import all_classical reals.
From mathcomp Require Import finmap interval_inference convex.

From Template Require Import Signature FuzzyRelation FRelDeduction.
From Template Require Import ProbabilityDistribution GeneralDistribution.
From Template Require Import KantorovichProperties ICA ICAKantorovichSoundness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope convex_scope.
Local Open Scope fset_scope.

Section GConv.
Context {R : realType} {A : choiceType}.

(** The convex combination of two [gdist]s: a mass function supported
    on the union of their supports, given pointwise by [weighted_sum].
    (Its finite support is a subset of that union, not necessarily
    equal to it -- some mass can cancel when [p] is [0] or [1] -- so
    it is built via the explicit [fsfun] comprehension rather than
    reusing the union set as the support outright.) *)
Definition gconv_fsfun (p : probability_weight R) (mu nu : gdist R A) :
    {fsfun A -> R with 0} :=
  [fsfun a in (finsupp mu `|` finsupp nu) => weighted_sum p (mu a) (nu a) | 0].

Lemma gconv_fsfunE (p : probability_weight R) (mu nu : gdist R A) (a : A) :
  gconv_fsfun p mu nu a = weighted_sum p (mu a) (nu a).
Proof.
rewrite /gconv_fsfun fsfunE inE.
case: ifP => // /norP [Hmu Hnu].
rewrite (fsfun_dflt Hmu) (fsfun_dflt Hnu) /weighted_sum.
by rewrite mulr0 mulr0 addr0.
Qed.

Lemma finsupp_gconv_sub (p : probability_weight R) (mu nu : gdist R A) :
  (finsupp (gconv_fsfun p mu nu) `<=` finsupp mu `|` finsupp nu)%fset.
Proof.
apply/fsubsetP => a.
rewrite mem_finsupp gconv_fsfunE => Hne.
case: (boolP (a \in finsupp mu `|` finsupp nu)%fset) => // HaB.
move: HaB; rewrite in_fsetU negb_or => /andP [Hmu Hnu].
have Hz : weighted_sum p (mu a) (nu a) = 0.
  by rewrite (fsfun_dflt Hmu) (fsfun_dflt Hnu) /weighted_sum mulr0 mulr0 addr0.
by rewrite Hz eqxx in Hne.
Qed.

Definition gconv (p : probability_weight R) (mu nu : gdist R A) : gdist R A.
refine (@GDist R A (gconv_fsfun p mu nu) _ _).
- move => a; rewrite gconv_fsfunE; exact: weighted_sum_ge0 (gd_ge0 mu a) (gd_ge0 nu a).
- pose B := (finsupp mu `|` finsupp nu)%fset.
  have HmuB : (finsupp mu `<=` B)%fset := fsubsetUl _ _.
  have HnuB : (finsupp nu `<=` B)%fset := fsubsetUr _ _.
  have HgB : (finsupp (gconv_fsfun p mu nu) `<=` B)%fset := finsupp_gconv_sub p mu nu.
  have Hvanish_g : forall a, a \in B -> a \notin finsupp (gconv_fsfun p mu nu) ->
      gconv_fsfun p mu nu a = 0.
    move => a _ Ha; exact: fsfun_dflt Ha.
  have Hvanish_mu : forall a, a \in B -> a \notin finsupp mu -> mu a = 0.
    move => a _ Ha; exact: fsfun_dflt Ha.
  have Hvanish_nu : forall a, a \in B -> a \notin finsupp nu -> nu a = 0.
    move => a _ Ha; exact: fsfun_dflt Ha.
  rewrite -(fsum_support_widen HgB Hvanish_g).
  rewrite (fsum_ext (g := fun a => weighted_sum p (mu a) (nu a))
    (fun a _ => gconv_fsfunE p mu nu a)).
  rewrite /fsum sum_weighted_sum.
  rewrite -/(fsum B mu) -/(fsum B nu).
  rewrite (fsum_support_widen HmuB Hvanish_mu) (fsum_support_widen HnuB Hvanish_nu).
  by rewrite (gd_sum1 mu) (gd_sum1 nu) weighted_sum_one.
Defined.

Lemma gconvE (p : probability_weight R) (mu nu : gdist R A) (a : A) :
  gconv p mu nu a = weighted_sum p (mu a) (nu a).
Proof. exact: gconv_fsfunE. Qed.

Lemma gconv_idem (p : probability_weight R) (mu : gdist R A) :
  gconv p mu mu = mu.
Proof. apply: gdist_ext => a; by rewrite gconvE weighted_sum_idem. Qed.

Lemma gconv_skew_comm (p : ica_weight R) (mu nu : gdist R A) :
  gconv (ica_probability_weight p) mu nu =
  gconv (ica_probability_weight (ica_weight_complement p)) nu mu.
Proof. apply: gdist_ext => a; by rewrite !gconvE weighted_sum_skew_comm. Qed.

Lemma gconv_skew_assoc (p q : ica_weight R) (mu nu xi : gdist R A) :
  gconv (ica_probability_weight q) (gconv (ica_probability_weight p) mu nu) xi =
  gconv (ica_probability_weight (ica_weight_product p q)) mu
    (gconv (ica_probability_weight (ica_weight_assoc_inner p q)) nu xi).
Proof. apply: gdist_ext => a; by rewrite !gconvE weighted_sum_skew_assoc. Qed.

(** Restricting a convex combination to a finite ambient set [B]
    agrees with taking the convex combination of the restrictions --
    a purely pointwise fact, needing no coupling machinery. *)
Lemma gdist_restrict_gconv (p : probability_weight R) (mu nu : gdist R A)
    (B : {fset A}) (HmuB : (finsupp mu `<=` B)%fset) (HnuB : (finsupp nu `<=` B)%fset)
    (HgB : (finsupp (gconv p mu nu) `<=` B)%fset) :
  gdist_restrict B (gconv p mu nu) HgB =
  convex_mixture p (gdist_restrict B mu HmuB) (gdist_restrict B nu HnuB).
Proof.
apply: fdist_ext => x.
by rewrite gdist_restrictE gconvE convex_mixtureE !gdist_restrictE.
Qed.

End GConv.

Section GModel.
Context {R : realType} {A : choiceType}.
Variable d : A -> A -> R.
Hypothesis Hd : forall x y, (0 <= d x y <= 1)%R.

Lemma Hd_le1 : forall x y, (0 <= d x y)%R.
Proof. move => x y; by case/andP: (Hd x y). Qed.

Definition g_fuzzy_space : fuzzy_space R :=
  {| fcarrier := A; frel := d; frel_range := Hd |}.

Lemma gkantorovich_range (mu nu : gdist R A) :
  (0 <= gkantorovich d mu nu <= 1)%R.
Proof.
rewrite /gkantorovich.
apply: fuzzy_kantorovich_lifting => x y; exact: Hd (fsval x) (fsval y).
Qed.

Definition g_kantorovich_fuzzy_space : fuzzy_space R :=
  {| fcarrier := gdist R A; frel := gkantorovich d; frel_range := gkantorovich_range |}.

Definition gkantorovich_ops : algebra_ops (@ica_signature R) (gdist R A) :=
  fun f =>
    match f with
    | ica_plus p =>
        fun args => gconv (ica_probability_weight p) (args (inord 0)) (args (inord 1))
    end.

Definition g_kantorovich_algebra : FuzzyAlgebra R (@ica_signature R) :=
  {| fa_space := g_kantorovich_fuzzy_space; fa_ops := gkantorovich_ops |}.

Lemma gkantorovich_eval_op {Y : Type} (rho : Y -> gdist R A)
    (p : ica_weight R) (s t : term (@ica_signature R) Y) :
  fuzzy_eval g_kantorovich_algebra rho (s <+ p +> t) =
  gconv (ica_probability_weight p)
    (fuzzy_eval g_kantorovich_algebra rho s)
    (fuzzy_eval g_kantorovich_algebra rho t).
Proof. rewrite /ica_op /=. by rewrite !inordK. Qed.

(** The four-way common witness set the interpolation axiom needs:
    large enough to restrict [mu1],[mu2],[nu1],[nu2] and both convex
    mixtures simultaneously. *)
Section FourWay.
Variables mu1 mu2 nu1 nu2 : gdist R A.
Variable p : probability_weight R.

Definition fourway_B : {fset A} :=
  (finsupp mu1 `|` finsupp mu2 `|` (finsupp nu1 `|` finsupp nu2))%fset.

Lemma fourway_mu1 : (finsupp mu1 `<=` fourway_B)%fset.
Proof. exact/fsubset_trans/fsubsetUl/fsubsetUl. Qed.
Lemma fourway_mu2 : (finsupp mu2 `<=` fourway_B)%fset.
Proof. exact/fsubset_trans/fsubsetUl/fsubsetUr. Qed.
Lemma fourway_nu1 : (finsupp nu1 `<=` fourway_B)%fset.
Proof. exact/fsubset_trans/fsubsetUr/fsubsetUl. Qed.
Lemma fourway_nu2 : (finsupp nu2 `<=` fourway_B)%fset.
Proof. exact/fsubset_trans/fsubsetUr/fsubsetUr. Qed.

Lemma fourway_conv_mu : (finsupp (gconv p mu1 mu2) `<=` fourway_B)%fset.
Proof.
apply: (fsubset_trans (finsupp_gconv_sub p mu1 mu2)).
exact: fsubsetUl.
Qed.

Lemma fourway_conv_nu : (finsupp (gconv p nu1 nu2) `<=` fourway_B)%fset.
Proof.
apply: (fsubset_trans (finsupp_gconv_sub p nu1 nu2)).
exact: fsubsetUr.
Qed.

End FourWay.

Lemma gkantorovich_convex_mixture (p : probability_weight R)
    (mu1 mu2 nu1 nu2 : gdist R A) :
  (gkantorovich d (gconv p mu1 mu2) (gconv p nu1 nu2) <=
   weighted_sum p (gkantorovich d mu1 nu1) (gkantorovich d mu2 nu2))%R.
Proof.
pose B := fourway_B mu1 mu2 nu1 nu2.
rewrite (gkantorovich_restrict Hd_le1 (fourway_conv_mu mu1 mu2 nu1 nu2 p)
  (fourway_conv_nu mu1 mu2 nu1 nu2 p)).
rewrite (gkantorovich_restrict Hd_le1 (fourway_mu1 mu1 mu2 nu1 nu2)
  (fourway_nu1 mu1 mu2 nu1 nu2)).
rewrite (gkantorovich_restrict Hd_le1 (fourway_mu2 mu1 mu2 nu1 nu2)
  (fourway_nu2 mu1 mu2 nu1 nu2)).
rewrite (gdist_restrict_gconv (fourway_mu1 mu1 mu2 nu1 nu2) (fourway_mu2 mu1 mu2 nu1 nu2)
  (fourway_conv_mu mu1 mu2 nu1 nu2 p)).
rewrite (gdist_restrict_gconv (fourway_nu1 mu1 mu2 nu1 nu2) (fourway_nu2 mu1 mu2 nu1 nu2)
  (fourway_conv_nu mu1 mu2 nu1 nu2 p)).
apply: kantorovich_convex_mixture.
move => x y; exact: Hd (fsval x) (fsval y).
Qed.

Theorem gkantorovich_models_ica :
  fuzzy_models g_kantorovich_algebra (@ica_theory R).
Proof.
rewrite /fuzzy_models.
move => Y phi Hphi.
case: Hphi => [p | p | p q | p eps delta Heps Hdelta] rho.
- by rewrite gkantorovich_eval_op gconv_idem.
- by rewrite !gkantorovich_eval_op gconv_skew_comm.
- by rewrite !gkantorovich_eval_op gconv_skew_assoc.
- rewrite !gkantorovich_eval_op.
  apply: (le_trans (gkantorovich_convex_mixture _ _ _ _ _)).
  apply: weighted_sum_le.
  + apply: (le_trans (interpretation_nexp rho (inord 0) (inord 2))).
    by rewrite /= /ica_interp_rel !inordK.
  + apply: (le_trans (interpretation_nexp rho (inord 1) (inord 3))).
    by rewrite /= /ica_interp_rel !inordK.
Qed.

(** Restricting the Dirac point mass at [x] to any finite [B]
    containing [x] recovers the finType Dirac mass at the
    corresponding element of [B]. *)
Lemma gdist_restrict_gdirac (x : A) (B : {fset A})
    (H : (finsupp (@gdirac R A x) `<=` B)%fset) (Hx : x \in B) :
  gdist_restrict B (@gdirac R A x) H = dirac_fdist (FSetSub Hx).
Proof.
apply: fdist_ext => y.
rewrite gdist_restrictE /dirac_fdist /= /gdirac /= gdirac_fsfunE.
case: (altP (fsval y =P x)) => Hxy.
- have -> : y = FSetSub Hx by apply: val_inj.
  by rewrite eqxx.
- case: (altP (y =P FSetSub Hx)) => Heq //.
  by move: Hxy; rewrite Heq /= eqxx.
Qed.

Definition gdirac_interpretation :
    interpretation g_fuzzy_space g_kantorovich_algebra.
refine (@Build_interpretation R (@ica_signature R)
  g_fuzzy_space g_kantorovich_algebra gdirac _).
move => x y.
have Hx : x \in (finsupp (@gdirac R A x) `|` finsupp (@gdirac R A y))%fset.
  by rewrite in_fsetU !finsupp_gdirac !in_fset1 eqxx.
have Hy : y \in (finsupp (@gdirac R A x) `|` finsupp (@gdirac R A y))%fset.
  by rewrite in_fsetU !finsupp_gdirac !in_fset1 eqxx orbT.
have Hxsub : (finsupp (@gdirac R A x) `<=`
    (finsupp (@gdirac R A x) `|` finsupp (@gdirac R A y)))%fset.
  exact: fsubsetUl.
have Hysub : (finsupp (@gdirac R A y) `<=`
    (finsupp (@gdirac R A x) `|` finsupp (@gdirac R A y)))%fset.
  exact: fsubsetUr.
rewrite /= (gkantorovich_restrict Hd_le1 Hxsub Hysub).
rewrite (gdist_restrict_gdirac Hxsub Hx) (gdist_restrict_gdirac Hysub Hy).
have Hle := kantorovich_dirac_le (FSetSub Hx) (FSetSub Hy)
  (fun a b => Hd (fsval a) (fsval b)).
exact: Hle.
Defined.

Definition gterm_distribution (s : term (@ica_signature R) A) : gdist R A :=
  fuzzy_eval g_kantorovich_algebra gdirac s.

(** Corollary 4.7, generalized to an arbitrary [choiceType] carrier:
    derivability at the full (possibly infinite) carrier [A] bounds
    the Kantorovich distance between the terms' denoted
    distributions in [D(A)]. *)
Theorem g_kantorovich_soundness (s t : term (@ica_signature R) A) (eps : R) :
  @derives_full R (@ica_signature R) (@ica_theory R) g_fuzzy_space (QEqJ eps s t) ->
  (gkantorovich d (gterm_distribution s) (gterm_distribution t) <= eps)%R.
Proof.
move => H.
exact: (derives_full_sound gkantorovich_models_ica H gdirac_interpretation).
Qed.

Theorem g_kantorovich_eq_soundness (s t : term (@ica_signature R) A) :
  @derives_full R (@ica_signature R) (@ica_theory R) g_fuzzy_space (EqJ s t) ->
  gterm_distribution s = gterm_distribution t.
Proof.
move => H.
exact: (derives_full_sound gkantorovich_models_ica H gdirac_interpretation).
Qed.

Theorem g_kantorovich_soundness_fin (s t : term (@ica_signature R) A) (eps : R) :
  @derives_fin R (@ica_signature R) (@ica_theory R) g_fuzzy_space (QEqJ eps s t) ->
  (gkantorovich d (gterm_distribution s) (gterm_distribution t) <= eps)%R.
Proof.
move => H.
exact: (derives_fin_sound gkantorovich_models_ica H gdirac_interpretation).
Qed.

End GModel.
