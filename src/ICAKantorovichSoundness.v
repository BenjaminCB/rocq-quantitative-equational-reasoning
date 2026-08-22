From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp Require Import all_classical reals.
From mathcomp Require Import ring lra.

From Template Require Import Signature FuzzyRelation FRelDeduction.
From Template Require Import ProbabilityDistribution KantorovichProperties ICA.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* ============================================================
   The finite-carrier Kantorovich ICA model

   This file contains:

     - the finite-carrier Kantorovich fuzzy space,
     - the distribution interpretation of [ica_plus],
     - ICA modelhood (Proposition 4.6),
     - the Dirac interpretation (Proposition 4.5), and
     - finite-carrier Kantorovich soundness (Corollary 4.7).

   [X : finType] is explicit throughout.  Nothing here depends on the
   arbitrary-carrier finite-support migration, and nothing here uses
   optimal-coupling existence: modelhood is not a compactness result, and the
   almost-optimal interface [kantorovich_convex_mixture] is exactly what the
   interpolation axiom needs.

   Soundness proper is [derives_full_sound] in [FRelDeduction.v]: it holds at
   every interpretation, because [satisfies] quantifies over all of them.  The
   [finite_kantorovich_*] theorems at the end of this file are Corollary 4.7 of
   the compactness paper, that theorem instantiated at the Dirac
   interpretation.  Dirac is not a restriction on soundness; it is the instance
   whose values are the distributions [[s]] and [[t]] denoted by the terms.

   In this development [d] is an implicit argument recovered from the range
   hypothesis, because the hypothesis mentions it and [Strict Implicit] is
   unset.  This is why [KantorovichProperties.v] writes
   [kantorovich_dirac_le x y Hd] with no [d], and why the definitions below are
   applied as [kantorovich_algebra Hd].
   ============================================================ *)

Lemma ica_weight_complementE {R : realType} (p : ica_weight R) :
  ica_weight_val (ica_weight_complement p) = (1 - ica_weight_val p)%R.
Proof. reflexivity. Qed.

Lemma ica_weight_productE {R : realType} (p q : ica_weight R) :
  ica_weight_val (ica_weight_product p q) =
  (ica_weight_val p * ica_weight_val q)%R.
Proof. reflexivity. Qed.

Lemma ica_weight_assoc_innerE {R : realType} (p q : ica_weight R) :
  ica_weight_val (ica_weight_assoc_inner p q) =
  ((1 - ica_weight_val p) * ica_weight_val q /
  (1 - ica_weight_val p * ica_weight_val q))%R.
Proof. reflexivity. Qed.

Lemma ica_weightE {R : realType} (p : ica_weight R) :
  weight (ica_probability_weight p) = ica_weight_val p.
Proof. reflexivity. Qed.

Lemma ica_weight_product_lt1 {R : realType} (p q : ica_weight R) :
  (0 < 1 - ica_weight_val p * ica_weight_val q)%R.
Proof.
  have /andP [H0 _] := ica_weight_open 
    (ica_weight_complement (ica_weight_product p q)).
  apply: H0.
Qed.

Lemma weighted_sum_idem {R : realType}
    (p : probability_weight R) (a : R) :
  weighted_sum p a a = a.
Proof.
  by rewrite /weighted_sum; lra.
Qed.

Lemma weighted_sum_skew_comm {R : realType}
    (p : ica_weight R) (a b : R) :
  weighted_sum (ica_probability_weight p) a b =
  weighted_sum (ica_probability_weight (ica_weight_complement p)) b a.
Proof.
  by rewrite /weighted_sum /=; lra.
Qed.

Lemma weighted_sum_skew_assoc {R : realType}
    (p q : ica_weight R) (a b c : R) :
  weighted_sum (ica_probability_weight q)
    (weighted_sum (ica_probability_weight p) a b) c =
  weighted_sum (ica_probability_weight (ica_weight_product p q)) a
    (weighted_sum (ica_probability_weight (ica_weight_assoc_inner p q))
      b c).
Proof.
  rewrite /weighted_sum /=.
  have Hne : (1 - ica_weight_val p * ica_weight_val q != 0)%R.
    by rewrite gt_eqF // ica_weight_product_lt1.
  field.
  apply: Hne.
Qed.

Lemma convex_mixtureE {R : realType} {X : finType}
    (p : probability_weight R)
    (mu nu : probability_distribution R X) (x : X) :
  convex_mixture p mu nu x = weighted_sum p (mu x) (nu x).
Proof. reflexivity. Qed.

Lemma convex_mixture_idem {R : realType} {X : finType}
    (p : probability_weight R) (mu : probability_distribution R X) :
  convex_mixture p mu mu = mu.
Proof.
  apply: probability_distribution_ext => x.
  by rewrite convex_mixtureE weighted_sum_idem.
Qed.

Lemma convex_mixture_skew_comm {R : realType} {X : finType}
    (p : ica_weight R) (mu nu : probability_distribution R X) :
  convex_mixture (ica_probability_weight p) mu nu =
  convex_mixture (ica_probability_weight (ica_weight_complement p)) nu mu.
Proof.
  apply: probability_distribution_ext => x.
  by rewrite convex_mixtureE weighted_sum_skew_comm.
Qed.

Lemma convex_mixture_skew_assoc {R : realType} {X : finType}
    (p q : ica_weight R) (mu nu xi : probability_distribution R X) :
  convex_mixture (ica_probability_weight q)
    (convex_mixture (ica_probability_weight p) mu nu) xi =
  convex_mixture (ica_probability_weight (ica_weight_product p q)) mu
    (convex_mixture
      (ica_probability_weight (ica_weight_assoc_inner p q)) nu xi).
Proof.
  apply: probability_distribution_ext => x.
  by rewrite convex_mixtureE weighted_sum_skew_assoc.
Qed.

Definition kantorovich_ops {R : realType} {X : finType} :
    algebra_ops (@ica_signature R) (probability_distribution R X) :=
  fun f =>
    match f with
    | ica_plus p =>
        fun args =>
          convex_mixture (ica_probability_weight p)
            (args (inord 0)) (args (inord 1))
    end.

Section KantorovichModel.
Context {R : realType} {X : finType}.
Variable d : X -> X -> R.
Hypothesis Hd : forall x y, (0 <= d x y <= 1)%R.

Definition finite_fuzzy_space : fuzzy_space R :=
  {| fcarrier := X; frel := d; frel_range := Hd |}.

Definition kantorovich_fuzzy_space : fuzzy_space R :=
  {| fcarrier := probability_distribution R X;
    frel := kantorovich_lifting d;
    frel_range := fun mu nu => fuzzy_kantorovich_lifting mu nu Hd |}.

Definition kantorovich_algebra : FuzzyAlgebra R (@ica_signature R) :=
  {| fa_space := kantorovich_fuzzy_space;
    fa_ops := kantorovich_ops |}.

Lemma kantorovich_eval_op {Y : Type}
    (rho : Y -> probability_distribution R X)
    (p : ica_weight R) (s t : term (@ica_signature R) Y) :
  fuzzy_eval kantorovich_algebra rho (s <+ p +> t) =
  convex_mixture (ica_probability_weight p)
    (fuzzy_eval kantorovich_algebra rho s)
    (fuzzy_eval kantorovich_algebra rho t).
Proof.
  rewrite /ica_op /=.
  by rewrite !inordK.
Qed.

Theorem kantorovich_models_ica :
  fuzzy_models kantorovich_algebra (@ica_theory R).
Proof.
  rewrite /fuzzy_models.
  move => Y phi Hphi.
  case: Hphi => [p | p | p q | p eps delta Heps Hdelta] rho.
  - by rewrite kantorovich_eval_op convex_mixture_idem.
  - by rewrite !kantorovich_eval_op convex_mixture_skew_comm.
  - by rewrite !kantorovich_eval_op convex_mixture_skew_assoc.
  - rewrite !kantorovich_eval_op.
    apply: (le_trans (kantorovich_convex_mixture _ _ _ _ _ Hd)).
    apply: weighted_sum_le.
    - apply: (le_trans (interpretation_nexp rho (inord 0) (inord 2))).
      by rewrite /= /ica_interp_rel !inordK.
    - apply: (le_trans (interpretation_nexp rho (inord 1) (inord 3))).
      by rewrite /= /ica_interp_rel !inordK.
Qed.

Definition dirac_interpretation :
    interpretation finite_fuzzy_space kantorovich_algebra :=
  @Build_interpretation R (@ica_signature R)
    finite_fuzzy_space kantorovich_algebra
    (fun x : X => dirac x)
    (fun x y => kantorovich_dirac_le x y Hd).

Definition ica_term_distribution (s : term (@ica_signature R) X) :
    probability_distribution R X :=
  fuzzy_eval kantorovich_algebra (fun x : X => dirac x) s.

Theorem finite_kantorovich_soundness
    (s t : term (@ica_signature R) X) (eps : R) :
  @derives_full R (@ica_signature R) (@ica_theory R)
    finite_fuzzy_space (QEqJ eps s t) ->
  (kantorovich_lifting d
    (ica_term_distribution s) (ica_term_distribution t) <= eps)%R.
Proof.
  move => H.
  apply: (derives_full_sound kantorovich_models_ica H dirac_interpretation).
Qed.

Theorem finite_kantorovich_eq_soundness
    (s t : term (@ica_signature R) X) :
  @derives_full R (@ica_signature R) (@ica_theory R)
    finite_fuzzy_space (EqJ s t) ->
  ica_term_distribution s = ica_term_distribution t.
Proof.
  move => H.
  apply: (derives_full_sound kantorovich_models_ica H dirac_interpretation).
Qed.

Theorem finite_kantorovich_soundness_fin
    (s t : term (@ica_signature R) X) (eps : R) :
  @derives_fin R (@ica_signature R) (@ica_theory R)
    finite_fuzzy_space (QEqJ eps s t) ->
  (kantorovich_lifting d
    (ica_term_distribution s) (ica_term_distribution t) <= eps)%R.
Proof.
  move => H.
  apply: (derives_fin_sound kantorovich_models_ica H dirac_interpretation).
Qed.
End KantorovichModel.
