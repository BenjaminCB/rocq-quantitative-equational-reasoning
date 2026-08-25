From Stdlib Require Import Logic.FunctionalExtensionality.
From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp Require Import all_classical reals.
From mathcomp Require Import ring lra.

From Template Require Import Signature FuzzyRelation FRelDeduction.
From Template Require Import ProbabilityDistribution KantorovichProperties ICA.
From Template Require Import ICAKantorovichSoundness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Fixpoint term_distribution {R : realType} {X : finType}
    (s : term (@ica_signature R) X) : probability_distribution R X :=
  match s with
  | Var x => dirac x
  | App f args =>
      match f with
      | ica_plus p =>
          convex_mixture (ica_probability_weight p)
            (term_distribution (args (inord 0)))
            (term_distribution (args (inord 1)))
      end
  end.

Lemma term_distribution_op {R : realType} {X : finType}
    (p : ica_weight R) (s t : term (@ica_signature R) X) :
  term_distribution (s <+ p +> t) =
  convex_mixture (ica_probability_weight p)
    (term_distribution s) (term_distribution t).
Proof.
  rewrite /ica_op /= !inordK.
  - reflexivity.
  - by [].
  - by [].
Qed.  

Lemma term_distributionE {R : realType} {X : finType}
    (d : X -> X -> R) (Hd : forall x y, (0 <= d x y <= 1)%R)
    (s : term (@ica_signature R) X) :
  ica_term_distribution Hd s = term_distribution s.
Proof.
  rewrite /ica_term_distribution.
  elim: s => [x | f args IH] //=.
  case: f args IH => p args IH /=.
  by rewrite (IH (inord 0)) (IH (inord 1)).
Qed.

Lemma ica_subst_op {R : realType} {X Y : Type}
    (sigma : X -> term (@ica_signature R) Y)
    (p : ica_weight R) (a b : term (@ica_signature R) X) :
  subst_term sigma (a <+ p +> b) =
  (subst_term sigma a) <+ p +> (subst_term sigma b).
Proof.
  rewrite /ica_op //=.
  congr App.
  apply: functional_extensionality => x /=.
  case: (Nat.eqb x 0); by [].
Qed.

Lemma ica_skew_comm_instance {R : realType}
    (mode : frel_derivation_mode) (X : fuzzy_space R)
    (p : ica_weight R) (s t : term (@ica_signature R) (fcarrier X)) :
  @frel_derives R ica_signature (@ica_theory R) mode X
    (EqJ (s <+ p +> t) (t <+ ica_weight_complement p +> s)).
Proof.
  pose sigma := fun i : fcarrier (ica_full_space R 2) =>
    if Nat.eqb (i : nat) 0 then s else t.
  have E0 : sigma (inord 0) = s by rewrite /sigma /= inordK.
  have E1 : sigma (inord 1) = t by rewrite /sigma /= inordK.
  have -> : (s <+ p +> t) =
      subst_term sigma ((Var (inord 0)) <+ p +> (Var (inord 1))).
    by rewrite ica_subst_op /= E0 E1.
  have -> : (t <+ ica_weight_complement p +> s) =
      subst_term sigma
        ((Var (inord 1)) <+ ica_weight_complement p +> (Var (inord 0))).
    by rewrite ica_subst_op /= E0 E1.
  apply: (FD_Subst
    (X := ica_full_space R 2)
    (phi := EqJ ((Var (inord 0)) <+ p +> (Var (inord 1)))
      ((Var (inord 1)) <+ ica_weight_complement p +> (Var (inord 0))))
    (sigma := sigma)).
  - apply: FD_Init. 
    apply: ICA_Skew_Comm.
  - move => x y.
    apply: FD_Max.
Qed.

Lemma ica_skew_assoc_instance {R : realType}
    (mode : frel_derivation_mode) (X : fuzzy_space R)
    (p q : ica_weight R) (s t u : term (@ica_signature R) (fcarrier X)) :
  @frel_derives R ica_signature (@ica_theory R) mode X
    (EqJ ((s <+ p +> t) <+ q +> u)
      (s <+ ica_weight_product p q +>
        (t <+ ica_weight_assoc_inner p q +> u))).
Proof.
  pose sigma := fun i : fcarrier (ica_full_space R 3) =>
    match (i : nat) with
    | 0 => s 
    | 1 => t
    | _ => u
    end.
  have E0 : sigma (inord 0) = s by rewrite /sigma /= inordK.
  have E1 : sigma (inord 1) = t by rewrite /sigma /= inordK.
  have E2 : sigma (inord 2) = u by rewrite /sigma /= inordK.
  have -> : (s <+ p +> t <+ q +> u) =
      subst_term sigma 
        ((Var (inord 0)) <+ p +> 
         (Var (inord 1)) <+ q +> 
         (Var (inord 2))).
    by rewrite !ica_subst_op /= E0 E1 E2.
  have -> : 
      ((s <+ ica_weight_product p q +>
       (t <+ ica_weight_assoc_inner p q +> u))) = 
      subst_term sigma
       (((Var (inord 0)) <+ ica_weight_product p q +>
        ((Var (inord 1)) <+ ica_weight_assoc_inner p q +> (Var (inord 2))))).
    by rewrite !ica_subst_op /= E0 E1 E2.
  apply: (FD_Subst
    (X := ica_full_space R 3)
    (phi := EqJ 
      ((Var (inord 0)) <+ p +> (Var (inord 1)) <+ q +>  (Var (inord 2)))
      (((Var (inord 0)) <+ ica_weight_product p q +>
        ((Var (inord 1)) <+ ica_weight_assoc_inner p q +> (Var (inord 2)))))
    )
    (sigma := sigma)).
  - apply: FD_Init. 
    apply: ICA_Skew_Assoc.
  - move => x y.
    apply: FD_Max.
Qed.

Lemma ica_plus_congr {R : realType}
    (mode : frel_derivation_mode) (X : fuzzy_space R)
    (p : ica_weight R)
    (s s' t t' : term (@ica_signature R) (fcarrier X)) :
  @frel_derives R ica_signature (@ica_theory R) mode X (EqJ s s') ->
  @frel_derives R ica_signature (@ica_theory R) mode X (EqJ t t') ->
  @frel_derives R ica_signature (@ica_theory R) mode X
    (EqJ (s <+ p +> t) (s' <+ p +> t')).
Proof.
  move => H1 H2.
  apply: FD_EqCong => i //=.
  case: (Nat.eqb i 0); [apply: H1 | apply H2].
Qed.

Fixpoint term_vars {R : realType} {X : finType}
    (s : term (@ica_signature R) X) : {set X} :=
  match s with
  | Var x => [set x]
  | App f args =>
      match f with
      | ica_plus p =>
          term_vars (args (inord 0)) :|: term_vars (args (inord 1))
      end
  end.

Lemma weighted_sum_gt0 {R : realType} (p : ica_weight R) (a b : R) :
  (0 <= a)%R -> (0 <= b)%R ->
  (0 < weighted_sum (ica_probability_weight p) a b)%R =
  ((0 < a)%R || (0 < b)%R).
Proof.
  move => Ha Hb.
  have /andP [Hp0 Hp1] := ica_weight_open p.
  case: (ltP 0 a) => Ea; case: (ltP 0 b) => Eb; rewrite /weighted_sum //=; nra.
Qed.

Lemma term_distribution_support {R : realType} {X : finType}
    (s : term (@ica_signature R) X) :
  distribution_support (term_distribution s) = term_vars s.
Proof.
  elim: s => [ x | f args i ].
  - rewrite /distribution_support /dirac //=.
    apply/setP => x'; rewrite !inE.
    by case: (x' == x); rewrite ?oner_neq0 ?eq_refl.
  - case: f args i => p args i /=.
    apply/setP => y; rewrite !inE.
    rewrite convex_mixtureE -(i (inord 0)) -(i (inord 1)) !inE.
    have Ha := probability_mass_ge0 (term_distribution (args (inord 0))) y.
    have Hb := probability_mass_ge0 (term_distribution (args (inord 1))) y.
    have Hw := weighted_sum_ge0 (ica_probability_weight p) Ha Hb.
    have gt0E : forall z : R, 0 <= z -> (z != 0) = (0 < z).
      by move=> z Hz; rewrite lt0r Hz andbT.
    rewrite (gt0E _ Ha) (gt0E _ Hb) (gt0E _ Hw).
    exact: weighted_sum_gt0.
Qed.

Lemma term_distribution_support_neq0 {R : realType} {X : finType}
    (s : term (@ica_signature R) X) :
  distribution_support (term_distribution s) != finset.set0.
Proof.
  rewrite term_distribution_support.
  elim: s => [x | f args i].
  - rewrite /term_vars /=.
    apply/set0Pn.
    exists x; apply: set11.
  - case: f args i => p args i /=.
    apply: subset_neq0 (finset.subsetUl _ _) (i (inord 0)).
Qed.
