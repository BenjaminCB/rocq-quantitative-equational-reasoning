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

Definition ica_weight_half (R : realType) : ica_weight R.
Proof.
  refine {| ica_weight_val := 1 / 2%:R |}.
  apply/andP; split; lra.
Defined.

Definition ica_weight_clamp {R : realType} (r : R) : ica_weight R :=
  match Bool.bool_dec (0 < r < 1) true with
  | left H => {| ica_weight_val := r; ica_weight_open := H |}
  | right _ => ica_weight_half R
  end.

Lemma ica_weight_clampE {R : realType} (r : R) :
  (0 < r < 1) -> ica_weight_val (ica_weight_clamp r) = r.
Proof.
  move => H.
  rewrite /ica_weight_clamp.
  case: (Bool.bool_dec (0 < r < 1) true); by [].
Qed.

Definition cond_mass {R : realType} {X : finType} 
    (mu : probability_distribution R X) (x y : X) : R :=
  if (mu x < 1) 
  then (if y == x then 0 else mu y / (1 - mu x))
  else mu y.

Lemma cond_mass_ge0 {R : realType} {X : finType}
    (mu : probability_distribution R X) (x : X) :
  forall y, (0 <= cond_mass mu x y).
Proof.
  move => y.
  rewrite /cond_mass.
  case: ifP => [Hlt|_]; last apply: probability_mass_ge0.
  have Hpos : (0 < 1 - mu x) by rewrite subr_gt0.
  case: ifP => _; first apply: lexx.
  by apply: divr_ge0; [apply: probability_mass_ge0 | apply: ltW].
Qed.

Lemma cond_mass_total {R : realType} {X : finType}
    (mu : probability_distribution R X) (x : X) :
  \sum_(y : X) cond_mass mu x y = 1.
Proof.
  rewrite /cond_mass.
  case Hlt: (mu x < 1); last apply: probability_mass_total.
  have Hpos : (0 < 1 - mu x) by rewrite subr_gt0.
  rewrite (bigD1 x) //= eqxx add0r.
  rewrite (eq_bigr (fun y => mu y / (1 - mu x))); last first.
  - by move => y Hy; rewrite (negbTE Hy).
  - rewrite -big_distrl /=.
    have Hrest : \sum_(y : X | y != x) mu y = (1 - mu x)%R.
      have := probability_mass_total mu.
      rewrite (bigD1 x) //= => Htot.
      by rewrite -Htot addrC addrK.
    by rewrite Hrest mulfV //= gt_eqF.
Qed.

Definition condition {R : realType} {X : finType}
    (mu : probability_distribution R X) (x : X) :
    probability_distribution R X :=
  {| probability_mass := cond_mass mu x;
     probability_mass_ge0 := cond_mass_ge0 mu x; 
     probability_mass_total := cond_mass_total mu x |}.

Lemma conditionE {R : realType} {X : finType}
    (mu : probability_distribution R X) (x y : X) :
  (mu x < 1)%R ->
  condition mu x y = (if y == x then 0 else mu y / (1 - mu x))%R.
Proof.
  move => Hlt1.
  rewrite /condition //= /cond_mass.
  case Heq: (mu x < 1); by rewrite ?Hlt1 in Heq.
Qed.

Lemma condition_support {R : realType} {X : finType}
    (mu : probability_distribution R X) (x : X) :
  (mu x < 1) -> x \in distribution_support mu ->
  distribution_support (condition mu x) =
    distribution_support mu :\ x.
Proof.
  move => Hlt Hin.
  have Hne0 : (1 - mu x != 0) by rewrite gt_eqF //= subr_gt0.
  apply/setP => y.
  rewrite !inE conditionE //=.
  case: ifP => [Heq | Hneq].
  - by rewrite eqxx.
  - rewrite Bool.andb_true_l.
    rewrite mulf_eq0 invr_eq0.
    by rewrite (negbTE Hne0) orbF.
Qed.

Lemma condition_recover {R : realType} {X : finType}
    (mu : probability_distribution R X) (x : X) :
  (mu x < 1) ->
  x \in distribution_support mu ->
  convex_mixture (ica_probability_weight (ica_weight_clamp (mu x)))
    (dirac x) (condition mu x) = mu.
Proof.
  move => Hlt1 Hin.
  rewrite inE in Hin.
  have Hgt0 : (0 < mu x). {
    rewrite lt_neqAle.
    apply/andP; split.
    - rewrite eq_sym.
      apply: Hin.
    - apply: probability_mass_ge0.
  }
  have Hne0 : (1 - mu x != 0) by rewrite gt_eqF //= subr_gt0.
  apply: probability_distribution_ext => y.
  rewrite /convex_mixture /weighted_sum //= /cond_mass.

  rewrite ica_weight_clampE; last by apply/andP; split.
  case: ifP => [Heq | Hneq]; case: ifP => [Hlt1' | Hnlt1'].
  - move/eqP: Heq => {}Heq.
    by rewrite mulr1 mulr0 addr0 Heq.
  - by rewrite Hlt1 in Hnlt1'.
  - by rewrite mulr0 add0r mulrCA divff //= mulr1.
  - by rewrite Hlt1 in Hnlt1'.
Qed.