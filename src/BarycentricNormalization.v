From Stdlib Require Import Logic.FunctionalExtensionality.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import all_classical reals.
From mathcomp.algebra_tactics Require Import ring lra.

From Template Require Import Signature FuzzyRelation FRelDeduction.
From Template Require Import ProbabilityDistribution KantorovichProperties ICA.
From Template Require Import ICAKantorovichSoundness KantorovichCompactness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Fixpoint term_distribution {R : realType} {X : finType}
    (s : term (@ica_signature R) X) : fdist R X :=
  match s with
  | Var x => dirac_fdist x
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
  case: (ltP 0 a) => Ea; case: (ltP 0 b) => Eb;
    rewrite /weighted_sum /weight ica_probability_weightE //=; nra.
Qed.

Lemma term_distribution_support {R : realType} {X : finType}
    (s : term (@ica_signature R) X) :
  distribution_support (term_distribution s) = term_vars s.
Proof.
  elim: s => [ x | f args i ].
  - rewrite /distribution_support /dirac_fdist //=.
    apply/setP => x'; rewrite !inE.
    by case: (x' == x); rewrite ?oner_neq0 ?eq_refl.
  - case: f args i => p args i /=.
    apply/setP => y; rewrite !inE.
    rewrite convex_mixtureE -(i (inord 0)) -(i (inord 1)) !inE.
    have Ha := fdist_ge0 (term_distribution (args (inord 0))) y.
    have Hb := fdist_ge0 (term_distribution (args (inord 1))) y.
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
  have H01 : (0 < 1 / 2%:R :> R) by lra.
  have H12 : (1 / 2%:R < 1 :> R) by lra.
  exact: mk_ica_weight H01 H12.
Defined.

Definition ica_weight_clamp {R : realType} (r : R) : ica_weight R :=
  match Bool.bool_dec (0 < r < 1) true with
  | left H => mk_ica_weight (elimT andP H).1 (elimT andP H).2
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
    (mu : fdist R X) (x y : X) : R :=
  if (mu x < 1)
  then (if y == x then 0 else mu y / (1 - mu x))
  else mu y.

Lemma cond_mass_ge0 {R : realType} {X : finType}
    (mu : fdist R X) (x : X) :
  forall y, (0 <= cond_mass mu x y).
Proof.
  move => y.
  rewrite /cond_mass.
  case: ifP => [Hlt|_]; last apply: fdist_ge0.
  have Hpos : (0 < 1 - mu x) by rewrite subr_gt0.
  case: ifP => _; first apply: lexx.
  by apply: divr_ge0; [apply: fdist_ge0 | apply: ltW].
Qed.

Lemma cond_mass_total {R : realType} {X : finType}
    (mu : fdist R X) (x : X) :
  \sum_(y : X) cond_mass mu x y = 1.
Proof.
  rewrite /cond_mass.
  case Hlt: (mu x < 1); last exact: fdist_1.
  have Hpos : (0 < 1 - mu x) by rewrite subr_gt0.
  rewrite (bigD1 x) //= eqxx add0r.
  under eq_bigr => y Hy do rewrite (negbTE Hy).
  rewrite -big_distrl /=.
  have Hrest : \sum_(y : X | y != x) mu y = (1 - mu x)%R.
    have Htot := fdist_1 mu.
    rewrite (bigD1 x) //= in Htot.
    by lra.
  by rewrite Hrest mulfV //= gt_eqF.
Qed.

Definition condition {R : realType} {X : finType}
    (mu : fdist R X) (x : X) : fdist R X :=
  {| fdist_val := cond_mass mu x;
     fdist_ge0 := cond_mass_ge0 mu x;
     fdist_1 := cond_mass_total mu x |}.

Lemma conditionE {R : realType} {X : finType}
    (mu : fdist R X) (x y : X) :
  (mu x < 1)%R ->
  condition mu x y = (if y == x then 0 else mu y / (1 - mu x))%R.
Proof.
  move => Hlt1.
  rewrite /condition //= /cond_mass.
  case Heq: (mu x < 1); by rewrite ?Hlt1 in Heq.
Qed.

Lemma condition_support {R : realType} {X : finType}
    (mu : fdist R X) (x : X) :
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

(** A canonical [fuzzy_space] structure on an arbitrary finite carrier,
    used solely to state EqJ-derivability facts about ICA terms: the
    metric plays no role in equational (as opposed to quantitative)
    derivations, so any witness relation works. *)
Definition ica_finite_space {R : realType} (X : finType) : fuzzy_space R.
Proof.
  refine {| fcarrier := X; frel := fun _ _ => 1 |}.
  by move => i j; rewrite ler01 lexx.
Defined.

Lemma ica_weight_val_inj {R : realType} (p q : ica_weight R) :
  ica_weight_val p = ica_weight_val q -> p = q.
Proof.
  case: p => r1 P1; case: q => r2 P2 /= Heq.
  subst r2.
  congr interval_inference.Itv.Def.
  apply: eq_irrelevance.
Qed.

Lemma app_ica_plus_eta {R : realType} {X : Type} (p : ica_weight R)
    (args : 'I_(ica_arity (ica_plus p)) -> term (@ica_signature R) X) :
  @App (@ica_signature R) X (ica_plus p) args = (args (inord 0)) <+ p +> (args (inord 1)).
Proof.
  rewrite /ica_op /=.
  congr App.
  apply: functional_extensionality => i.
  case: i => [[|[|m]] Hm] //=.
  - by have -> : Ordinal Hm = inord 0 by apply: ord_inj; rewrite inordK.
  - by have -> : Ordinal Hm = inord 1 by apply: ord_inj; rewrite inordK.
Qed.

Lemma convex_mixture_dirac_split {R : realType} {X : finType}
    (p : ica_weight R) (mu0 mu1 : fdist R X) (x0 : X) :
  convex_mixture (ica_probability_weight p) mu0 mu1 = dirac_fdist x0 ->
  mu0 = dirac_fdist x0 /\ mu1 = dirac_fdist x0.
Proof.
  move => H.
  have /andP [Hp0 Hp1] := ica_weight_open p.
  have Hpt : forall y, weighted_sum (ica_probability_weight p) (mu0 y) (mu1 y)
      = dirac_fdist x0 y.
    move => y.
    have := congr1 (fun f : fdist R X => fdist_val f y) H.
    by rewrite convex_mixtureE.
  split; apply: fdist_ext => y;
    have H0 := fdist_ge0 mu0 y; have H1 := fdist_ge0 mu1 y;
    have L0 := fdist_le1 mu0 y; have L1 := fdist_le1 mu1 y;
    move: (Hpt y);
    rewrite /weighted_sum /dirac_fdist ica_weightE //=;
    case: (eqVneq y x0) => [Heqxy | _ ] Heq; first (subst y); nra.
Qed.

(** Every term whose induced distribution is a Dirac at [x0] is provably
    (via idempotency, skew-commutativity and skew-associativity alone)
    equal to the variable term [Var x0]. This is the base case of
    barycentric normalization. *)
Lemma dirac_uniqueness {R : realType} {X : finType}
    (mode : frel_derivation_mode)
    (s : term (@ica_signature R) X) (x0 : X) :
  term_distribution s = dirac_fdist x0 ->
  @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
    (EqJ s (Var x0)).
Proof.
  elim: s x0 => [x | f args IH] x0 /=.
  - move => H.
    have Hx : (if x0 == x then 1 else 0) = (1 : R).
      have := congr1 (fun f : fdist R X => fdist_val f x0) H.
      by rewrite /dirac_fdist /= eqxx.
    case: eqP Hx => [-> _ | _ Hx]; first exact: FD_EqRefl.
    by exfalso; move: Hx; lra.
  - case: f args IH => p args IH /= H.
    have [H0 H1] := convex_mixture_dirac_split H.
    have D0 := IH (inord 0) x0 H0.
    have D1 := IH (inord 1) x0 H1.
    rewrite app_ica_plus_eta.
    apply: FD_EqTrans.
    - apply: (ica_plus_congr p D0 D1).
    - exact: ica_idem_instance.
Qed.

(** Merging two occurrences of the same point [u] nested inside a
    barycentric expression: [u +_p1 (u +_p2 w)] collapses, via a single
    application of skew-associativity followed by idempotency, to
    [u +_Q w] where [Q] is the total mass assigned to [u]. This is the
    key algebraic step used when a coupling assigns positive mass to a
    point from both branches of a binary mixture. *)
Lemma ica_merge_instance {R : realType} (mode : frel_derivation_mode)
    (X : fuzzy_space R) (p1 p2 : ica_weight R)
    (u w : term (@ica_signature R) (fcarrier X)) :
  @frel_derives R ica_signature (@ica_theory R) mode X
    (EqJ (u <+ p1 +> (u <+ p2 +> w))
         (u <+ (ica_weight_clamp
                  (ica_weight_val p1 + (1 - ica_weight_val p1) * ica_weight_val p2)) +> w)).
Proof.
  have /andP [H1a H1b] := ica_weight_open p1.
  have /andP [H2a H2b] := ica_weight_open p2.
  set Qr := ica_weight_val p1 + (1 - ica_weight_val p1) * ica_weight_val p2.
  have HQ : 0 < Qr < 1.
    apply/andP; split; rewrite /Qr; nra.
  set Pr := ica_weight_val p1 / Qr.
  have HQ0 : Qr != 0 by apply: lt0r_neq0; case/andP: HQ.
  have HP : 0 < Pr < 1.
    apply/andP; split; rewrite /Pr.
    - by apply: divr_gt0 => //; case/andP: HQ.
    - have HQpos : 0 < Qr by case/andP: HQ.
      rewrite ltr_pdivrMr // mul1r /Qr; nra.
  pose P := mk_ica_weight (elimT andP HP).1 (elimT andP HP).2.
  pose Qw := mk_ica_weight (elimT andP HQ).1 (elimT andP HQ).2.
  have EPr : ica_weight_val P = Pr by [].
  have EQr : ica_weight_val Qw = Qr by [].
  have Eprod : ica_weight_product P Qw = p1.
    apply: ica_weight_val_inj.
    rewrite ica_weight_productE EPr EQr /Pr.
    by field.
  have EprodR : Pr * Qr = ica_weight_val p1.
    by have := congr1 ica_weight_val Eprod; rewrite ica_weight_productE EPr EQr.
  have Hne1 : 1 - ica_weight_val p1 != 0 by apply: lt0r_neq0; rewrite subr_gt0.
  have Einner : ica_weight_assoc_inner P Qw = p2.
    apply: ica_weight_val_inj.
    rewrite ica_weight_assoc_innerE EPr EQr EprodR mulrBl EprodR mul1r.
    rewrite (_ : Qr - ica_weight_val p1 = (1 - ica_weight_val p1) * ica_weight_val p2).
    - by rewrite /Qr; ring.
    - rewrite (mulrC (1 - ica_weight_val p1) (ica_weight_val p2)).
      by rewrite (mulfK Hne1).
  have EQrClamp : Qw = ica_weight_clamp Qr.
    apply: ica_weight_val_inj.
    by rewrite EQr ica_weight_clampE //.
  apply: FD_EqTrans.
  - apply: FD_EqSym.
    rewrite -Eprod -Einner.
    apply: (ica_skew_assoc_instance mode P Qw u u w).
  - rewrite -EQrClamp.
    apply: ica_plus_congr; [exact: ica_idem_instance | exact: FD_EqRefl].
Qed.

(** The general two-sided merge: when both branches of a binary mixture
    have already had the same point [u] extracted, the whole expression
    collapses to a single occurrence of [u] together with a combined
    remainder. Built from one application of skew-associativity, one of
    skew-commutativity, a second application of skew-associativity, and
    finally [ica_merge_instance]. *)
Lemma general_merge {R : realType} (mode : frel_derivation_mode)
    (X : fuzzy_space R) (q0 p q1 : ica_weight R)
    (u w0 w1 : term (@ica_signature R) (fcarrier X)) :
  let r := ica_weight_assoc_inner q0 p in
  let q1c := ica_weight_product q1 (ica_weight_complement r) in
  let Pw := ica_weight_assoc_inner q1 (ica_weight_complement r) in
  let q0p := ica_weight_product q0 p in
  @frel_derives R ica_signature (@ica_theory R) mode X
    (EqJ ((u <+ q0 +> w0) <+ p +> (u <+ q1 +> w1))
         (u <+ (ica_weight_clamp
                  (ica_weight_val q0p + (1 - ica_weight_val q0p) * ica_weight_val q1c)) +>
           (w1 <+ Pw +> w0))).
Proof.
  move => r q1c Pw q0p.
  apply: FD_EqTrans.
  - apply: (ica_skew_assoc_instance mode q0 p u w0 (u <+ q1 +> w1)).
  - apply: FD_EqTrans.
    + apply: ica_plus_congr.
      * exact: FD_EqRefl.
      * exact: (ica_skew_comm_instance mode r w0 (u <+ q1 +> w1)).
    + apply: FD_EqTrans.
      * apply: ica_plus_congr.
        -- exact: FD_EqRefl.
        -- exact: (ica_skew_assoc_instance mode q1 (ica_weight_complement r) u w1 w0).
      * exact: (ica_merge_instance mode q0p q1c u (w1 <+ Pw +> w0)).
Qed.

(** A distribution carrying its full unit mass at a single point is that
    point's Dirac distribution. *)
Lemma fdist_mass1_dirac {R : realType} {X : finType} (mu : fdist R X) (x : X) :
  mu x = 1 -> mu = dirac_fdist x.
Proof.
  move => Hx.
  apply: fdist_ext => y.
  rewrite /dirac_fdist /=.
  case: eqP => [-> | Hne]; first exact: Hx.
  have Htot := fdist_1 mu.
  rewrite (bigD1 x) //= Hx in Htot.
  have Hrest : \sum_(i | i != x) mu i = 0 by lra.
  apply: (psumr_eq0P (fun i _ => fdist_ge0 mu i) Hrest).
  apply/eqP => Heq.
  exact: (Hne Heq).
Qed.

Lemma condition_recover {R : realType} {X : finType}
    (mu : fdist R X) (x : X) :
  (mu x < 1) ->
  x \in distribution_support mu ->
  convex_mixture (ica_probability_weight (ica_weight_clamp (mu x)))
    (dirac_fdist x) (condition mu x) = mu.
Proof.
  move => Hlt1 Hin.
  rewrite inE in Hin.
  have Hgt0 : (0 < mu x). {
    rewrite lt_neqAle.
    apply/andP; split.
    - rewrite eq_sym.
      apply: Hin.
    - apply: fdist_ge0.
  }
  have Hne0 : (1 - mu x != 0) by rewrite gt_eqF //= subr_gt0.
  apply: fdist_ext => y.
  rewrite convex_mixtureE /weighted_sum /dirac_fdist //= /cond_mass /weight ica_probability_weightE.
  rewrite ica_weight_clampE; first by apply/andP; split.
  case: ifP => [Heq | Hneq]; case: ifP => [Hlt1' | Hnlt1'].
  - move/eqP: Heq => {}Heq.
    by rewrite mulr1 mulr0 addr0 Heq.
  - by rewrite Hlt1 in Hnlt1'.
  - by rewrite mulr0 add0r mulrCA divff //= mulr1.
  - by rewrite Hlt1 in Hnlt1'.
Qed.

(** The barycentric extraction step: every point [x] in the support of a
    term's induced distribution can be "peeled off" via the ICA axioms,
    producing a witness weight and remainder term whose own distribution is
    exactly the conditional distribution [condition] after removing [x]'s
    mass. This is the induction underlying Proposition 4.10's completeness
    argument. *)
Lemma extract_exists {R : realType} {X : finType} (mode : frel_derivation_mode)
    (s : term (@ica_signature R) X) (x : X) :
  0 < term_distribution s x ->
  exists (q : ica_weight R) (w : term (@ica_signature R) X),
    @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
      (EqJ s (Var x <+ q +> w)) /\
    (term_distribution s x < 1 ->
       ica_weight_val q = term_distribution s x /\
       term_distribution w = condition (term_distribution s) x).
Proof.
  elim: s x => [x0 | f args IH] x Hpos.
  - move: Hpos; rewrite /term_distribution /dirac_fdist /= => Hpos.
    have Ex : x = x0 by case: eqP Hpos => [-> _ | _ ]; [| rewrite ltxx].
    exists (ica_weight_half R), (Var x0).
    split.
    + rewrite Ex.
      apply: FD_EqSym.
      exact: ica_idem_instance.
    + move => Hlt; exfalso; move: Hlt; rewrite Ex /dirac_fdist /= eqxx; lra.
  - move: Hpos; case: f args IH => p args IH /= Hpos.
    rewrite app_ica_plus_eta.
    set s0 := args (inord 0).
    set s1 := args (inord 1).
    rewrite -!weighted_sumE in Hpos *.
    set mu0 := term_distribution s0.
    set mu1 := term_distribution s1.
    set mu := convex_mixture (ica_probability_weight p) mu0 mu1.
    have Hle1 := fdist_le1 mu x.
    have Emux : mu x = weighted_sum (ica_probability_weight p) (mu0 x) (mu1 x)
      by rewrite /mu convex_mixtureE.
    case: (eqVneq (mu x) 1) => [Hmu1 | Hmune1].
    + have Hd : mu = dirac_fdist x := fdist_mass1_dirac Hmu1.
      have Ds : @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
          (EqJ (s0 <+ p +> s1) (Var x)).
        apply: (dirac_uniqueness mode).
        by rewrite term_distribution_op.
      exists (ica_weight_half R), (Var x).
      split.
      * apply: FD_EqTrans; first exact: Ds.
        apply: FD_EqSym.
        exact: ica_idem_instance.
      * rewrite -Emux Hmu1 => Hlt; exfalso; move: Hlt; lra.
    + have Hmult1 : mu x < 1 by rewrite lt_neqAle Hmune1 Hle1.
      have Hor : 0 < mu0 x \/ 0 < mu1 x.
        move: Hpos; rewrite weighted_sum_gt0; try exact: fdist_ge0.
        by move => /orP [H|H]; [left | right].
      have Hget1 : 0 < mu1 x ->
          exists q w, @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
              (EqJ s1 (Var x <+ q +> w)) /\
            (mu1 x = 1 -> w = Var x) /\
            (mu1 x < 1 -> ica_weight_val q = mu1 x /\ term_distribution w = condition mu1 x).
        move => Hpos1.
        case: (eqVneq (mu1 x) 1) => [H1 | Hn1].
        * have Ds1 : @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
              (EqJ s1 (Var x)).
            apply: (dirac_uniqueness mode).
            exact: (fdist_mass1_dirac H1).
          exists (ica_weight_half R), (Var x); split; [ | split].
          -- apply: FD_EqTrans; first exact: Ds1.
             apply: FD_EqSym.
             exact: ica_idem_instance.
          -- by [].
          -- move => Hlt; exfalso; rewrite H1 in Hlt; lra.
        * have Hlt1 : mu1 x < 1 by rewrite lt_neqAle Hn1 (fdist_le1 mu1 x).
          have [q [w [Dq Cq]]] := IH (inord 1) x Hpos1.
          exists q, w; split; [exact: Dq | split].
          -- by move => H1'; move: Hn1; rewrite H1' eqxx.
          -- exact: Cq.
      case: (eqVneq (mu0 x) 0) => [Hz0 | Hnz0].
      * have Hpos1 : 0 < mu1 x by case: Hor; rewrite ?Hz0 //; lra.
        case: (eqVneq (mu1 x) 1) => [H1 | Hn1].
        -- have Ds1 : @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
               (EqJ s1 (Var x)).
             apply: (dirac_uniqueness mode).
             exact: (fdist_mass1_dirac H1).
           exists (ica_weight_complement p), s0.
           split.
           ++ apply: FD_EqTrans.
              ** apply: ica_plus_congr; [exact: FD_EqRefl | exact: Ds1].
              ** exact: (@ica_skew_comm_instance R mode (ica_finite_space X) p s0 (Var x)).
           ++ move => _; split.
              ** by rewrite Hz0 H1 ica_weight_complementE /weighted_sum ica_weightE mulr0 add0r mulr1.
              ** apply: fdist_ext => y.
                 rewrite (conditionE y Hmult1).
                 have H1d := fdist_mass1_dirac H1.
                 case: eqP => [-> | Hne].
                 --- by rewrite Hz0.
                 --- have Heq : (y == x) = false by apply/eqP => Habs; exact: (Hne Habs).
                     have Hmuy : mu y = mu0 y * (1 - mu x).
                       rewrite /mu convex_mixtureE /weighted_sum H1d /dirac_fdist /= Heq mulr0 addr0.
                       rewrite eqxx -weighted_sumE Hz0 /weighted_sum ica_probability_weightE mulr0 add0r mulr1.
                       by rewrite mulrC opprB addrCA subrr addr0.
                     rewrite Hmuy mulfK //.
                     by rewrite lt0r_neq0 // subr_gt0.
        -- have [q1 [w1 [Dq1 Cq1]]] := Hget1 Hpos1.
           have Hmu1lt1 : mu1 x < 1 by rewrite lt_neqAle Hn1 (fdist_le1 mu1 x).
           have [Eq1 Ew1] := Cq1.2 Hmu1lt1.
           exists (ica_weight_product q1 (ica_weight_complement p)),
             (w1 <+ ica_weight_assoc_inner q1 (ica_weight_complement p) +> s0).
           split.
           ++ apply: FD_EqTrans.
              ** exact: (@ica_skew_comm_instance R mode (ica_finite_space X) p s0 s1).
              ** apply: FD_EqTrans.
                 --- apply: ica_plus_congr; [exact: Dq1 | exact: FD_EqRefl].
                 --- exact: (@ica_skew_assoc_instance R mode (ica_finite_space X) q1 (ica_weight_complement p) (Var x) w1 s0).
           ++ move => _; split.
              ** by rewrite ica_weight_productE ica_weight_complementE Eq1 Hz0 /weighted_sum ica_weightE; ring.
              ** apply: fdist_ext => y.
                 rewrite term_distribution_op convex_mixtureE (conditionE y Hmult1) Ew1.
                 have HD : (1 - mu x) = 1 - mu1 x * (1 - ica_weight_val p).
                   by rewrite Emux Hz0 /weighted_sum ica_weightE mulr0 add0r; ring.
                 have HbD : (1 - mu1 x) != 0 by rewrite subr_eq0 eq_sym.
                 have HD0 : (1 - mu x) != 0 by rewrite lt0r_neq0 // subr_gt0.
                 case: eqP => [-> | Hne].
                 --- rewrite (conditionE x Hmu1lt1) eqxx Hz0.
                     by rewrite /weighted_sum mulr0 mulr0 addr0.
                 --- rewrite (conditionE y Hmu1lt1) (negbTE (introN eqP Hne)).
                     rewrite /weighted_sum ica_weightE ica_weight_assoc_innerE ica_weight_complementE HD.
                     have HD' : (1 - mu1 x * (1 - ica_weight_val p)) != 0 by rewrite -HD.
                     rewrite /mu convex_mixtureE /weighted_sum ica_weightE.
                     have -> : term_distribution s0 y = mu0 y by [].
                     rewrite Eq1.
                     field.
                     +++ exact: HbD.
                     +++ exact: HD'.
      * have Hpos0 : 0 < mu0 x by rewrite lt0r Hnz0 fdist_ge0.
        have Hget0 : 0 < mu0 x ->
            exists q w, @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
                (EqJ s0 (Var x <+ q +> w)) /\
              (mu0 x = 1 -> w = Var x) /\
              (mu0 x < 1 -> ica_weight_val q = mu0 x /\ term_distribution w = condition mu0 x).
          move => Hp0.
          case: (eqVneq (mu0 x) 1) => [H1 | Hn1].
          -- have Ds0 : @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
                 (EqJ s0 (Var x)).
               apply: (dirac_uniqueness mode).
               exact: (fdist_mass1_dirac H1).
             exists (ica_weight_half R), (Var x); split; [ | split].
             ++ apply: FD_EqTrans; first exact: Ds0.
                apply: FD_EqSym.
                exact: ica_idem_instance.
             ++ by [].
             ++ move => Hlt; exfalso; rewrite H1 in Hlt; lra.
          -- have Hlt1 : mu0 x < 1 by rewrite lt_neqAle Hn1 (fdist_le1 mu0 x).
             have [q [w [Dq Cq]]] := IH (inord 0) x Hp0.
             exists q, w; split; [exact: Dq | split].
             ++ by move => H1'; move: Hn1; rewrite H1' eqxx.
             ++ exact: Cq.
        case: (eqVneq (mu1 x) 0) => [Hz1 | Hnz1].
        -- case: (eqVneq (mu0 x) 1) => [H1 | Hn1].
           ++ have Ds0 : @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
                  (EqJ s0 (Var x)).
                apply: (dirac_uniqueness mode).
                exact: (fdist_mass1_dirac H1).
              exists p, s1.
              split.
              ** apply: ica_plus_congr; [exact: Ds0 | exact: FD_EqRefl].
              ** move => _; split.
                 --- by rewrite Hz1 H1 /weighted_sum ica_weightE; ring.
                 --- apply: fdist_ext => y.
                     rewrite (conditionE y Hmult1).
                     have H1d := fdist_mass1_dirac H1.
                     case: eqP => [-> | Hne].
                     +++ by rewrite Hz1.
                     +++ have -> : mu y = mu1 y * (1 - mu x).
                           rewrite /mu convex_mixtureE /weighted_sum H1d /dirac_fdist /=.
                           have -> : (y == x) = false by apply/eqP => Habs; exact: (Hne Habs).
                           rewrite eqxx -weighted_sumE Hz1 /weighted_sum ica_weightE.
                           rewrite /ica_weight_val; ring.
                         by rewrite mulfK // lt0r_neq0 // subr_gt0.
           ++ have Hlt1 : mu0 x < 1 by rewrite lt_neqAle Hn1 (fdist_le1 mu0 x).
              have [q0 [w0 [Dq0 Cq0]]] := Hget0 Hpos0.
              have [Eq0 Ew0] := Cq0.2 Hlt1.
              exists (ica_weight_product q0 p), (w0 <+ ica_weight_assoc_inner q0 p +> s1).
              split.
              ** apply: FD_EqTrans.
                 --- apply: ica_plus_congr; [exact: Dq0 | exact: FD_EqRefl].
                 --- exact: (@ica_skew_assoc_instance R mode (ica_finite_space X) q0 p (Var x) w0 s1).
              ** move => _; split.
                 --- by rewrite ica_weight_productE Eq0 Hz1 /weighted_sum ica_weightE; ring.
                 --- apply: fdist_ext => y.
                     rewrite term_distribution_op convex_mixtureE (conditionE y Hmult1) Ew0.
                     have HD : (1 - mu x) = 1 - mu0 x * ica_weight_val p.
                       by rewrite Emux Hz1 /weighted_sum ica_weightE mulr0 addr0; ring.
                     case: eqP => [-> | Hne].
                     +++ rewrite (conditionE x Hlt1) eqxx.
                         by rewrite Hz1 /weighted_sum mulr0 mulr0 addr0.
                     +++ rewrite (conditionE y Hlt1) (negbTE (introN eqP Hne)).
                         rewrite /weighted_sum.
                         rewrite ica_weightE ica_weight_assoc_innerE HD.
                         have -> : term_distribution s1 y = mu1 y by [].
                         have HD' : (1 - mu0 x * ica_weight_val p) != 0 by rewrite -HD lt0r_neq0 // subr_gt0.
                         have Hb1' : (1 - mu0 x) != 0 by rewrite subr_eq0 eq_sym.
                         rewrite /mu convex_mixtureE /weighted_sum ica_weightE.
                         rewrite Eq0.
                         field.
                         *** exact: Hb1'.
                         *** exact: HD'.
        -- have Hpos1 : 0 < mu1 x by rewrite lt0r Hnz1 fdist_ge0.
           have [q0 [w0 [Dq0 Cq0]]] := Hget0 Hpos0.
           have [q1 [w1 [Dq1 Cq1]]] := Hget1 Hpos1.
           case: (eqVneq (mu0 x) 1) => [H10 | Hn10]; case: (eqVneq (mu1 x) 1) => [H11 | Hn11].
           ++ exfalso; move: Hmult1; rewrite Emux H10 H11 /weighted_sum ica_weightE; lra.
           ++ have Ew0x := Cq0.1 H10.
              rewrite Ew0x in Dq0.
              have Ds0 : @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
                  (EqJ s0 (Var x)).
                apply: FD_EqTrans; first exact: Dq0.
                exact: ica_idem_instance.
              exists (ica_weight_clamp (ica_weight_val p + (1 - ica_weight_val p) * ica_weight_val q1)), w1.
              split.
              ** apply: FD_EqTrans.
                 --- apply: ica_plus_congr; [exact: Ds0 | exact: Dq1].
                 --- exact: (@ica_merge_instance R mode (ica_finite_space X) p q1 (Var x) w1).
              ** move => _.
                 have Hlt11 : mu1 x < 1 by rewrite lt_neqAle Hn11 (fdist_le1 mu1 x).
                 have [Eq1 Ew1] := Cq1.2 Hlt11.
                 split.
                 --- rewrite ica_weight_clampE.
                     +++ apply/andP; split.
                         ---- have /andP [Hp0 Hp1] := ica_weight_open p.
                              have /andP [Hq10a Hq10b] := ica_weight_open q1.
                              nra.
                         ---- have /andP [Hp0 Hp1] := ica_weight_open p.
                              have /andP [Hq10a Hq10b] := ica_weight_open q1.
                              nra.
                     +++ by rewrite Eq1 H10 /weighted_sum ica_weightE; ring.
                 --- rewrite Ew1.
                     apply: fdist_ext => y.
                     rewrite (conditionE y Hlt11) (conditionE y Hmult1).
                     case: ifP => Heq; first by [].
                     have Hmu0y : mu0 y = 0.
                       have H0d := fdist_mass1_dirac H10.
                       by rewrite H0d /dirac_fdist /= Heq.
                     have -> : mu y = mu1 y * (1 - ica_weight_val p).
                       rewrite /mu convex_mixtureE /weighted_sum Hmu0y mulr0 add0r ica_weightE; ring.
                     have -> : (1 - mu x) = (1 - mu1 x) * (1 - ica_weight_val p).
                       rewrite Emux H10 /weighted_sum ica_weightE; ring.
                     rewrite mulrC -mulrA.
                     have HneP : (1 - ica_weight_val p) != 0.
                       have /andP [_ Hlp1] := ica_weight_open p.
                       by rewrite lt0r_neq0 // subr_gt0.
                     field.
                     +++ by rewrite subr_eq0 eq_sym.
                     +++ exact: HneP.
           ++ have Ew1x := Cq1.1 H11.
              rewrite Ew1x in Dq1.
              have Ds1 : @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
                  (EqJ s1 (Var x)).
                apply: FD_EqTrans; first exact: Dq1.
                exact: ica_idem_instance.
              have Hlt10 : mu0 x < 1 by rewrite lt_neqAle Hn10 (fdist_le1 mu0 x).
              have [Eq0 Ew0] := Cq0.2 Hlt10.
              exists (ica_weight_clamp (ica_weight_val (ica_weight_complement p) + (1 - ica_weight_val (ica_weight_complement p)) * ica_weight_val q0)), w0.
              split.
              ** apply: FD_EqTrans.
                 --- exact: (@ica_skew_comm_instance R mode (ica_finite_space X) p s0 s1).
                 --- apply: FD_EqTrans.
                     +++ apply: ica_plus_congr; [exact: Ds1 | exact: Dq0].
                     +++ exact: (@ica_merge_instance R mode (ica_finite_space X) (ica_weight_complement p) q0 (Var x) w0).
              ** move => _; split.
                 --- rewrite ica_weight_clampE.
                     +++ apply/andP; split.
                         ---- rewrite ica_weight_complementE.
                              have Hq0 := ica_weight_open q0.
                              have /andP [Hp0 Hp1] := ica_weight_open p.
                              nra.
                         ---- rewrite ica_weight_complementE.
                              have Hq0 := ica_weight_open q0.
                              have /andP [Hp0 Hp1] := ica_weight_open p.
                              nra.
                     +++ by rewrite Eq0 ica_weight_complementE H11 /weighted_sum ica_weightE; ring.
                 --- rewrite Ew0.
                     apply: fdist_ext => y.
                     rewrite (conditionE y Hlt10) (conditionE y Hmult1).
                     case: ifP => Heq; first by [].
                     have Hmu1y : mu1 y = 0.
                       have H1d := fdist_mass1_dirac H11.
                       by rewrite H1d /dirac_fdist /= Heq.
                     have -> : mu y = mu0 y * ica_weight_val p.
                       rewrite /mu convex_mixtureE /weighted_sum Hmu1y mulr0 addr0 ica_weightE; ring.
                     have -> : (1 - mu x) = (1 - mu0 x) * ica_weight_val p.
                       rewrite Emux H11 /weighted_sum ica_weightE; ring.
                     have HneP0 : ica_weight_val p != 0.
                       have /andP [Hlp0 _] := ica_weight_open p.
                       by rewrite lt0r_neq0.
                     field.
                     +++ by rewrite subr_eq0 eq_sym.
                     +++ exact: HneP0.
           ++ have Hlt10 : mu0 x < 1 by rewrite lt_neqAle Hn10 (fdist_le1 mu0 x).
              have Hlt11 : mu1 x < 1 by rewrite lt_neqAle Hn11 (fdist_le1 mu1 x).
              have [Eq0 Ew0] := Cq0.2 Hlt10.
              have [Eq1 Ew1] := Cq1.2 Hlt11.
              pose r := ica_weight_assoc_inner q0 p.
              pose q1c := ica_weight_product q1 (ica_weight_complement r).
              pose Pw := ica_weight_assoc_inner q1 (ica_weight_complement r).
              pose q0p := ica_weight_product q0 p.
              exists (ica_weight_clamp (ica_weight_val q0p + (1 - ica_weight_val q0p) * ica_weight_val q1c)),
                (w1 <+ Pw +> w0).
              split.
              ** apply: FD_EqTrans.
                 --- apply: ica_plus_congr; [exact: Dq0 | exact: Dq1].
                 --- exact: (@general_merge R mode (ica_finite_space X) q0 p q1 (Var x) w0 w1).
              ** move => _.
                 have /andP [Hp0 Hp1] := ica_weight_open p.
                 have /andP [Hq00 Hq01] := ica_weight_open q0.
                 have Hr1 : 0 <= ica_weight_val q0 * ica_weight_val p < 1 by nra.
                 have HDr : (1 - ica_weight_val q0 * ica_weight_val p) != 0.
                   by rewrite lt0r_neq0 // subr_gt0; case/andP: Hr1.
                 have Erval : ica_weight_val r = (1 - ica_weight_val q0) * ica_weight_val p / (1 - ica_weight_val q0 * ica_weight_val p).
                   by rewrite /r ica_weight_assoc_innerE.
                 have Ecomprval : ica_weight_val (ica_weight_complement r) = 1 - ica_weight_val r.
                   by rewrite ica_weight_complementE.
                 have Eq0pval : ica_weight_val q0p = ica_weight_val q0 * ica_weight_val p.
                   by rewrite /q0p ica_weight_productE.
                 have Eq1cval : ica_weight_val q1c = ica_weight_val q1 * ica_weight_val (ica_weight_complement r).
                   by rewrite /q1c ica_weight_productE.
                 have EQval : ica_weight_val q0p + (1 - ica_weight_val q0p) * ica_weight_val q1c
                     = weighted_sum (ica_probability_weight p) (mu0 x) (mu1 x).
                   rewrite Eq0pval Eq1cval Ecomprval Erval Eq0 Eq1 /weighted_sum ica_weightE.
                   field.
                   by rewrite -Eq0.
                 split.
                 --- rewrite ica_weight_clampE.
                     +++ apply/andP; split.
                         ---- rewrite EQval; exact: Hpos.
                         ---- rewrite EQval -Emux; exact: Hmult1.
                     +++ exact: EQval.
                 --- apply: fdist_ext => y.
                     rewrite term_distribution_op convex_mixtureE (conditionE y Hmult1) Ew1 Ew0.
                     have HDmu : (1 - mu x) != 0 by rewrite lt0r_neq0 // subr_gt0.
                     have HDb1 : (1 - mu1 x) != 0 by rewrite subr_eq0 eq_sym.
                     have HDb0 : (1 - mu0 x) != 0 by rewrite subr_eq0 eq_sym.
                     case: ifP => Heq.
                     +++ move/eqP: Heq => Heq; subst y.
                         rewrite (conditionE x Hlt11) (conditionE x Hlt10) eqxx.
                         by rewrite /weighted_sum mulr0 mulr0 addr0.
                     +++ rewrite (conditionE y Hlt11) (conditionE y Hlt10) Heq.
                         rewrite /weighted_sum ica_weightE /Pw ica_weight_assoc_innerE Ecomprval Erval Eq0 Eq1.
                         have Hmuy : mu y = ica_weight_val p * mu0 y + (1 - ica_weight_val p) * mu1 y.
                           by rewrite /mu convex_mixtureE /weighted_sum ica_weightE.
                         rewrite Hmuy Emux /weighted_sum ica_weightE.
                         have HD3 : (1 - mu0 x * ica_weight_val p) != 0 by rewrite -Eq0.
                         have HD4 : (1 - (ica_weight_val p * mu0 x + (1 - ica_weight_val p) * mu1 x)) != 0.
                           have -> : ica_weight_val p * mu0 x + (1 - ica_weight_val p) * mu1 x
                               = mu x.
                             by rewrite Emux /weighted_sum ica_weightE.
                           exact: HDmu.
                         have HD5eq : 1 - mu1 x * (1 - (1 - mu0 x) * ica_weight_val p / (1 - mu0 x * ica_weight_val p))
                             = (1 - mu x) / (1 - mu0 x * ica_weight_val p).
                           rewrite Emux /weighted_sum ica_weightE.
                           field.
                           exact: HD3.
                         have HD5 : (1 - mu1 x * (1 - (1 - mu0 x) * ica_weight_val p / (1 - mu0 x * ica_weight_val p))) != 0.
                           rewrite HD5eq.
                           by apply: mulf_neq0; [exact: HDmu | rewrite invr_neq0].
                         field.
                         ---- exact: HDb1.
                         ---- exact: HD3.
                         ---- exact: HDb0.
                         ---- exact: HD4.
Qed.

Definition ica_dirac_interp {R : realType} {X : finType}
    (d : X -> X -> R) (Hd : forall x y, (0 <= d x y <= 1)%R) :
    interpretation (ica_finite_space X) (kantorovich_algebra Hd) :=
  @Build_interpretation R (@ica_signature R) (ica_finite_space X)
    (kantorovich_algebra Hd)
    (fun x => dirac_fdist x)
    (fun x y => kantorovich_lifting_le1 (dirac_fdist x) (dirac_fdist y) Hd).

Theorem term_distribution_eq_sound {R : realType} {X : finType}
    (mode : frel_derivation_mode) (s t : term (@ica_signature R) X) :
  @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
    (EqJ s t) ->
  term_distribution s = term_distribution t.
Proof.
  pose d : X -> X -> R := fun _ _ => 0.
  have Hd : forall x y : X, (0 <= d x y <= 1)%R.
    by move => x y; apply/andP; split; [exact: lexx | exact: ler01].
  have E : forall u : term (@ica_signature R) X,
      fuzzy_eval (kantorovich_algebra Hd) (ica_dirac_interp Hd) u =
      term_distribution u.
    move => u.
    by rewrite -(term_distributionE Hd u).
  case: mode.
  - move => H.
    have Hsat := derives_fin_sound (@kantorovich_models_ica R X d Hd) H
      (ica_dirac_interp Hd).
    move: Hsat => /=.
    by rewrite -(E s) -(E t).
  - move => H.
    have Hsat := derives_full_sound (@kantorovich_models_ica R X d Hd) H
      (ica_dirac_interp Hd).
    move: Hsat => /=.
    by rewrite -(E s) -(E t).
Qed.

Lemma term_distribution_complete_bound {R : realType} {X : finType} :
  forall n (s t : term (@ica_signature R) X),
    (#|distribution_support (term_distribution s)| <= n)%N ->
    term_distribution s = term_distribution t ->
    @frel_derives R ica_signature (@ica_theory R) FRelFinite
      (ica_finite_space X) (EqJ s t).
Proof.
  elim => [ | n IH] s t Hn Heq.
  - exfalso.
    have Hne := term_distribution_support_neq0 s.
    case/set0Pn: Hne => x0 Hx0.
    move: Hn; rewrite leqn0 => /eqP Hn0.
    have HA0 : distribution_support (term_distribution s) == finset.set0.
      by rewrite -cards_eq0 Hn0.
    move/eqP: HA0 => HA0.
    move: Hx0; rewrite HA0 inE.
    done.
  - have Hne := term_distribution_support_neq0 s.
    case/set0Pn: Hne => x Hxin.
    have Hx : term_distribution s x != 0 by move: Hxin; rewrite inE.
    have Hpos : 0 < term_distribution s x by rewrite lt0r Hx fdist_ge0.
    have Heqx : term_distribution s x = term_distribution t x by rewrite Heq.
    case: (eqVneq (term_distribution s x) 1) => [Hx1 | Hxn1].
    + have Hds : term_distribution s = dirac_fdist x := fdist_mass1_dirac Hx1.
      have Hdt : term_distribution t = dirac_fdist x by rewrite -Heq.
      apply: FD_EqTrans.
      * exact: (dirac_uniqueness FRelFinite Hds).
      * apply: FD_EqSym.
        exact: (dirac_uniqueness FRelFinite Hdt).
    + have Hxlt1 : term_distribution s x < 1
        by rewrite lt_neqAle Hxn1 (fdist_le1 (term_distribution s) x).
      have Hpos' : 0 < term_distribution t x by rewrite -Heqx.
      have Hxlt1' : term_distribution t x < 1 by rewrite -Heqx.
      have [qs [ws [Ds Cs]]] := extract_exists FRelFinite Hpos.
      have [qt [wt [Dt Ct]]] := extract_exists FRelFinite Hpos'.
      have [Eqs Ews] := Cs Hxlt1.
      have [Eqt Ewt] := Ct Hxlt1'.
      have Eq : qs = qt.
        apply: ica_weight_val_inj.
        by rewrite Eqs Heqx -Eqt.
      have Ew : term_distribution ws = term_distribution wt.
        by rewrite Ews Ewt Heq.
      have Hcard := cardsD1 x (distribution_support (term_distribution s)).
      rewrite Hxin add1n in Hcard.
      have Hbound : (#|distribution_support (term_distribution s) :\ x| <= n)%N.
        by rewrite Hcard ltnS in Hn.
      have Hbound' : (#|distribution_support (term_distribution ws)| <= n)%N.
        by rewrite Ews (condition_support Hxlt1 Hxin).
      have IHws := IH ws wt Hbound' Ew.
      rewrite -Eq in Dt.
      apply: FD_EqTrans; first exact: Ds.
      apply: FD_EqTrans.
      * apply: ica_plus_congr; [exact: FD_EqRefl | exact: IHws].
      * exact: FD_EqSym Dt.
Qed.

Theorem term_distribution_complete {R : realType} {X : finType}
    (s t : term (@ica_signature R) X) :
  term_distribution s = term_distribution t ->
  @frel_derives R ica_signature (@ica_theory R) FRelFinite
    (ica_finite_space X) (EqJ s t).
Proof.
  exact: term_distribution_complete_bound
    (#|distribution_support (term_distribution s)|) s t (leqnn _).
Qed.

Theorem term_distribution_correctness {R : realType} {X : finType}
    (mode : frel_derivation_mode) (s t : term (@ica_signature R) X) :
  term_distribution s = term_distribution t <->
  @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
    (EqJ s t).
Proof.
  split.
  - move => Heq.
    have Hfin := term_distribution_complete Heq.
    case: mode.
    + exact: Hfin.
    + exact: derives_fin_to_full Hfin.
  - exact: term_distribution_eq_sound.
Qed.

(** Every [fdist]'s support is nonempty: an empty support would force the
    total mass to sum to [0], contradicting [fdist_1]. *)
Lemma fdist_support_neq0 {R : realType} {X : finType} (mu : fdist R X) :
  distribution_support mu != finset.set0.
Proof.
  apply/negP => /eqP H0.
  have Hall : forall x : X, mu x = 0.
    move => x.
    have Hnotin : x \notin distribution_support mu by rewrite H0 inE.
    apply/eqP; move: Hnotin; rewrite inE negbK; done.
  have Hsum0 : \sum_(x : X) mu x = 0 by apply: big1 => x _; exact: Hall x.
  have Htot := fdist_1 mu.
  rewrite Hsum0 in Htot.
  have H01 : (1:R) != 0 := oner_neq0 R.
  move: H01.
  by rewrite -Htot eqxx.
Qed.

(** [set0Pn]'s first argument is the set itself (not the disequality proof),
    so it must be supplied explicitly to extract a witness; this packages
    that once for reuse in [term_of_fdist_bound]. *)
Definition fdist_support_witness {R : realType} {X : finType}
    (mu : fdist R X) : exists x : X, x \in distribution_support mu :=
  set0Pn (distribution_support mu) (fdist_support_neq0 mu).

Fixpoint term_of_fdist_bound {R : realType} {X : finType}
    (n : nat) (mu : fdist R X) : term (@ica_signature R) X :=
  let x := xchoose (fdist_support_witness mu) in
  if mu x == 1 then Var x
  else match n with
       | 0 => Var x
       | n'.+1 =>
           Var x <+ (ica_weight_clamp (mu x)) +>
             term_of_fdist_bound n' (condition mu x)
       end.

Lemma term_of_fdist_bound_correct {R : realType} {X : finType} :
  forall n (mu : fdist R X),
    (#|distribution_support mu| <= n)%N ->
    term_distribution (term_of_fdist_bound n mu) = mu.
Proof.
  elim => [ | n IH] mu Hn.
  - exfalso.
    have Hne := fdist_support_neq0 mu.
    case/set0Pn: Hne => x0 Hx0.
    move: Hn; rewrite leqn0 => /eqP Hn0.
    have HA0 : distribution_support mu == finset.set0 by rewrite -cards_eq0 Hn0.
    move/eqP: HA0 => HA0.
    move: Hx0; rewrite HA0 inE.
    done.
  - rewrite /term_of_fdist_bound /=.
    have Hxin0 : xchoose (fdist_support_witness mu) \in distribution_support mu :=
      xchooseP (fdist_support_witness mu).
    set x := xchoose (fdist_support_witness mu).
    case: eqP => [Hx1 | Hxn1].
    + by rewrite (fdist_mass1_dirac Hx1).
    + have Hxlt1 : mu x < 1.
        rewrite lt_neqAle (fdist_le1 mu x) andbT.
        apply/negP => /eqP Habs.
        exact: Hxn1 Habs.
      rewrite term_distribution_op /=.
      have Hcard := cardsD1 x (distribution_support mu).
      rewrite Hxin0 add1n in Hcard.
      have Hbound : (#|distribution_support mu :\ x| <= n)%N.
        by rewrite Hcard ltnS in Hn.
      have Hbound' : (#|distribution_support (condition mu x)| <= n)%N.
        by rewrite (condition_support Hxlt1 Hxin0).
      rewrite (IH (condition mu x) Hbound').
      exact: condition_recover Hxlt1 Hxin0.
Qed.

Definition term_of_fdist {R : realType} {X : finType}
    (mu : fdist R X) : term (@ica_signature R) X :=
  term_of_fdist_bound #|distribution_support mu| mu.

Theorem term_of_fdist_correct {R : realType} {X : finType}
    (mu : fdist R X) :
  term_distribution (term_of_fdist mu) = mu.
Proof.
  exact: term_of_fdist_bound_correct #|distribution_support mu| mu (leqnn _).
Qed.

Theorem term_of_fdist_derives {R : realType} {X : finType}
    (mode : frel_derivation_mode) (s : term (@ica_signature R) X) :
  @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
    (EqJ s (term_of_fdist (term_distribution s))).
Proof.
  apply/term_distribution_correctness.
  by rewrite term_of_fdist_correct.
Qed.

(** [dist_map f mu]: the pushforward of [mu] along [f], i.e. the distribution
    that assigns to [x] the total [mu]-mass of [f]'s fiber over [x]. Used
    (M3) to relate a coupling's joint distribution, viewed as an [fdist] on
    a product type, to its two marginals. *)
Definition dist_map {R : realType} {Y X : finType}
    (f : Y -> X) (mu : fdist R Y) : fdist R X.
Proof.
  refine {| fdist_val := fun x => \sum_(y : Y | f y == x) mu y;
            fdist_ge0 := _;
            fdist_1 := _ |}.
  - move => x; apply: sumr_ge0 => y _; exact: fdist_ge0.
  - rewrite -(fdist_1 mu) (partition_big f xpredT) //=.
Defined.

Lemma dist_mapE {R : realType} {Y X : finType}
    (f : Y -> X) (mu : fdist R Y) (x : X) :
  dist_map f mu x = \sum_(y : Y | f y == x) mu y.
Proof. by []. Qed.

Lemma dist_map_dirac {R : realType} {Y X : finType}
    (f : Y -> X) (y0 : Y) :
  dist_map f (@dirac_fdist R Y y0) = dirac_fdist (f y0).
Proof.
  apply: fdist_ext => x.
  rewrite dist_mapE /dirac_fdist /=.
  case: eqP => [-> | Hne].
  - rewrite (bigD1 y0) //= eqxx big1 ?addr0 //.
    move => y' /andP [_ Hy']; by rewrite (negbTE Hy').
  - apply: big1 => y /eqP Hfy.
    case: eqP => [Hy0 | //].
    exfalso; apply: Hne; by rewrite -Hfy Hy0.
Qed.

Lemma dist_map_convex_mixture {R : realType} {Y X : finType}
    (f : Y -> X) (p : probability_weight R) (mu nu : fdist R Y) :
  dist_map f (convex_mixture p mu nu) =
  convex_mixture p (dist_map f mu) (dist_map f nu).
Proof.
  apply: fdist_ext => x.
  rewrite convex_mixtureE !dist_mapE.
  under eq_bigr => y _ do rewrite convex_mixtureE.
  rewrite /weighted_sum big_split -!big_distrr //=.
Qed.

(** Pushing a term's induced distribution forward along [f] is the same as
    substituting [Var \o f] into the term and taking the distribution of the
    result: renaming variables and interpreting commute. *)
Lemma term_distribution_subst_var {R : realType} {Y X : finType}
    (f : Y -> X) (e : term (@ica_signature R) Y) :
  term_distribution (subst_term (Var \o f) e) = dist_map f (term_distribution e).
Proof.
  elim: e => [y | ff args IH] /=.
  - by rewrite dist_map_dirac.
  - case: ff args IH => p args IH /=.
    by rewrite (IH (inord 0)) (IH (inord 1)) dist_map_convex_mixture.
Qed.

(** The joint distribution underlying a coupling, viewed as an [fdist] over
    the product finType [X * Y] rather than the curried [joint_fdist]. *)
Definition fdist_of_coupling {R : realType} {X Y : finType}
    {mu : fdist R X} {nu : fdist R Y} (gamma : coupling mu nu) :
    fdist R (X * Y)%type.
Proof.
  refine {| fdist_val := fun p => gamma p.1 p.2;
            fdist_ge0 := _;
            fdist_1 := _ |}.
  - move => p; exact: joint_ge0.
  - by rewrite -pair_bigA; exact: joint_1.
Defined.

Lemma dist_map_fst_coupling {R : realType} {X Y : finType}
    {mu : fdist R X} {nu : fdist R Y} (gamma : coupling mu nu) :
  dist_map fst (fdist_of_coupling gamma) = mu.
Proof.
  apply: fdist_ext => x.
  rewrite dist_mapE /=.
  have Hk : forall p : X * Y, p.1 == x -> (x, p.2) = p.
    move => [x' y'] /= /eqP ->; reflexivity.
  rewrite (reindex_onto (fun y : Y => (x, y)) snd Hk) /=.
  rewrite -(coupling_fst gamma x).
  apply: eq_bigl => y; by rewrite !eqxx.
Qed.

Lemma dist_map_snd_coupling {R : realType} {X Y : finType}
    {mu : fdist R X} {nu : fdist R Y} (gamma : coupling mu nu) :
  dist_map snd (fdist_of_coupling gamma) = nu.
Proof.
  apply: fdist_ext => y.
  rewrite dist_mapE /=.
  have Hk : forall p : X * Y, p.2 == y -> (p.1, y) = p.
    move => [x' y'] /= /eqP ->; reflexivity.
  rewrite (reindex_onto (fun x : X => (x, y)) fst Hk) /=.
  rewrite -(coupling_snd gamma y).
  apply: eq_bigl => x; by rewrite !eqxx.
Qed.

Definition ica_coupling_term {R : realType} {X : finType}
    (s t : term (@ica_signature R) X)
    (gamma : coupling (term_distribution s) (term_distribution t)) :
    term (@ica_signature R) (X * X)%type :=
  term_of_fdist (fdist_of_coupling gamma).

Theorem ica_coupling_term_fst {R : realType} {X : finType}
    (mode : frel_derivation_mode)
    (s t : term (@ica_signature R) X)
    (gamma : coupling (term_distribution s) (term_distribution t)) :
  @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
    (EqJ (subst_term (Var \o fst) (ica_coupling_term gamma)) s).
Proof.
  apply/term_distribution_correctness.
  rewrite term_distribution_subst_var /ica_coupling_term term_of_fdist_correct.
  exact: dist_map_fst_coupling.
Qed.

Theorem ica_coupling_term_snd {R : realType} {X : finType}
    (mode : frel_derivation_mode)
    (s t : term (@ica_signature R) X)
    (gamma : coupling (term_distribution s) (term_distribution t)) :
  @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
    (EqJ (subst_term (Var \o snd) (ica_coupling_term gamma)) t).
Proof.
  apply/term_distribution_correctness.
  rewrite term_distribution_subst_var /ica_coupling_term term_of_fdist_correct.
  exact: dist_map_snd_coupling.
Qed.

Definition joint_cost {R : realType} {X : finType}
    (d : X -> X -> R) (mu : fdist R (X * X)%type) : R :=
  \sum_(p : X * X) mu p * d p.1 p.2.

Lemma joint_cost_coupling {R : realType} {X : finType}
    (d : X -> X -> R) {mu nu : fdist R X} (gamma : coupling mu nu) :
  joint_cost d (fdist_of_coupling gamma) = coupling_cost d gamma.
Proof.
  rewrite /joint_cost /coupling_cost /=.
  rewrite pair_bigA.
  by [].
Qed.

Lemma joint_cost_range {R : realType} {X : finType}
    (d : X -> X -> R) (Hd : forall x y, (0 <= d x y <= 1)%R)
    (mu : fdist R (X * X)%type) :
  (0 <= joint_cost d mu <= 1)%R.
Proof.
  apply/andP; split.
  - rewrite /joint_cost; apply: sumr_ge0 => p _.
    apply: mulr_ge0; [exact: fdist_ge0 | by case/andP: (Hd p.1 p.2)].
  - rewrite /joint_cost.
    apply: (le_trans (y := \sum_(p : X*X) mu p * 1)).
    + apply: ler_sum => p _.
      apply: ler_wpM2l; [exact: fdist_ge0 | by case/andP: (Hd p.1 p.2)].
    + under eq_bigr => p _ do rewrite mulr1.
      by rewrite fdist_1.
Qed.

Lemma joint_cost_condition {R : realType} {X : finType}
    (d : X -> X -> R) (mu : fdist R (X * X)%type) (x : X * X) :
  (mu x < 1)%R -> x \in distribution_support mu ->
  joint_cost d mu =
  weighted_sum (ica_probability_weight (ica_weight_clamp (mu x)))
    (d x.1 x.2) (joint_cost d (condition mu x)).
Proof.
  move => Hlt1 Hin.
  have Hxne0 : mu x != 0 by move: Hin; rewrite inE.
  have Hxgt0 : 0 < mu x by rewrite lt0r Hxne0 fdist_ge0.
  have HqE : ica_weight_val (ica_weight_clamp (mu x)) = mu x.
    apply: ica_weight_clampE.
    by apply/andP; split.
  have Hne0 : (1 - mu x != 0) by rewrite gt_eqF //= subr_gt0.
  rewrite /weighted_sum ica_weightE HqE.
  rewrite /joint_cost.
  rewrite [X in X = _](bigD1 x) //=.
  congr (_ + _).
  rewrite [X in _ = _ * X](bigD1 x) //=.
  rewrite /cond_mass Hlt1 eqxx mul0r add0r.
  rewrite big_distrr /=.
  apply: eq_bigr => p Hp.
  rewrite (negbTE Hp).
  rewrite mulrA mulrCA divff // mulr1.
  reflexivity.
Qed.

Lemma ica_interp_instance {R : realType} (mode : frel_derivation_mode)
    (X : fuzzy_space R) (p : ica_weight R) (eps delta : R)
    (Heps : (0 <= eps <= 1)%R) (Hdelta : (0 <= delta <= 1)%R)
    (a b c e : term (@ica_signature R) (fcarrier X)) :
  @frel_derives R ica_signature (@ica_theory R) mode X (QEqJ eps a b) ->
  @frel_derives R ica_signature (@ica_theory R) mode X (QEqJ delta c e) ->
  @frel_derives R ica_signature (@ica_theory R) mode X
    (QEqJ (weighted_sum (ica_probability_weight p) eps delta)
      (a <+ p +> c) (b <+ p +> e)).
Proof.
  move => Hab Hce.
  pose sigma := fun i : 'I_4 =>
    match (i : nat) with
    | 0 => a
    | 1 => c
    | 2 => b
    | 3 => e
    | _ => a
    end.
  have E0 : sigma (inord 0) = a by rewrite /sigma inordK.
  have E1 : sigma (inord 1) = c by rewrite /sigma inordK.
  have E2 : sigma (inord 2) = b by rewrite /sigma inordK.
  have E3 : sigma (inord 3) = e by rewrite /sigma inordK.
  have -> : (a <+ p +> c) = subst_term sigma ((Var (inord 0)) <+ p +> (Var (inord 1))).
    by rewrite ica_subst_op /= E0 E1.
  have -> : (b <+ p +> e) = subst_term sigma ((Var (inord 2)) <+ p +> (Var (inord 3))).
    by rewrite ica_subst_op /= E2 E3.
  apply: (FD_Subst
    (X := ica_interp_space Heps Hdelta)
    (phi := QEqJ (weighted_sum (ica_probability_weight p) eps delta)
      ((Var (inord 0)) <+ p +> (Var (inord 1)))
      ((Var (inord 2)) <+ p +> (Var (inord 3))))
    (sigma := sigma)).
  - apply: FD_Init.
    exact: (ICA_Interp p Heps Hdelta).
  - move => x y.
    rewrite /= /ica_interp_rel /sigma.
    case: (nat_of_ord x) => [ | [ | x' ] ];
    case: (nat_of_ord y) => [ | [ | [ | [ | y' ] ] ] ] => //=;
    try exact: FD_Max.
Qed.

Lemma term_of_fdist_bound_QEqJ {R : realType} {X : finType}
    (d : X -> X -> R) (Hd : forall x y, (0 <= d x y <= 1)%R) :
  forall n (mu : fdist R (X * X)%type),
    (#|distribution_support mu| <= n)%N ->
    @frel_derives R ica_signature (@ica_theory R) FRelFinite
      (finite_fuzzy_space Hd)
      (QEqJ (joint_cost d mu)
        (subst_term (Var \o fst) (term_of_fdist_bound n mu))
        (subst_term (Var \o snd) (term_of_fdist_bound n mu))).
Proof.
  elim => [ | n IH] mu Hn.
  - exfalso.
    have Hne := fdist_support_neq0 mu.
    case/set0Pn: Hne => x0 Hx0.
    move: Hn; rewrite leqn0 => /eqP Hn0.
    have HA0 : distribution_support mu == finset.set0 by rewrite -cards_eq0 Hn0.
    move/eqP: HA0 => HA0.
    move: Hx0; rewrite HA0 inE.
    done.
  - rewrite /term_of_fdist_bound -/term_of_fdist_bound.
    have Hxin0 : xchoose (fdist_support_witness mu) \in distribution_support mu :=
      xchooseP (fdist_support_witness mu).
    set x := xchoose (fdist_support_witness mu).
    case: eqP => [Hx1 | Hxn1].
    + have Hdirac : mu = dirac_fdist x := fdist_mass1_dirac Hx1.
      have Hcost : joint_cost d mu = d x.1 x.2.
        rewrite /joint_cost Hdirac (bigD1 x) //= eqxx mul1r big1 ?addr0 //.
        move => y /negbTE Hy.
        by rewrite /dirac_fdist /= Hy mul0r.
      rewrite Hcost /=.
      exact: (@FD_UseVariables R ica_signature (@ica_theory R) FRelFinite
        (finite_fuzzy_space Hd) x.1 x.2).
    + have Hxlt1 : mu x < 1.
        rewrite lt_neqAle (fdist_le1 mu x) andbT.
        apply/negP => /eqP Habs.
        exact: Hxn1 Habs.
      have Hcard := cardsD1 x (distribution_support mu).
      rewrite Hxin0 add1n in Hcard.
      have Hbound : (#|distribution_support mu :\ x| <= n)%N.
        by rewrite Hcard ltnS in Hn.
      have Hbound' : (#|distribution_support (condition mu x)| <= n)%N.
        by rewrite (condition_support Hxlt1 Hxin0).
      have IHw := IH (condition mu x) Hbound'.
      set w := term_of_fdist_bound n (condition mu x).
      have Heps : (0 <= d x.1 x.2 <= 1)%R := Hd x.1 x.2.
      have Hdelta : (0 <= joint_cost d (condition mu x) <= 1)%R :=
        joint_cost_range Hd (condition mu x).
      rewrite (ica_subst_op (Var \o fst)) (ica_subst_op (Var \o snd)).
      rewrite (joint_cost_condition d Hxlt1 Hxin0).
      rewrite /=.
      exact: (ica_interp_instance (ica_weight_clamp (mu x)) Heps Hdelta
        (@FD_UseVariables R ica_signature (@ica_theory R) FRelFinite
          (finite_fuzzy_space Hd) x.1 x.2)
        IHw).
Qed.

Theorem ica_coupling_term_QEqJ {R : realType} {X : finType}
    (d : X -> X -> R) (Hd : forall x y, (0 <= d x y <= 1)%R)
    (s t : term (@ica_signature R) X)
    (gamma : coupling (term_distribution s) (term_distribution t)) :
  @frel_derives R ica_signature (@ica_theory R) FRelFinite
    (finite_fuzzy_space Hd)
    (QEqJ (coupling_cost d gamma)
      (subst_term (Var \o fst) (ica_coupling_term gamma))
      (subst_term (Var \o snd) (ica_coupling_term gamma))).
Proof.
  rewrite -(joint_cost_coupling d gamma).
  rewrite /ica_coupling_term /term_of_fdist.
  exact: (term_of_fdist_bound_QEqJ Hd (leqnn #|distribution_support (fdist_of_coupling gamma)|)).
Qed.

Lemma ica_finite_eqj_reambient {R : realType} {X : finType}
    (d : X -> X -> R) (Hd : forall x y, (0 <= d x y <= 1)%R)
    (mode : frel_derivation_mode) (s t : term (@ica_signature R) X) :
  @frel_derives R ica_signature (@ica_theory R) mode (ica_finite_space X)
    (EqJ s t) ->
  @frel_derives R ica_signature (@ica_theory R) mode (finite_fuzzy_space Hd)
    (EqJ s t).
Proof.
  move => H.
  have H' : @frel_derives R ica_signature (@ica_theory R) mode
      (finite_fuzzy_space Hd)
      (subst_judgement (@Var (@ica_signature R) X) (EqJ s t)).
    apply: (FD_Subst (X := ica_finite_space X)).
    - exact: H.
    - move => x y.
      exact: FD_Max.
  by rewrite /subst_judgement !subst_term_var in H'.
Qed.

Theorem ica_completeness {R : realType} {X : finType}
    (d : X -> X -> R) (Hd : forall x y, (0 <= d x y <= 1)%R)
    (s t : term (@ica_signature R) X) (eps : R) :
  (kantorovich_lifting d (term_distribution s) (term_distribution t) <= eps)%R ->
  @frel_derives R ica_signature (@ica_theory R) FRelFull
    (finite_fuzzy_space Hd) (QEqJ eps s t).
Proof.
  move => Hle.
  apply: FD_OrderComplete => delta Hdelta.
  apply: derives_fin_to_full.
  have Hd0 : forall x y, (0 <= d x y)%R.
    move => x y; case/andP: (Hd x y) => H0 _; exact: H0.
  have Heta : (0 < delta -
      kantorovich_lifting d (term_distribution s) (term_distribution t))%R.
    rewrite subr_gt0.
    exact: le_lt_trans Hle Hdelta.
  have [gamma Hgamma] := kantorovich_almost_optimal
    (term_distribution s) (term_distribution t) Hd0 Heta.
  have Heq : (kantorovich_lifting d (term_distribution s)
      (term_distribution t) +
      (delta - kantorovich_lifting d (term_distribution s)
        (term_distribution t)))%R = delta.
    by rewrite addrC subrK.
  rewrite Heq in Hgamma.
  have Hcost_le : (coupling_cost d gamma <= delta)%R := ltW Hgamma.
  have HQ := ica_coupling_term_QEqJ Hd gamma.
  have HQ' := FD_Up Hcost_le HQ.
  have Hfst := ica_finite_eqj_reambient Hd (ica_coupling_term_fst FRelFinite gamma).
  have Hsnd := ica_finite_eqj_reambient Hd (ica_coupling_term_snd FRelFinite gamma).
  exact: (FD_QEqReplaceR (FD_QEqReplaceL (FD_EqSym Hfst) HQ') Hsnd).
Qed.

Set Silent.
Print Assumptions ica_completeness.
Unset Silent.

Theorem ica_finite_completeness {R : realType} {X : finType}
    (d : X -> X -> R) (Hd : forall x y, (0 <= d x y <= 1)%R)
    (s t : term (@ica_signature R) X) (eps : R) :
  (kantorovich_lifting d (term_distribution s) (term_distribution t) <= eps)%R ->
  @frel_derives R ica_signature (@ica_theory R) FRelFinite
    (finite_fuzzy_space Hd) (QEqJ eps s t).
Proof.
  move => Hle.
  have Hd0 : forall x y, (0 <= d x y)%R.
    move => x y; case/andP: (Hd x y) => H0 _; exact: H0.
  have [gamma Hgamma] := kantorovich_optimal_coupling
    (term_distribution s) (term_distribution t) Hd0.
  have HQ := ica_coupling_term_QEqJ Hd gamma.
  rewrite Hgamma in HQ.
  have HQ' := FD_Up Hle HQ.
  have Hfst := ica_finite_eqj_reambient Hd (ica_coupling_term_fst FRelFinite gamma).
  have Hsnd := ica_finite_eqj_reambient Hd (ica_coupling_term_snd FRelFinite gamma).
  exact: (FD_QEqReplaceR (FD_QEqReplaceL (FD_EqSym Hfst) HQ') Hsnd).
Qed.