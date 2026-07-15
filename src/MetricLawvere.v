(* ============================================================
   Metric refinements of quantitative enriched Lawvere theories
   ============================================================ *)

From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp Require Import all_classical reals ereal.

From Template Require Import Metric Category QET.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Definition rat_to_ereal (R : realType) (eps : rat) : \bar R :=
  (ratr eps : R)%:E.

(* ============================================================
   Zero-distance equivalence
   ============================================================ *)

Definition qspace_zero_equiv (A : QuantitativeSpace)
    (x y : qs_carrier A) : Prop :=
  @qs_rel A 0 x y.

Lemma qspace_zero_equiv_refl (A : QuantitativeSpace)
    (x : qs_carrier A) :
  @qspace_zero_equiv A x x.
Proof. exact: qs_refl. Qed.

Lemma qspace_zero_equiv_symm (A : QuantitativeSpace)
    (x y : qs_carrier A) :
  @qspace_zero_equiv A x y -> @qspace_zero_equiv A y x.
Proof. exact: qs_symm. Qed.

Lemma qspace_zero_equiv_trans (A : QuantitativeSpace)
    (x y z : qs_carrier A) :
  @qspace_zero_equiv A x y ->
  @qspace_zero_equiv A y z ->
  @qspace_zero_equiv A x z.
Proof.
  move=> Hxy Hyz.
  have := @qs_tri A 0 0 x y z Hxy Hyz.
  by rewrite addr0.
Qed.

Lemma qspace_hom_respects_zero {A B : QuantitativeSpace}
    (f : QSpaceHom A B) (x y : qs_carrier A) :
  @qspace_zero_equiv A x y ->
  @qspace_zero_equiv B (qs_hom_fun f x) (qs_hom_fun f y).
Proof. exact: qs_hom_nexp. Qed.

Lemma qlt_comp_respects_zero (U : QuantitativeLawvereTheory)
    {n m k : nat}
    (g g' : qlt_op U m k) (f f' : qlt_op U n m) :
  @qspace_zero_equiv (qlt_hom_object U m k) g g' ->
  @qspace_zero_equiv (qlt_hom_object U n m) f f' ->
  @qspace_zero_equiv (qlt_hom_object U n k)
    (@qlt_comp U n m k g f)
    (@qlt_comp U n m k g' f').
Proof.
  move=> Hg Hf.
  apply: (@qs_hom_nexp _ _ (qlt_comp_hom U n m k) 0 (g, f) (g', f')).
  exists (0 : rat), (0 : rat).
  split; first by rewrite addr0.
  split; assumption.
Qed.

(* ============================================================
   Metric quotient of a quantitative space
   ============================================================ *)

Record QSpaceMetricQuotient (R : realType) (A : QuantitativeSpace) := {
  qmq_space : ext_metric_space R;
  qmq_class : qs_carrier A -> carrier qmq_space;
  qmq_surj : forall z : carrier qmq_space, exists x, qmq_class x = z;
  qmq_bound : forall eps x y,
    @qs_rel A eps x y ->
    dist (qmq_class x) (qmq_class y) <= rat_to_ereal R eps;
  qmq_zero_exact : forall x y,
    @qspace_zero_equiv A x y <-> qmq_class x = qmq_class y;
}.

Arguments qmq_space {R A} _.
Arguments qmq_class {R A} _ _.
Arguments qmq_surj {R A} _ _.
Arguments qmq_bound {R A} _ {eps x y} _.
Arguments qmq_zero_exact {R A} _ _ _.

Definition qmq_metric_hom_object {R : realType} {A : QuantitativeSpace}
    (Q : QSpaceMetricQuotient R A) : obj (Met R) :=
  qmq_space Q.

(* ============================================================
   Metric-enriched categories using additive composition bounds
   ============================================================ *)

Record MetricEnrichedCategory (R : realType) := {
  me_obj : Type;
  me_hom : me_obj -> me_obj -> ext_metric_space R;
  me_id : forall X, carrier (me_hom X X);
  me_comp : forall X Y Z,
    carrier (me_hom Y Z) ->
    carrier (me_hom X Y) ->
    carrier (me_hom X Z);
  me_comp_nexp : forall X Y Z
      (g g' : carrier (me_hom Y Z))
      (f f' : carrier (me_hom X Y)),
    dist (me_comp g f) (me_comp g' f') <=
    dist g g' + dist f f';
}.

Record MetricEnrichedFunctor {R : realType}
    (C D : MetricEnrichedCategory R) := {
  mef_obj : me_obj C -> me_obj D;
  mef_hom : forall X Y,
    Metrichom
      (@me_hom R C X Y)
      (@me_hom R D (mef_obj X) (mef_obj Y));
  mef_id : forall X,
    metric_hom_fun (mef_hom X X) (@me_id R C X) =
    @me_id R D (mef_obj X);
  mef_comp : forall X Y Z
      (g : carrier (@me_hom R C Y Z))
      (f : carrier (@me_hom R C X Y)),
    metric_hom_fun (mef_hom X Z) (@me_comp R C X Y Z g f) =
    @me_comp R D (mef_obj X) (mef_obj Y) (mef_obj Z)
      (metric_hom_fun (mef_hom Y Z) g)
      (metric_hom_fun (mef_hom X Y) f);
}.

(* ============================================================
   Transporting a quantitative Lawvere theory to metric spaces
   ============================================================ *)

Record MetricLawvereQuotient
    (R : realType) (U : QuantitativeLawvereTheory) := {
  mlq_hom : forall n m, QSpaceMetricQuotient R (qlt_hom_object U n m);
  mlq_comp : forall n m k,
    carrier (qmq_space (mlq_hom m k)) ->
    carrier (qmq_space (mlq_hom n m)) ->
    carrier (qmq_space (mlq_hom n k));
  mlq_comp_agrees : forall n m k
      (g : qlt_op U m k) (f : qlt_op U n m),
    mlq_comp
      (qmq_class (mlq_hom m k) g)
      (qmq_class (mlq_hom n m) f) =
    qmq_class (mlq_hom n k) (@qlt_comp U n m k g f);
  mlq_comp_nexp : forall n m k
      (g g' : carrier (qmq_space (mlq_hom m k)))
      (f f' : carrier (qmq_space (mlq_hom n m))),
    dist (mlq_comp g f) (mlq_comp g' f') <=
    dist g g' + dist f f';
}.

Arguments mlq_hom {R U} _ _ _.
Arguments mlq_comp {R U} _ {n m k} _ _.
Arguments mlq_comp_agrees {R U} _ {n m k} _ _.
Arguments mlq_comp_nexp {R U} _ {n m k} _ _ _ _.

Definition mlq_id {R : realType} {U : QuantitativeLawvereTheory}
    (Q : MetricLawvereQuotient R U) (n : nat) :
    carrier (qmq_space (mlq_hom Q n n)) :=
  qmq_class (mlq_hom Q n n) (@qlt_id U n).

Definition MetricEnrichedLawvereCategory
    (R : realType)
    (U : QuantitativeLawvereTheory)
    (Q : MetricLawvereQuotient R U) :
    MetricEnrichedCategory R.
Proof.
  refine {|
    me_obj := nat;
    me_hom := fun n m => qmq_space (mlq_hom Q n m);
    me_id := mlq_id Q;
    me_comp := fun n m k => @mlq_comp R U Q n m k;
    me_comp_nexp := fun n m k => @mlq_comp_nexp R U Q n m k
  |}.
Defined.
