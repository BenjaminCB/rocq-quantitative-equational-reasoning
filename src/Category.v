(* ============================================================
   Generic category-theoretic infrastructure
   ============================================================ *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp Require Import all_classical reals ereal.

From Template Require Import Metric.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ereal_scope.

Record Category := {
  Obj : Type;
  Hom : Obj -> Obj -> Type;
  id : forall X, Hom X X;
  comp : forall {X Y Z}, Hom Y Z -> Hom X Y -> Hom X Z;
  comp_assoc : forall {W X Y Z}
      (h : Hom Y Z) (g : Hom X Y) (f : Hom W X),
    comp h (comp g f) = comp (comp h g) f;
  comp_id_l : forall {X Y} (f : Hom X Y), comp (id Y) f = f;
  comp_id_r : forall {X Y} (f : Hom X Y), comp f (id X) = f;
}.

Notation "f <| g" := (comp f g)
  (at level 40, left associativity).

Record MonoidalCategory := {
  mon_cat :> Category;
  tensor_obj : Obj mon_cat -> Obj mon_cat -> Obj mon_cat;
  tensor_hom : forall {A B C D : Obj mon_cat},
    Hom A C -> Hom B D -> Hom (tensor_obj A B) (tensor_obj C D);
  tensor_unit : Obj mon_cat;
  tensor_assoc : forall A B C,
    Hom (tensor_obj (tensor_obj A B) C)
        (tensor_obj A (tensor_obj B C));
  tensor_assoc_inv : forall A B C,
    Hom (tensor_obj A (tensor_obj B C))
        (tensor_obj (tensor_obj A B) C);
  tensor_left_unitor : forall A,
    Hom (tensor_obj tensor_unit A) A;
  tensor_left_unitor_inv : forall A,
    Hom A (tensor_obj tensor_unit A);
  tensor_right_unitor : forall A,
    Hom (tensor_obj A tensor_unit) A;
  tensor_right_unitor_inv : forall A,
    Hom A (tensor_obj A tensor_unit)
}.

Record EnrichedCategory (V : MonoidalCategory) := {
  enriched_obj : Type;
  enriched_hom : enriched_obj -> enriched_obj -> Obj V;
  enriched_id : forall X,
    Hom (tensor_unit V) (enriched_hom X X);
  enriched_comp : forall X Y Z,
    Hom (tensor_obj (enriched_hom Y Z) (enriched_hom X Y))
        (enriched_hom X Z)
}.

Record MetricHom {R : realType} (M N : ext_metric_space R) := {
  metric_hom_fun : carrier M -> carrier N;
  metric_hom_nexp : forall a b,
    dist (metric_hom_fun a) (metric_hom_fun b) <= dist a b
}.

Lemma MetricHom_ext {R : realType} {M N : ext_metric_space R}
    (f g : MetricHom M N) :
  (forall x, metric_hom_fun f x = metric_hom_fun g x) -> f = g.
Proof.
  case: f => ff f_nexp.
  case: g => gf g_nexp.
  move => /= Hfg.
  have Hfun : ff = gf by apply functional_extensionality.
  case: gf / Hfun in g_nexp Hfg *.
  f_equal.
  apply proof_irrelevance.
Qed.

Definition MetricHom_id {R : realType} (M : ext_metric_space R) :
    MetricHom M M.
Proof.
  refine {| metric_hom_fun := fun x => x |}.
  move=> a b.
  exact: lexx.
Defined.

Definition MetricHom_comp {R : realType}
    {M N P : ext_metric_space R}
    (g : MetricHom N P) (f : MetricHom M N) : MetricHom M P.
Proof.
  refine {| metric_hom_fun := fun x => metric_hom_fun g (metric_hom_fun f x) |}.
  move=> a b.
  exact: (le_trans (metric_hom_nexp g (metric_hom_fun f a) (metric_hom_fun f b))
                   (metric_hom_nexp f a b)).
Defined.

Definition MetricSpaceCategory (R : realType) : Category.
Proof.
  refine {|
    Obj := ext_metric_space R;
    Hom := @MetricHom R;
    id := @MetricHom_id R;
    comp := fun _ _ _ => @MetricHom_comp R _ _ _
  |}.
  - move=> W X Y Z h g f.
    apply MetricHom_ext => x.
    reflexivity.
  - move=> X Y f.
    apply MetricHom_ext => x.
    reflexivity.
  - move=> X Y f.
    apply MetricHom_ext => x.
    reflexivity.
Defined.