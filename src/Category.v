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

Record Functor (C D : Category) := {
  f_obj : Obj C -> Obj D;
  f_hom : forall {X Y : Obj C},
    Hom X Y -> Hom (f_obj X) (f_obj Y);
  f_id : forall X,
    f_hom (id X) = id (f_obj X);
  f_comp : forall {X Y Z : Obj C}
      (g : Hom Y Z) (f : Hom X Y),
    f_hom (g <| f) = f_hom g <| f_hom f;
}.

Record MonoidalCategory := {
  mon_cat :> Category;
  t_obj : Obj mon_cat -> Obj mon_cat -> Obj mon_cat;
  t_hom : forall {A B C D : Obj mon_cat},
    Hom A C -> Hom B D -> Hom (t_obj A B) (t_obj C D);
  t_unit : Obj mon_cat;
  t_assoc : forall A B C,
    Hom (t_obj (t_obj A B) C)
        (t_obj A (t_obj B C));
  t_assoc_inv : forall A B C,
    Hom (t_obj A (t_obj B C))
        (t_obj (t_obj A B) C);
  t_left_unitor : forall A,
    Hom (t_obj t_unit A) A;
  t_left_unitor_inv : forall A,
    Hom A (t_obj t_unit A);
  t_right_unitor : forall A,
    Hom (t_obj A t_unit) A;
  t_right_unitor_inv : forall A,
    Hom A (t_obj A t_unit)
}.

Record EnrichedCategory (V : MonoidalCategory) := {
  e_obj : Type;
  e_hom : e_obj -> e_obj -> Obj V;
  e_id : forall X,
    Hom (t_unit V) (e_hom X X);
  e_comp : forall X Y Z,
    Hom (t_obj (e_hom Y Z) (e_hom X Y))
        (e_hom X Z)
}.

Record EnrichedFunctor {V : MonoidalCategory}
    (C D : EnrichedCategory V) := {
  e_f_obj : e_obj C -> e_obj D;
  e_f_hom : forall X Y,
    Hom (e_hom X Y)
        (e_hom (e_f_obj X) (e_f_obj Y));
  e_f_id : forall X,
    e_f_hom X X <| @e_id V C X =
    @e_id V D (e_f_obj X);
  e_f_comp : forall X Y Z,
    e_f_hom X Z <| @e_comp V C X Y Z =
    @e_comp V D
        (e_f_obj X)
        (e_f_obj Y)
        (e_f_obj Z)
      <| t_hom (e_f_hom Y Z) (e_f_hom X Y);
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
