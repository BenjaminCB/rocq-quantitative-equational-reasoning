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
  obj : Type;
  hom : obj -> obj -> Type;
  id : forall X, hom X X;
  comp : forall {X Y Z}, hom Y Z -> hom X Y -> hom X Z;
  comp_assoc : forall {W X Y Z}
      (h : hom Y Z) (g : hom X Y) (f : hom W X),
    comp h (comp g f) = comp (comp h g) f;
  comp_id_l : forall {X Y} (f : hom X Y), comp (id Y) f = f;
  comp_id_r : forall {X Y} (f : hom X Y), comp f (id X) = f;
}.

Notation "f <| g" := (comp f g)
  (at level 40, left associativity).

Record Functor (C D : Category) := {
  f_obj : obj C -> obj D;
  f_hom : forall {X Y : obj C},
    hom X Y -> hom (f_obj X) (f_obj Y);
  f_id : forall X,
    f_hom (id X) = id (f_obj X);
  f_comp : forall {X Y Z : obj C}
      (g : hom Y Z) (f : hom X Y),
    f_hom (g <| f) = f_hom g <| f_hom f;
}.

Record MonoidalCategory := {
  mon_cat :> Category;
  t_obj : obj mon_cat -> obj mon_cat -> obj mon_cat;
  t_hom : forall {A B C D : obj mon_cat},
    hom A C -> hom B D -> hom (t_obj A B) (t_obj C D);
  t_unit : obj mon_cat;
  t_assoc : forall A B C,
    hom (t_obj (t_obj A B) C)
        (t_obj A (t_obj B C));
  t_assoc_inv : forall A B C,
    hom (t_obj A (t_obj B C))
        (t_obj (t_obj A B) C);
  t_left_unitor : forall A,
    hom (t_obj t_unit A) A;
  t_left_unitor_inv : forall A,
    hom A (t_obj t_unit A);
  t_right_unitor : forall A,
    hom (t_obj A t_unit) A;
  t_right_unitor_inv : forall A,
    hom A (t_obj A t_unit)
}.

Record EnrichedCategory (V : MonoidalCategory) := {
  e_obj : Type;
  e_hom : e_obj -> e_obj -> obj V;
  e_id : forall X,
    hom (t_unit V) (e_hom X X);
  e_comp : forall X Y Z,
    hom (t_obj (e_hom Y Z) (e_hom X Y))
        (e_hom X Z)
}.

Record EnrichedFunctor {V : MonoidalCategory}
    (C D : EnrichedCategory V) := {
  e_f_obj : e_obj C -> e_obj D;
  e_f_hom : forall X Y,
    hom (e_hom X Y)
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

Record Metrichom {R : realType} (M N : ext_metric_space R) := {
  metric_hom_fun : carrier M -> carrier N;
  metric_hom_nexp : forall a b,
    dist (metric_hom_fun a) (metric_hom_fun b) <= dist a b
}.

Lemma Metrichom_ext {R : realType} {M N : ext_metric_space R}
    (f g : Metrichom M N) :
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

Definition Metrichom_id {R : realType} (M : ext_metric_space R) :
    Metrichom M M.
Proof.
  refine {| metric_hom_fun := fun x => x |}.
  move=> a b.
  exact: lexx.
Defined.

Definition Metrichom_comp {R : realType}
    {M N P : ext_metric_space R}
    (g : Metrichom N P) (f : Metrichom M N) : Metrichom M P.
Proof.
  refine {| metric_hom_fun := fun x => metric_hom_fun g (metric_hom_fun f x) |}.
  move=> a b.
  exact: (le_trans (metric_hom_nexp g (metric_hom_fun f a) (metric_hom_fun f b))
                   (metric_hom_nexp f a b)).
Defined.

Definition Met (R : realType) : Category.
Proof.
  refine {|
    obj := ext_metric_space R;
    hom := @Metrichom R;
    id := @Metrichom_id R;
    comp := fun _ _ _ => @Metrichom_comp R _ _ _
  |}.
  - move=> W X Y Z h g f.
    apply Metrichom_ext => x.
    reflexivity.
  - move=> X Y f.
    apply Metrichom_ext => x.
    reflexivity.
  - move=> X Y f.
    apply Metrichom_ext => x.
    reflexivity.
Defined.
