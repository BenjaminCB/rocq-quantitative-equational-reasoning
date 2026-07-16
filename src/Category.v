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

Record Metric_hom {R : realType} (M N : ext_metric_space R) := {
  metric_hom_fun : carrier M -> carrier N;
  metric_hom_nexp : forall a b,
    dist (metric_hom_fun a) (metric_hom_fun b) <= dist a b
}.

Lemma Metric_hom_ext {R : realType} {M N : ext_metric_space R}
    (f g : Metric_hom M N) :
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

Definition Metric_hom_id {R : realType} (M : ext_metric_space R) :
    Metric_hom M M.
Proof.
  refine {| metric_hom_fun := fun x => x |}.
  move=> a b.
  exact: lexx.
Defined.

Definition Metric_hom_comp {R : realType}
    {M N P : ext_metric_space R}
    (g : Metric_hom N P) (f : Metric_hom M N) : Metric_hom M P.
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
    hom := @Metric_hom R;
    id := @Metric_hom_id R;
    comp := fun _ _ _ => @Metric_hom_comp R _ _ _
  |}.
  - move=> W X Y Z h g f.
    apply Metric_hom_ext => x.
    reflexivity.
  - move=> X Y f.
    apply Metric_hom_ext => x.
    reflexivity.
  - move=> X Y f.
    apply Metric_hom_ext => x.
    reflexivity.
Defined.

Definition prod_metric_space {R : realType} (M N : ext_metric_space R) :
    ext_metric_space R.
Proof.
  refine {|
    carrier := carrier M * carrier N;
    dist := fun p q => maxe (dist p.1 q.1) (dist p.2 q.2);
  |}.
  - move => a b. 
    rewrite /maxe.
    case (dist a.1 b.1 < dist a.2 b.2); apply dist_ge0.
  - move => a.
    rewrite /maxe !dist_refl if_same //=.
  - move => [a1 a2] [b1 b2] H.
    have Ha : dist a1 b1 = 0.
      have h1 : dist a1 b1 <= 0%R by rewrite -H le_max lexx.
      have h2 : 0%R <= dist a1 b1 := dist_ge0 a1 b1.
      by apply/eqP; rewrite eq_le h2 h1.
    have Hb : dist a2 b2 = 0.
      have h1 : dist a2 b2 <= 0%R by rewrite -H le_max lexx orbT.
      have h2 : 0%R <= dist a2 b2 := dist_ge0 a2 b2.
      by apply/eqP; rewrite eq_le h2 h1.
    have E1 : a1 = b1 by exact: dist_eq0 a1 b1 Ha.
    have E2 : a2 = b2 by exact: dist_eq0 a2 b2 Hb.
    by subst b1; subst b2.
  - move => [a1 a2] [b1 b2].
    simpl.
    by rewrite (dist_symm a1 b1) (dist_symm a2 b2) maxC.
  - move => [a1 a2] [b1 b2] [c1 c2].
    simpl.
    apply: (le_trans (le_max2 (dist_tri a1 b1 c1) (dist_tri a2 b2 c2))).
    rewrite ge_max.
    apply/andP; split; apply: leeD; rewrite le_max ?lexx ?orbT //.
Defined.

Definition unit_ext_metric_space {R : realType} : ext_metric_space R.
Proof.
  refine {|
    carrier := unit;
    dist := fun _ _ => 0%:E;
  |}.
  - by [].
  - by [].
  - move => a b H.
    case a; case b.
    by [].
  - by [].
  - by move=> _ _ _; rewrite add0e.
Defined.

Definition MetMonoidal (R : realType) : MonoidalCategory.
Proof.
  refine {|
    mon_cat := Met R;
    t_obj := fun M N => prod_ext_metric_space R (obj M) (obj N);
    t_hom := fun A B C D f g => (* product of Metric_hom *);
    t_unit := unit_ext_metric_space R;
    (* coherence isomorphisms: associator, left/right unitors *);
  |}.
Defined.