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
Local Open Scope classical_set_scope.

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
        (e_hom X Z);
  e_comp_assoc : forall W X Y Z,
    e_comp X Y W <| t_hom (e_comp Y Z W) (id (e_hom X Y)) =
    e_comp X Z W
      <| t_hom (id (e_hom Z W)) (e_comp X Y Z)
      <| t_assoc (e_hom Z W) (e_hom Y Z) (e_hom X Y);
  e_comp_id_l : forall X Y,
    e_comp X Y Y <| t_hom (e_id Y) (id (e_hom X Y)) =
    t_left_unitor (e_hom X Y);
  e_comp_id_r : forall X Y,
    e_comp X X Y <| t_hom (id (e_hom X Y)) (e_id X) =
    t_right_unitor (e_hom X Y)
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

Definition met_t_obj {R : realType} (M N : ext_metric_space R) :
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

Definition met_t_hom {R : realType} {A B C D : ext_metric_space R}
    (f : Metric_hom A C) (g : Metric_hom B D) :
    Metric_hom (met_t_obj A B) (met_t_obj C D).
Proof.
  refine (@Build_Metric_hom R (met_t_obj A B) (met_t_obj C D)
    (fun xy : carrier (met_t_obj A B) =>
      (metric_hom_fun f xy.1, metric_hom_fun g xy.2)) _).
  move => [x y] [x' y'].
  rewrite /dist //= /maxe.
  case: ifP => H1; case: ifP => H2.
  - exact: metric_hom_nexp g y y'.
  - have Hyx : dist y y' <= dist x x' by rewrite leNgt H2.
    exact: le_trans (metric_hom_nexp g y y') Hyx.
  - apply ltW in H2.
    exact: le_trans (metric_hom_nexp f x x') H2.
  - exact: metric_hom_nexp f x x'.
Defined.

Definition met_t_unit {R : realType} : ext_metric_space R.
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

Definition met_t_assoc {R : realType} (A B C : ext_metric_space R) :
    Metric_hom (met_t_obj (met_t_obj A B) C)
               (met_t_obj A (met_t_obj B C)).
Proof.
  refine (@Build_Metric_hom R
    (met_t_obj (met_t_obj A B) C)
    (met_t_obj A (met_t_obj B C))
    (fun xyz : carrier (met_t_obj (met_t_obj A B) C) =>
      (xyz.1.1, (xyz.1.2, xyz.2))) _).
  move => [[x y] z] [[x' y'] z'] //=.
  by rewrite maxA.
Defined.

Definition met_t_assoc_inv {R : realType} (A B C : ext_metric_space R) :
    Metric_hom (met_t_obj A (met_t_obj B C))
               (met_t_obj (met_t_obj A B) C).
Proof.
  refine (@Build_Metric_hom R
    (met_t_obj A (met_t_obj B C))
    (met_t_obj (met_t_obj A B) C)
    (fun xyz : carrier (met_t_obj A (met_t_obj B C)) =>
      ((xyz.1, xyz.2.1), xyz.2.2)) _).
  move => [x [y z]] [x' [y' z']] //=.
  by rewrite maxA.
Defined.

Definition met_t_left_unitor {R : realType} (A : ext_metric_space R) :
    Metric_hom (met_t_obj met_t_unit A) A.
Proof.
  refine (@Build_Metric_hom R (met_t_obj met_t_unit A) A
    (fun ux : carrier (met_t_obj met_t_unit A) => ux.2) _).
  move => [u a] [u' b] //=.
  rewrite /maxe.
  case: ifP => H; first by [].
  have H' : dist a b <= 0 by rewrite leNgt H.
  exact: H'.
Defined.

Definition met_t_left_unitor_inv {R : realType} (A : ext_metric_space R) :
    Metric_hom A (met_t_obj met_t_unit A).
Proof.
  refine (@Build_Metric_hom R A (met_t_obj met_t_unit A)
    (fun x : carrier A => (tt, x)) _).
  move => a b.
  rewrite {1}/dist //= /maxe.
  case: ifP => H; first by [].
  exact: dist_ge0.
Defined.

Definition met_t_right_unitor {R : realType} (A : ext_metric_space R) :
    Metric_hom (met_t_obj A met_t_unit) A.
Proof.
  refine (@Build_Metric_hom R (met_t_obj A met_t_unit) A
    (fun xu : carrier (met_t_obj A met_t_unit) => xu.1) _).
  move => [a u] [b u'] //=.
  rewrite /maxe.
  case: ifP => H; last by [].
  move /ltW in H.
  exact: H.
Defined.

Definition met_t_right_unitor_inv {R : realType} (A : ext_metric_space R) :
    Metric_hom A (met_t_obj A met_t_unit).
Proof.
  refine (@Build_Metric_hom R A (met_t_obj A met_t_unit)
    (fun x : carrier A => (x, tt)) _).
  move => a b.
  rewrite {1}/dist //= /maxe.
  case: ifP => H; last by [].
  exact: dist_ge0.
Defined.

Definition MetMonoidal {R : realType} : MonoidalCategory.
Proof.
  refine {|
    mon_cat := Met R;
    t_obj := met_t_obj;
    t_hom := fun _ _ _ _ => met_t_hom;
    t_unit := met_t_unit;
    t_assoc := met_t_assoc;
    t_assoc_inv := met_t_assoc_inv;
    t_left_unitor := met_t_left_unitor;
    t_left_unitor_inv := met_t_left_unitor_inv;
    t_right_unitor := met_t_right_unitor;
    t_right_unitor_inv := met_t_right_unitor_inv
  |}.
Defined.

(* ============================================================
   Additive monoidal structure on metric spaces

   Unlike the max tensor used for finite powers, this tensor is the
   appropriate base for enriched composition: changing both arrows
   contributes the sum of their errors.
   ============================================================ *)

Definition met_add_t_obj {R : realType}
    (M N : ext_metric_space R) : ext_metric_space R.
Proof.
  refine {|
    carrier := carrier M * carrier N;
    dist := fun p q => dist p.1 q.1 + dist p.2 q.2
  |}.
  - move=> a b.
    exact: adde_ge0 (dist_ge0 a.1 b.1) (dist_ge0 a.2 b.2).
  - move=> a.
    by rewrite !dist_refl add0e.
  - move=> [a1 a2] [b1 b2] H.
    have Ha_le : dist a1 b1 <= 0.
    { rewrite -H.
      exact: leeDl (dist_ge0 a2 b2). }
    have Hb_le : dist a2 b2 <= 0.
    { rewrite -H.
      exact: leeDr (dist_ge0 a1 b1). }
    have Ha : dist a1 b1 = 0.
    { apply: Order.POrderTheory.le_anti.
      by apply/andP; split; [exact Ha_le | exact: dist_ge0]. }
    have Hb : dist a2 b2 = 0.
    { apply: Order.POrderTheory.le_anti.
      by apply/andP; split; [exact Hb_le | exact: dist_ge0]. }
    have -> : a1 = b1 := @dist_eq0 R M a1 b1 Ha.
    have -> : a2 = b2 := @dist_eq0 R N a2 b2 Hb.
    reflexivity.
  - move=> [a1 a2] [b1 b2] /=.
    by rewrite (dist_symm a1 b1) (dist_symm a2 b2).
  - move=> [a1 a2] [b1 b2] [c1 c2] /=.
    rewrite addeACA.
    exact: leeD (dist_tri a1 b1 c1) (dist_tri a2 b2 c2).
Defined.

Definition met_add_t_hom {R : realType}
    {A B C D : ext_metric_space R}
    (f : Metric_hom A C) (g : Metric_hom B D) :
    Metric_hom (met_add_t_obj A B) (met_add_t_obj C D).
Proof.
  refine (@Build_Metric_hom R
    (met_add_t_obj A B) (met_add_t_obj C D)
    (fun xy : carrier (met_add_t_obj A B) =>
      (metric_hom_fun f xy.1, metric_hom_fun g xy.2)) _).
  move=> [x y] [x' y'] /=.
  exact: leeD (metric_hom_nexp f x x') (metric_hom_nexp g y y').
Defined.

Definition met_add_t_assoc {R : realType}
    (A B C : ext_metric_space R) :
    Metric_hom (met_add_t_obj (met_add_t_obj A B) C)
               (met_add_t_obj A (met_add_t_obj B C)).
Proof.
  refine (@Build_Metric_hom R
    (met_add_t_obj (met_add_t_obj A B) C)
    (met_add_t_obj A (met_add_t_obj B C))
    (fun xyz : carrier (met_add_t_obj (met_add_t_obj A B) C) =>
      (xyz.1.1, (xyz.1.2, xyz.2))) _).
  move=> [[x y] z] [[x' y'] z'] /=.
  by rewrite addeA.
Defined.

Definition met_add_t_assoc_inv {R : realType}
    (A B C : ext_metric_space R) :
    Metric_hom (met_add_t_obj A (met_add_t_obj B C))
               (met_add_t_obj (met_add_t_obj A B) C).
Proof.
  refine (@Build_Metric_hom R
    (met_add_t_obj A (met_add_t_obj B C))
    (met_add_t_obj (met_add_t_obj A B) C)
    (fun xyz : carrier (met_add_t_obj A (met_add_t_obj B C)) =>
      ((xyz.1, xyz.2.1), xyz.2.2)) _).
  move=> [x [y z]] [x' [y' z']] /=.
  by rewrite addeA.
Defined.

Definition met_add_t_left_unitor {R : realType}
    (A : ext_metric_space R) :
    Metric_hom (met_add_t_obj met_t_unit A) A.
Proof.
  refine (@Build_Metric_hom R
    (met_add_t_obj met_t_unit A) A
    (fun ux : carrier (met_add_t_obj met_t_unit A) => ux.2) _).
  by move=> [u x] [u' y] /=; rewrite add0e.
Defined.

Definition met_add_t_left_unitor_inv {R : realType}
    (A : ext_metric_space R) :
    Metric_hom A (met_add_t_obj met_t_unit A).
Proof.
  refine (@Build_Metric_hom R A (met_add_t_obj met_t_unit A)
    (fun x : carrier A => (tt, x)) _).
  by move=> x y /=; rewrite add0e.
Defined.

Definition met_add_t_right_unitor {R : realType}
    (A : ext_metric_space R) :
    Metric_hom (met_add_t_obj A met_t_unit) A.
Proof.
  refine (@Build_Metric_hom R
    (met_add_t_obj A met_t_unit) A
    (fun xu : carrier (met_add_t_obj A met_t_unit) => xu.1) _).
  by move=> [x u] [y u'] /=; rewrite adde0.
Defined.

Definition met_add_t_right_unitor_inv {R : realType}
    (A : ext_metric_space R) :
    Metric_hom A (met_add_t_obj A met_t_unit).
Proof.
  refine (@Build_Metric_hom R A (met_add_t_obj A met_t_unit)
    (fun x : carrier A => (x, tt)) _).
  by move=> x y /=; rewrite adde0.
Defined.

Definition MetAddMonoidal {R : realType} : MonoidalCategory.
Proof.
  refine {|
    mon_cat := Met R;
    t_obj := met_add_t_obj;
    t_hom := fun _ _ _ _ => met_add_t_hom;
    t_unit := met_t_unit;
    t_assoc := met_add_t_assoc;
    t_assoc_inv := met_add_t_assoc_inv;
    t_left_unitor := met_add_t_left_unitor;
    t_left_unitor_inv := met_add_t_left_unitor_inv;
    t_right_unitor := met_add_t_right_unitor;
    t_right_unitor_inv := met_add_t_right_unitor_inv
  |}.
Defined.

(* ============================================================
   Sup metric on non-expansive maps
   ============================================================ *)

Definition metric_hom_sup_dist {R : realType}
    {M N : ext_metric_space R} (f g : Metric_hom M N) : \bar R :=
  ereal_sup (range (fun ox : option (carrier M) =>
    match ox with
    | Some x => dist (metric_hom_fun f x) (metric_hom_fun g x)
    | None => 0
    end)).

Lemma metric_hom_sup_ubound {R : realType}
    {M N : ext_metric_space R} (f g : Metric_hom M N)
    (ox : option (carrier M)) :
  (match ox with
   | Some x => dist (metric_hom_fun f x) (metric_hom_fun g x)
   | None => 0
   end) <= metric_hom_sup_dist f g.
Proof.
  apply: ereal_sup_ubound.
  by exists ox.
Qed.

Definition metric_hom_space {R : realType}
    (M N : ext_metric_space R) : ext_metric_space R.
Proof.
  refine {|
    carrier := Metric_hom M N;
    dist := metric_hom_sup_dist
  |}.
  - move=> f g.
    exact: (@metric_hom_sup_ubound R M N f g None).
  - move=> f.
    apply: Order.POrderTheory.le_anti.
    apply/andP; split.
    + apply: ge_ereal_sup => y.
      move=> [ox _ <-].
      by case: ox => [x|] /=; rewrite ?dist_refl.
    + exact: (@metric_hom_sup_ubound R M N f f None).
  - move=> f g H.
    apply Metric_hom_ext => x.
    have Hzero :
        dist (metric_hom_fun f x) (metric_hom_fun g x) = 0.
    { apply: Order.POrderTheory.le_anti.
      apply/andP; split.
      - have Hx := @metric_hom_sup_ubound R M N f g (Some x).
        by rewrite H in Hx.
      - exact: dist_ge0. }
    exact: (@dist_eq0 R N
      (metric_hom_fun f x) (metric_hom_fun g x) Hzero).
  - move=> f g.
    apply: Order.POrderTheory.le_anti.
    apply/andP; split.
    + apply: ge_ereal_sup => y.
      move=> [ox _ <-].
      case: ox => [x|] /=.
      * rewrite dist_symm.
        exact: (@metric_hom_sup_ubound R M N g f (Some x)).
      * exact: (@metric_hom_sup_ubound R M N g f None).
    + apply: ge_ereal_sup => y.
      move=> [ox _ <-].
      case: ox => [x|] /=.
      * rewrite dist_symm.
        exact: (@metric_hom_sup_ubound R M N f g (Some x)).
      * exact: (@metric_hom_sup_ubound R M N f g None).
  - move=> f g h.
    apply: ge_ereal_sup => y.
    move=> [ox _ <-].
    case: ox => [x|] /=.
    + apply: (le_trans (dist_tri
        (metric_hom_fun f x)
        (metric_hom_fun g x)
        (metric_hom_fun h x))).
      exact: leeD
        (@metric_hom_sup_ubound R M N f g (Some x))
        (@metric_hom_sup_ubound R M N g h (Some x)).
    + exact: adde_ge0
        (@metric_hom_sup_ubound R M N f g None)
        (@metric_hom_sup_ubound R M N g h None).
Defined.

Definition met_enriched_id {R : realType} (M : ext_metric_space R) :
    Metric_hom met_t_unit (metric_hom_space M M).
Proof.
  refine (@Build_Metric_hom R met_t_unit (metric_hom_space M M)
    (fun _ : carrier met_t_unit => Metric_hom_id M) _).
  by move=> u v; rewrite !dist_refl.
Defined.

Definition met_enriched_comp {R : realType}
    (X Y Z : ext_metric_space R) :
    Metric_hom
      (met_add_t_obj (metric_hom_space Y Z) (metric_hom_space X Y))
      (metric_hom_space X Z).
Proof.
  refine (@Build_Metric_hom R
    (met_add_t_obj (metric_hom_space Y Z) (metric_hom_space X Y))
    (metric_hom_space X Z)
    (fun gf : carrier
        (met_add_t_obj (metric_hom_space Y Z) (metric_hom_space X Y)) =>
      Metric_hom_comp gf.1 gf.2) _).
  move=> [g f] [g' f'].
  change
    (metric_hom_sup_dist (Metric_hom_comp g f)
       (Metric_hom_comp g' f') <=
     metric_hom_sup_dist g g' + metric_hom_sup_dist f f')%E.
  apply: ge_ereal_sup => y.
  move=> [ox _ <-].
  case: ox => [x|] /=.
  - apply: (le_trans (dist_tri
      (metric_hom_fun g (metric_hom_fun f x))
      (metric_hom_fun g' (metric_hom_fun f x))
      (metric_hom_fun g' (metric_hom_fun f' x)))).
    apply: leeD.
    + exact: (@metric_hom_sup_ubound R Y Z g g'
        (Some (metric_hom_fun f x))).
    + apply: (le_trans
        (metric_hom_nexp g' (metric_hom_fun f x)
          (metric_hom_fun f' x))).
      exact: (@metric_hom_sup_ubound R X Y f f' (Some x)).
  - exact: adde_ge0
      (@metric_hom_sup_ubound R Y Z g g' None)
      (@metric_hom_sup_ubound R X Y f f' None).
Defined.

Definition MetSelfEnriched (R : realType) :
    EnrichedCategory (@MetAddMonoidal R).
Proof.
  refine (@Build_EnrichedCategory (@MetAddMonoidal R)
    (ext_metric_space R) (@metric_hom_space R)
    (@met_enriched_id R) (@met_enriched_comp R) _ _ _).
  - move=> W X Y Z.
    apply Metric_hom_ext => hgf.
    case: hgf => hg f.
    case: hg => h g.
    apply Metric_hom_ext => x.
    reflexivity.
  - move=> X Y.
    apply Metric_hom_ext => uf.
    case: uf => u f.
    case: u.
    apply Metric_hom_ext => x.
    reflexivity.
  - move=> X Y.
    apply Metric_hom_ext => fu.
    case: fu => f u.
    case: u.
    apply Metric_hom_ext => x.
    reflexivity.
Defined.

(* ============================================================
   Enriched representable models
   ============================================================ *)

Definition enriched_postcomp {R : realType}
    (C : EnrichedCategory (@MetAddMonoidal R))
    (A X Y : e_obj C) (g : carrier (e_hom X Y)) :
    Metric_hom (e_hom A X) (e_hom A Y).
Proof.
  refine (@Build_Metric_hom R (e_hom A X) (e_hom A Y)
    (fun f : carrier (e_hom A X) =>
      metric_hom_fun (@e_comp (@MetAddMonoidal R) C A X Y) (g, f)) _).
  move=> f f'.
  have H := metric_hom_nexp
    (@e_comp (@MetAddMonoidal R) C A X Y) (g, f) (g, f').
  by rewrite /= dist_refl add0e in H.
Defined.

Definition enriched_postcomp_hom {R : realType}
    (C : EnrichedCategory (@MetAddMonoidal R))
    (A X Y : e_obj C) :
    Metric_hom (e_hom X Y)
      (metric_hom_space (e_hom A X) (e_hom A Y)).
Proof.
  refine (@Build_Metric_hom R (e_hom X Y)
    (metric_hom_space (e_hom A X) (e_hom A Y))
    (fun g : carrier (e_hom X Y) =>
      @enriched_postcomp R C A X Y g) _).
  move=> g g'.
  change
    (metric_hom_sup_dist (@enriched_postcomp R C A X Y g)
       (@enriched_postcomp R C A X Y g') <= dist g g')%E.
  apply: ge_ereal_sup => y.
  move=> [ox _ <-].
  case: ox => [f|] /=.
  - have H := metric_hom_nexp
      (@e_comp (@MetAddMonoidal R) C A X Y) (g, f) (g', f).
    by rewrite /= dist_refl adde0 in H.
  - exact: dist_ge0.
Defined.

Definition enriched_representable {R : realType}
    (C : EnrichedCategory (@MetAddMonoidal R)) (A : e_obj C) :
    EnrichedFunctor C (MetSelfEnriched R).
Proof.
  refine (@Build_EnrichedFunctor (@MetAddMonoidal R)
    C (MetSelfEnriched R)
    (fun X => e_hom A X)
    (fun X Y => @enriched_postcomp_hom R C A X Y) _ _).
  - move=> X.
    apply Metric_hom_ext => u.
    case: u.
    apply Metric_hom_ext => f.
    have H := @e_comp_id_l (@MetAddMonoidal R) C A X.
    have Hpoint := congr1
      (fun k : Metric_hom
          (met_add_t_obj met_t_unit (e_hom A X)) (e_hom A X) =>
        metric_hom_fun k (tt, f)) H.
    cbn in Hpoint |-.
    exact Hpoint.
  - move=> X Y Z.
    apply Metric_hom_ext => gf.
    case: gf => g f.
    apply Metric_hom_ext => h.
    have H := @e_comp_assoc (@MetAddMonoidal R) C Z A X Y.
    have Hpoint := congr1
      (fun k : Metric_hom
          (met_add_t_obj
            (met_add_t_obj (e_hom Y Z) (e_hom X Y))
            (e_hom A X))
          (e_hom A Z) =>
        metric_hom_fun k ((g, f), h)) H.
    cbn in Hpoint |-.
    exact Hpoint.
Defined.
