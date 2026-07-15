(* ============================================================
   Quantitative equational theories as enriched Lawvere theories
   ============================================================ *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Lists.List.
From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp Require Import all_classical reals ereal.

From Template Require Import Metric Category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

Notation Qnn q := (0 <= q)%R.

Lemma Qnn_add : forall p q : rat, Qnn p -> Qnn q -> Qnn (p + q).
Proof. apply: addr_ge0. Qed.

Lemma Qnn_zero : Qnn (0 : rat).
Proof. apply: lexx. Qed.

Definition nnrat := {q : rat | Qnn q}.

Definition nnrat_val (eps : nnrat) : rat := sval eps.

Definition nnrat_embed (R : realType) (eps : nnrat) : R :=
  ratr (nnrat_val eps).

Lemma nnrat_embed_ge0 (R : realType) (eps : nnrat) :
  (0 <= nnrat_embed R eps)%R.
Proof.
  case: eps => eps Heps.
  by rewrite /nnrat_embed /nnrat_val /= ler0q.
Qed.

(* ============================================================
   Signatures, terms, and substitution
   ============================================================ *)

Record signature := {
  sym : Type;
  arity : sym -> nat;
}.

Inductive term (sig : signature) (X : Type) : Type :=
  | Var : X -> term sig X
  | App : forall f : sym sig, ('I_(arity f) -> term sig X) -> term sig X.

Arguments Var {sig X} _.
Arguments App {sig X} _ _.

Fixpoint subst_term {sig X Y} (sigma : X -> term sig Y)
    (t : term sig X) : term sig Y :=
  match t with
  | Var x => sigma x
  | App f args => App f (subst_term sigma \o args)
  end.

Definition subst_comp {sig X Y Z}
    (sigma : Y -> term sig Z) (tau : X -> term sig Y) :
    X -> term sig Z :=
  subst_term sigma \o tau.

Lemma subst_term_comp {sig X Y Z}
    (sigma : Y -> term sig Z) (tau : X -> term sig Y)
    (t : term sig X) :
  subst_term sigma (subst_term tau t) = subst_term (subst_comp sigma tau) t.
Proof.
  elim: t => [x | f args IH] //=.
  congr App.
  apply functional_extensionality => i.
  apply: IH.
Qed.

Lemma subst_term_var {sig X} (t : term sig X) :
  subst_term Var t = t.
Proof.
  elim: t => [x | f args IH] //=.
  congr App.
  apply functional_extensionality => i.
  exact: IH.
Qed.

(* ============================================================
   Quantitative equations and axiom schemes
   ============================================================ *)

Record qeq (sig : signature) (X : Type) := {
  lhs : term sig X;
  rhs : term sig X;
  eps : rat;
}.

Notation "t ~[ e ] s" := {| lhs := t; rhs := s; eps := e |}
  (at level 70, no associativity).

Definition subst_qeq {sig X Y}
    (sigma : X -> term sig Y) (q : qeq sig X) : qeq sig Y :=
  {| lhs := subst_term sigma (lhs q);
     rhs := subst_term sigma (rhs q);
     eps := eps q |}.

Definition ctx sig X := seq (qeq sig X).

Definition subst_ctx {sig X Y}
    (sigma : X -> term sig Y) : ctx sig X -> ctx sig Y :=
  map (subst_qeq sigma).

Definition axiom_scheme (sig : signature) :=
  forall (X : Type), ctx sig X -> qeq sig X -> Prop.

Inductive derives {sig} (U : axiom_scheme sig)
    : forall X : Type, ctx sig X -> qeq sig X -> Prop :=
  | D_Refl : forall X Gamma t,
      @derives sig U X Gamma (t ~[0] t)
  | D_Symm : forall X Gamma t s eps,
      Qnn eps ->
      @derives sig U X Gamma (t ~[eps] s) ->
      @derives sig U X Gamma (s ~[eps] t)
  | D_Triang : forall X Gamma t s u eps eps',
      Qnn eps -> Qnn eps' ->
      @derives sig U X Gamma (t ~[eps] s) ->
      @derives sig U X Gamma (s ~[eps'] u) ->
      @derives sig U X Gamma (t ~[eps + eps'] u)
  | D_Max : forall X Gamma t s eps eps',
      Qnn eps -> (0 < eps')%R ->
      @derives sig U X Gamma (t ~[eps] s) ->
      @derives sig U X Gamma (t ~[eps + eps'] s)
  | D_Arch : forall X Gamma t s eps,
      Qnn eps ->
      (forall eps', (eps < eps')%R ->
        @derives sig U X Gamma (t ~[eps'] s)) ->
      @derives sig U X Gamma (t ~[eps] s)
  | D_NExp : forall X Gamma (f : sym sig)
                     (ts ss : 'I_(arity f) -> term sig X) eps,
      Qnn eps ->
      (forall i, @derives sig U X Gamma (ts i ~[eps] ss i)) ->
      @derives sig U X Gamma (App f ts ~[eps] App f ss)
  | D_Subst : forall X Y Gamma t s eps
                       (sigma : X -> term sig Y),
      @derives sig U X Gamma (t ~[eps] s) ->
      @derives sig U Y (subst_ctx sigma Gamma)
        (subst_term sigma t ~[eps] subst_term sigma s)
  | D_Cut : forall X Gamma Gamma' phi,
      (forall psi, List.In psi Gamma' -> @derives sig U X Gamma psi) ->
      @derives sig U X Gamma' phi ->
      @derives sig U X Gamma phi
  | D_Assumpt : forall X Gamma phi,
      List.In phi Gamma ->
      @derives sig U X Gamma phi
  | D_Axiom : forall X Gamma phi,
      U X Gamma phi -> @derives sig U X Gamma phi.

Arguments D_Refl {sig U X Gamma} t.
Arguments D_Symm {sig U X Gamma t s eps} _ _.
Arguments D_Triang {sig U X Gamma t s u eps eps'} _ _ _ _.
Arguments D_NExp {sig U X Gamma f ts ss eps} _ _.
Arguments D_Subst {sig U X Y Gamma t s eps} sigma _.
Arguments D_Axiom {sig U X Gamma phi} _.

Lemma subst_term_nexp {sig X Y} (U : axiom_scheme sig)
    (eps : rat) (sigma tau : X -> term sig Y) (t : term sig X) :
  Qnn eps ->
  (forall x, @derives sig U Y [::] (sigma x ~[eps] tau x)) ->
  @derives sig U Y [::] (subst_term sigma t ~[eps] subst_term tau t).
Proof.
  move=> Heps Hvars.
  elim: t => [x | f args IH] //=.
  apply: D_NExp; first exact Heps.
  move=> i.
  exact: IH.
Qed.

(* ============================================================
   The Induced Pseudometric
   ============================================================ *)

Definition d_U {R : realType} {sig X} (U : axiom_scheme sig)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nnrat_embed R) (
    fun eps => derives U [::] (s ~[nnrat_val eps] t)
  ).

Definition gamma_U {R : realType} {sig X} (U : axiom_scheme sig)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nnrat_embed R) (
    fun eps => forall Gamma, derives U Gamma (s ~[nnrat_val eps] t)
  ).

Definition delta_U {R : realType} {sig X} (U : axiom_scheme sig)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nnrat_embed R) (
    fun eps => exists Gamma, derives U Gamma (s ~[nnrat_val eps] t)
  ).

Lemma delta_U_context_witness {sig X} (U : axiom_scheme sig)
    (s t : term sig X) (eps : nnrat) :
  exists Gamma, derives U Gamma (s ~[nnrat_val eps] t).
Proof.
  exists [:: s ~[nnrat_val eps] t].
  apply: D_Assumpt.
  by left.
Qed.

Proposition delta_U_zero {R : realType} {sig X}
    (U : axiom_scheme sig) (s t : term sig X) :
  @delta_U R sig X U s t = 0.
Proof.
  apply: Order.POrderTheory.le_anti.
  rewrite /delta_U /extended_infimum.
  apply/andP; split.
  - apply: ge_ereal_inf.
    exists (0%:E : \bar R); [ | apply lexx].
    exists (0 : R)%R; [ | by []].
    exists (exist _ (0 : rat) Qnn_zero).
    split.
    + apply: delta_U_context_witness.
    + rewrite /nnrat_embed /=.
      symmetry.
      apply: (ratr_nat R 0).
  - rewrite /delta_U /extended_infimum.
    have Hlb :
        (0%R <= ereal_inf
          (EFin @` bound_set (@nnrat_embed R)
            (fun eps : nnrat =>
              exists Gamma : ctx sig X,
                derives U Gamma (s ~[nnrat_val eps] t))))%E.
    { apply/ereal_infP => y Himg.
      case: Himg => r Hb <-.
      case: Hb => eps [_ Hr].
      rewrite Hr.
      apply: lee_tofin.
      exact: nnrat_embed_ge0.
    }
    exact Hlb.
Qed.

Lemma derives_empty_cut {sig X} (U : axiom_scheme sig)
    (Gamma : ctx sig X) phi :
  derives U [::] phi -> derives U Gamma phi.
Proof.
  move=> H.
  apply: (D_Cut (Gamma' := [::])).
  - move=> psi Hpsi. inversion Hpsi.
  - exact H.
Qed.

Proposition gamma_U_eq_d_U {R : realType} {sig X}
    (U : axiom_scheme sig) (s t : term sig X) :
  @gamma_U R sig X U s t = @d_U R sig X U s t.
Proof.
  rewrite /gamma_U /d_U /extended_infimum /bound_set.
  congr ereal_inf.
  apply/seteqP; split=> r.
  - move=> H.
    case: H => x Hbound Hfin.
    move: Hbound => [eps [Hderive Hx]].
    exists x.
    + exists eps; split.
      * exact: (Hderive [::]).
      * exact Hx.
    + exact Hfin.
  - move=> H.
    case: H => x Hbound Hfin.
    move: Hbound => [eps [Hderive Hx]].
    exists x.
    + exists eps; split.
      * move=> Gamma.
        exact: derives_empty_cut Hderive.
      * exact Hx.
    + exact Hfin.
Qed.

(* ============================================================
   Ordinary Lawvere category of a signature
   ============================================================ *)

Definition lawvere_op (sig : signature) (n m : nat) : Type :=
  'I_m -> term sig 'I_n.

Definition lawvere_id (sig : signature) (n : nat) : lawvere_op sig n n :=
  fun i => Var i.

Definition lawvere_comp (sig : signature) {n m k : nat}
    (g : lawvere_op sig m k) (f : lawvere_op sig n m) :
    lawvere_op sig n k :=
  fun i => subst_term f (g i).

Definition LawvereCategory (sig : signature) : Category.
Proof.
  refine {|
    obj := nat;
    hom := lawvere_op sig;
    id := lawvere_id sig;
    comp := fun _ _ _ => @lawvere_comp sig _ _ _
  |}.
  - move=> W X Y Z h g f.
    apply functional_extensionality => i /=.
    symmetry.
    exact: subst_term_comp.
  - move=> X Y f.
    apply functional_extensionality => i /=.
    reflexivity.
  - move=> X Y f.
    apply functional_extensionality => i /=.
    exact: subst_term_var.
Defined.

(* ============================================================
   Quantitative spaces and their additive tensor
   ============================================================ *)

Record QuantitativeSpace := {
  qs_carrier : Type;
  qs_rel : rat -> qs_carrier -> qs_carrier -> Prop;
  qs_refl : forall x, qs_rel 0 x x;
  qs_symm : forall eps x y, qs_rel eps x y -> qs_rel eps y x;
  qs_tri : forall eps eps' x y z,
    qs_rel eps x y -> qs_rel eps' y z -> qs_rel (eps + eps') x z;
}.

Record QSpaceHom (A B : QuantitativeSpace) := {
  qs_hom_fun : qs_carrier A -> qs_carrier B;
  qs_hom_nexp : forall eps x y,
    @qs_rel A eps x y ->
    @qs_rel B eps (qs_hom_fun x) (qs_hom_fun y);
}.

Arguments qs_hom_fun {A B} _ _.
Arguments qs_hom_nexp {A B} _ {eps x y} _.

Lemma QSpaceHom_ext {A B : QuantitativeSpace} (f g : QSpaceHom A B) :
  (forall x, qs_hom_fun f x = qs_hom_fun g x) -> f = g.
Proof.
  case: f => ff f_nexp.
  case: g => gf g_nexp.
  move=> /= Hfg.
  have Hfun : ff = gf by apply functional_extensionality.
  case: gf / Hfun in g_nexp Hfg *.
  f_equal.
  apply proof_irrelevance.
Qed.

Definition QSpaceHom_id (A : QuantitativeSpace) : QSpaceHom A A.
Proof.
  refine {| qs_hom_fun := fun x => x |}.
  move=> eps x y Hxy.
  exact Hxy.
Defined.

Definition QSpaceHom_comp {A B C : QuantitativeSpace}
    (g : QSpaceHom B C) (f : QSpaceHom A B) : QSpaceHom A C.
Proof.
  refine {| qs_hom_fun := fun x => qs_hom_fun g (qs_hom_fun f x) |}.
  move=> eps x y Hxy.
  apply: qs_hom_nexp.
  exact: qs_hom_nexp.
Defined.

Definition QSpaceCat : Category.
Proof.
  refine {|
    obj := QuantitativeSpace;
    hom := QSpaceHom;
    id := QSpaceHom_id;
    comp := fun _ _ _ => @QSpaceHom_comp _ _ _
  |}.
  - move=> W X Y Z h g f.
    apply QSpaceHom_ext => x.
    reflexivity.
  - move=> X Y f.
    apply QSpaceHom_ext => x.
    reflexivity.
  - move=> X Y f.
    apply QSpaceHom_ext => x.
    reflexivity.
Defined.

Definition qspace_tensor_rel (A B : QuantitativeSpace)
    (eps : rat) (xy xy' : qs_carrier A * qs_carrier B) : Prop :=
  exists epsA : rat, exists epsB : rat,
    eps = (epsA + epsB)%R /\
    @qs_rel A epsA (fst xy) (fst xy') /\
    @qs_rel B epsB (snd xy) (snd xy').

Definition qspace_tensor (A B : QuantitativeSpace) : QuantitativeSpace.
Proof.
  refine {|
    qs_carrier := qs_carrier A * qs_carrier B;
    qs_rel := @qspace_tensor_rel A B
  |}.
  - move=> [x y].
    exists (0 : rat), (0 : rat).
    split; first by rewrite addr0.
    split; exact: qs_refl.
  - move=> eps [x y] [x' y'] [epsA [epsB [-> [Hx Hy]]]].
    exists epsA, epsB.
    split; first reflexivity.
    split; exact: qs_symm.
  - move=> eps eps' [x y] [x' y'] [x'' y''].
    move=> [epsA [epsB [-> [Hx Hy]]]].
    move=> [epsA' [epsB' [-> [Hx' Hy']]]].
    exists (epsA + epsA')%R, (epsB + epsB')%R.
    split; first by rewrite addrACA.
    split.
    + exact: (qs_tri Hx Hx').
    + exact: (qs_tri Hy Hy').
Defined.

Definition qspace_unit : QuantitativeSpace.
Proof.
  refine {|
    qs_carrier := unit;
    qs_rel := fun eps _ _ => eps = (0 : rat)
  |}.
  - move=> [].
    reflexivity.
  - move=> eps [] [] H.
    exact H.
  - move=> eps eps' [] [] [] -> ->.
    by rewrite addr0.
Defined.

Definition qspace_tensor_hom {A B C D : QuantitativeSpace}
    (f : QSpaceHom A C) (g : QSpaceHom B D) :
    QSpaceHom (qspace_tensor A B) (qspace_tensor C D).
Proof.
  refine (@Build_QSpaceHom (qspace_tensor A B) (qspace_tensor C D)
    (fun xy : qs_carrier (qspace_tensor A B) =>
      (qs_hom_fun f (fst xy), qs_hom_fun g (snd xy))) _).
  move=> eps [x y] [x' y'] [epsA [epsB [Heps [Hx Hy]]]].
  exists epsA, epsB.
  split; first exact Heps.
  split.
  - exact: qs_hom_nexp Hx.
  - exact: qs_hom_nexp Hy.
Defined.

Definition qspace_assoc (A B C : QuantitativeSpace) :
    QSpaceHom (qspace_tensor (qspace_tensor A B) C)
              (qspace_tensor A (qspace_tensor B C)).
Proof.
  refine (@Build_QSpaceHom
    (qspace_tensor (qspace_tensor A B) C)
    (qspace_tensor A (qspace_tensor B C))
    (fun xyz : qs_carrier (qspace_tensor (qspace_tensor A B) C) =>
      (fst (fst xyz), (snd (fst xyz), snd xyz))) _).
  move=> eps [[x y] z] [[x' y'] z'].
  move=> [epsAB [epsC [-> [[epsA [epsB [-> [Hx Hy]]]] Hz]]]].
  exists epsA, (epsB + epsC)%R.
  split; first by rewrite addrA.
  split; first exact Hx.
  exists epsB, epsC.
  split; first reflexivity.
  split; assumption.
Defined.

Definition qspace_assoc_inv (A B C : QuantitativeSpace) :
    QSpaceHom (qspace_tensor A (qspace_tensor B C))
              (qspace_tensor (qspace_tensor A B) C).
Proof.
  refine (@Build_QSpaceHom
    (qspace_tensor A (qspace_tensor B C))
    (qspace_tensor (qspace_tensor A B) C)
    (fun xyz : qs_carrier (qspace_tensor A (qspace_tensor B C)) =>
      ((fst xyz, fst (snd xyz)), snd (snd xyz))) _).
  move=> eps [x [y z]] [x' [y' z']].
  move=> [epsA [epsBC [-> [Hx [epsB [epsC [-> [Hy Hz]]]]]]]].
  exists (epsA + epsB)%R, epsC.
  split; first by rewrite addrA.
  split; last exact Hz.
  exists epsA, epsB.
  split; first reflexivity.
  split; assumption.
Defined.

Definition qspace_left_unitor (A : QuantitativeSpace) :
    QSpaceHom (qspace_tensor qspace_unit A) A.
Proof.
  refine (@Build_QSpaceHom (qspace_tensor qspace_unit A) A
    (fun ux : qs_carrier (qspace_tensor qspace_unit A) => snd ux) _).
  move=> eps [[] x] [[] x'] [epsU [epsA [-> [-> Hx]]]].
  by rewrite add0r.
Defined.

Definition qspace_left_unitor_inv (A : QuantitativeSpace) :
    QSpaceHom A (qspace_tensor qspace_unit A).
Proof.
  refine (@Build_QSpaceHom A (qspace_tensor qspace_unit A)
    (fun x : qs_carrier A => (tt, x)) _).
  move=> eps x x' Hx.
  exists (0 : rat), eps.
  split; first by rewrite add0r.
  split; first reflexivity.
  exact Hx.
Defined.

Definition qspace_right_unitor (A : QuantitativeSpace) :
    QSpaceHom (qspace_tensor A qspace_unit) A.
Proof.
  refine (@Build_QSpaceHom (qspace_tensor A qspace_unit) A
    (fun xu : qs_carrier (qspace_tensor A qspace_unit) => fst xu) _).
  move=> eps [x []] [x' []] [epsA [epsU [-> [Hx ->]]]].
  by rewrite addr0.
Defined.

Definition qspace_right_unitor_inv (A : QuantitativeSpace) :
    QSpaceHom A (qspace_tensor A qspace_unit).
Proof.
  refine (@Build_QSpaceHom A (qspace_tensor A qspace_unit)
    (fun x : qs_carrier A => (x, tt)) _).
  move=> eps x x' Hx.
  exists eps, (0 : rat).
  split; first by rewrite addr0.
  split; last reflexivity.
  exact Hx.
Defined.

Definition QSpaceMonoidal : MonoidalCategory.
Proof.
  refine {|
    mon_cat := QSpaceCat;
    t_obj := qspace_tensor;
    t_hom := fun _ _ _ _ => qspace_tensor_hom;
    t_unit := qspace_unit;
    t_assoc := qspace_assoc;
    t_assoc_inv := qspace_assoc_inv;
    t_left_unitor := qspace_left_unitor;
    t_left_unitor_inv := qspace_left_unitor_inv;
    t_right_unitor := qspace_right_unitor;
    t_right_unitor_inv := qspace_right_unitor_inv
  |}.
Defined.

(* ============================================================
   Quantitative Lawvere theories
   ============================================================ *)

Record QuantitativeLawvereTheory := {
  qlt_sig : signature;
  qlt_rule : axiom_scheme qlt_sig;
}.

Arguments qlt_sig _ : clear implicits.
Arguments qlt_rule _ : clear implicits.

Definition qlt_derives (U : QuantitativeLawvereTheory) (X : Type) :
    ctx (qlt_sig U) X -> qeq (qlt_sig U) X -> Prop :=
  @derives (qlt_sig U) (qlt_rule U) X.

Definition qlt_op (U : QuantitativeLawvereTheory) (n m : nat) : Type :=
  lawvere_op (qlt_sig U) n m.

Definition qlt_id (U : QuantitativeLawvereTheory) (n : nat) :
    qlt_op U n n :=
  @lawvere_id (qlt_sig U) n.

Definition qlt_comp (U : QuantitativeLawvereTheory) {n m k : nat}
    (g : qlt_op U m k) (f : qlt_op U n m) : qlt_op U n k :=
  @lawvere_comp (qlt_sig U) n m k g f.

Definition qlt_arrow_rel (U : QuantitativeLawvereTheory)
    (n m : nat) (eps : rat) (f g : qlt_op U n m) : Prop :=
  Qnn eps /\
  forall i, @qlt_derives U 'I_n [::] (f i ~[eps] g i).

Definition qlt_hom_object (U : QuantitativeLawvereTheory)
    (n m : nat) : QuantitativeSpace.
Proof.
  refine {|
    qs_carrier := qlt_op U n m;
    qs_rel := @qlt_arrow_rel U n m
  |}.
  - move=> f.
    split; first exact: Qnn_zero.
    move=> i.
    exact: D_Refl.
  - move=> eps f g [Heps Hfg].
    split; first exact Heps.
    move=> i.
    exact: (D_Symm Heps (Hfg i)).
  - move=> eps eps' f g h [Heps Hfg] [Heps' Hgh].
    split; first exact: Qnn_add.
    move=> i.
    exact: (D_Triang Heps Heps' (Hfg i) (Hgh i)).
Defined.

Definition qlt_id_hom (U : QuantitativeLawvereTheory) (n : nat) :
    QSpaceHom qspace_unit (qlt_hom_object U n n).
Proof.
  refine (@Build_QSpaceHom qspace_unit (qlt_hom_object U n n)
    (fun _ : qs_carrier qspace_unit => @qlt_id U n) _).
  move=> eps [] [] ->.
  apply: qs_refl.
Defined.

Definition qlt_comp_hom (U : QuantitativeLawvereTheory)
    (n m k : nat) :
    QSpaceHom
      (qspace_tensor (qlt_hom_object U m k) (qlt_hom_object U n m))
      (qlt_hom_object U n k).
Proof.
  refine (@Build_QSpaceHom
    (qspace_tensor (qlt_hom_object U m k) (qlt_hom_object U n m))
    (qlt_hom_object U n k)
    (fun gf : qs_carrier
        (qspace_tensor (qlt_hom_object U m k) (qlt_hom_object U n m)) =>
      @qlt_comp U n m k (fst gf) (snd gf)) _).
  move=> eps [g f] [g' f'].
  move=> [eps_g [eps_f [-> [[Hg_nn Hg] [Hf_nn Hf]]]]].
  split; first exact: Qnn_add.
  move=> i /=.
  apply: (D_Triang Hg_nn Hf_nn).
  - exact: (D_Subst f (Hg i)).
  - apply: subst_term_nexp; first exact Hf_nn.
    exact Hf.
Defined.

Definition EnrichedLawvereCategory (U : QuantitativeLawvereTheory) :
    EnrichedCategory QSpaceMonoidal.
Proof.
  exact (@Build_EnrichedCategory QSpaceMonoidal
    nat (qlt_hom_object U) (qlt_id_hom U) (qlt_comp_hom U)).
Defined.
