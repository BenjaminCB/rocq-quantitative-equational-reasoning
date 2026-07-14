(* ============================================================
   Quantitative Algebraic Reasoning, MathComp-style core

   This is a parallel rewrite of the core of QET.v.  It avoids
   Vector.t and the Stdlib-Reals metric layer, using:
   - MathComp seq for finite contexts,
   - ordinal-indexed operation arguments,
   - MathComp Analysis extended reals through Metric.v.
   ============================================================ *)

(* ============================================================
   Section 2: Quantitative Equational Theories
   ============================================================ *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Lists.List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat all_algebra.

(* add non constructive axioms *)
From mathcomp Require Import all_classical reals ereal.

From Template Require Import Metric Category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ereal_scope.

Notation Qnn q := (0 <= q)%R.

Lemma Qnn_add : forall p q : rat, Qnn p -> Qnn q -> Qnn (p + q).
Proof. apply: addr_ge0. Qed.

Lemma Qnn_zero : Qnn (0 : rat).
Proof. apply: lexx. Qed.

(* ============================================================
   Section 2.1: Signatures and terms
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

(* ============================================================
   Section 2.2: Quantitative equations and deduction rules
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

Reserved Notation "Gamma '|-' phi" (at level 72).

Inductive derives (sig : signature) (X : Type)
    : ctx sig X -> qeq sig X -> Prop :=
  | D_Refl : forall Gamma t,
      Gamma |- (t ~[0] t)
  | D_Symm : forall Gamma t s eps,
      Qnn eps ->
      Gamma |- (t ~[eps] s) ->
      Gamma |- (s ~[eps] t)
  | D_Triang : forall Gamma t s u eps eps',
      Qnn eps -> Qnn eps' ->
      Gamma |- (t ~[eps] s) ->
      Gamma |- (s ~[eps'] u) ->
      Gamma |- (t ~[eps + eps'] u)
  | D_Max : forall Gamma t s eps eps',
      Qnn eps -> 
      (0 < eps')%R ->
      Gamma |- (t ~[eps] s) ->
      Gamma |- (t ~[eps + eps'] s)
  | D_Arch : forall Gamma t s eps,
      Qnn eps ->
      (forall eps', (eps < eps')%R -> Gamma |- (t ~[eps'] s)) ->
      Gamma |- (t ~[eps] s)
  | D_NExp : forall Gamma (f : sym sig)
                    (ts ss : 'I_(arity f) -> term sig X) eps,
      Qnn eps ->
      (forall i, Gamma |- (ts i ~[eps] ss i)) ->
      Gamma |- (App f ts ~[eps] App f ss)
  | D_Subst : forall Gamma t s eps (sigma : X -> term sig X),
      Gamma |- (t ~[eps] s) ->
      subst_ctx sigma Gamma |- (subst_term sigma t ~[eps] subst_term sigma s)
  | D_Cut : forall Gamma Gamma' phi,
      (forall psi, List.In psi Gamma' -> Gamma |- psi) ->
      Gamma' |- phi ->
      Gamma |- phi
  | D_Assumpt : forall Gamma phi,
      List.In phi Gamma ->
      Gamma |- phi
  where "Gamma '|-' phi" := (derives Gamma phi).

Lemma derives_weaken {sig X} (Gamma Gamma' : ctx sig X) phi :
  (forall psi, List.In psi Gamma -> List.In psi Gamma') ->
  Gamma |- phi ->
  Gamma' |- phi.
Proof.
  move=> Hsub Hder.
  apply: (D_Cut (Gamma' := Gamma)).
  - move=> psi Hpsi. exact: D_Assumpt (Hsub _ Hpsi).
  - exact Hder.
Qed.

Lemma derives_empty_cut {sig X} (Gamma : ctx sig X) phi :
  [::] |- phi -> Gamma |- phi.
Proof.
  move=> H.
  apply: (D_Cut (Gamma' := [::])).
  - move => psi Hpsi. inversion Hpsi.
  - exact H.
Qed.

Definition axiom_set (sig : signature) (X : Type) :=
  ctx sig X -> qeq sig X -> Prop.

Inductive derives_S {sig X} (S : axiom_set sig X)
    : ctx sig X -> qeq sig X -> Prop :=
  | DS_Refl : forall Gamma t,
      derives_S S Gamma (t ~[0] t)
  | DS_Symm : forall Gamma t s eps,
      Qnn eps ->
      derives_S S Gamma (t ~[eps] s) ->
      derives_S S Gamma (s ~[eps] t)
  | DS_Triang : forall Gamma t s u eps eps',
      Qnn eps -> Qnn eps' ->
      derives_S S Gamma (t ~[eps] s) ->
      derives_S S Gamma (s ~[eps'] u) ->
      derives_S S Gamma (t ~[eps + eps'] u)
  | DS_Max : forall Gamma t s eps eps',
      Qnn eps -> (0 < eps')%R ->
      derives_S S Gamma (t ~[eps] s) ->
      derives_S S Gamma (t ~[eps + eps'] s)
  | DS_Arch : forall Gamma t s eps,
      Qnn eps ->
      (forall eps', (eps < eps')%R -> derives_S S Gamma (t ~[eps'] s)) ->
      derives_S S Gamma (t ~[eps] s)
  | DS_NExp : forall Gamma (f : sym sig)
                     (ts ss : 'I_(arity f) -> term sig X) eps,
      Qnn eps ->
      (forall i, derives_S S Gamma (ts i ~[eps] ss i)) ->
      derives_S S Gamma (App f ts ~[eps] App f ss)
  | DS_Subst : forall Gamma t s eps (sigma : X -> term sig X),
      derives_S S Gamma (t ~[eps] s) ->
      derives_S S (subst_ctx sigma Gamma)
        (subst_term sigma t ~[eps] subst_term sigma s)
  | DS_Cut : forall Gamma Gamma' phi,
      (forall psi, List.In psi Gamma' -> derives_S S Gamma psi) ->
      derives_S S Gamma' phi ->
      derives_S S Gamma phi
  | DS_Assumpt : forall Gamma phi,
      List.In phi Gamma ->
      derives_S S Gamma phi
  | DS_Axiom : forall Gamma phi,
      S Gamma phi -> derives_S S Gamma phi.

Lemma derives_S_empty_cut {sig X} (S : axiom_set sig X)
    (Gamma : ctx sig X) phi :
  derives_S S [::] phi -> derives_S S Gamma phi.
Proof.
  move=> H.
  apply: (DS_Cut (Gamma' := [::])).
  - move=> psi Hpsi. inversion Hpsi.
  - exact H.
Qed.

Definition axiom_scheme (sig : signature) :=
  forall X : Type, axiom_set sig X.

Inductive derives_scheme {sig} (S : axiom_scheme sig)
    : forall X : Type, ctx sig X -> qeq sig X -> Prop :=
  | DSS_Refl : forall X Gamma t,
      @derives_scheme sig S X Gamma (t ~[0] t)
  | DSS_Symm : forall X Gamma t s eps,
      Qnn eps ->
      @derives_scheme sig S X Gamma (t ~[eps] s) ->
      @derives_scheme sig S X Gamma (s ~[eps] t)
  | DSS_Triang : forall X Gamma t s u eps eps',
      Qnn eps -> Qnn eps' ->
      @derives_scheme sig S X Gamma (t ~[eps] s) ->
      @derives_scheme sig S X Gamma (s ~[eps'] u) ->
      @derives_scheme sig S X Gamma (t ~[eps + eps'] u)
  | DSS_Max : forall X Gamma t s eps eps',
      Qnn eps -> (0 < eps')%R ->
      @derives_scheme sig S X Gamma (t ~[eps] s) ->
      @derives_scheme sig S X Gamma (t ~[eps + eps'] s)
  | DSS_Arch : forall X Gamma t s eps,
      Qnn eps ->
      (forall eps', (eps < eps')%R ->
        @derives_scheme sig S X Gamma (t ~[eps'] s)) ->
      @derives_scheme sig S X Gamma (t ~[eps] s)
  | DSS_NExp : forall X Gamma (f : sym sig)
                     (ts ss : 'I_(arity f) -> term sig X) eps,
      Qnn eps ->
      (forall i, @derives_scheme sig S X Gamma (ts i ~[eps] ss i)) ->
      @derives_scheme sig S X Gamma (App f ts ~[eps] App f ss)
  | DSS_Subst : forall X Y Gamma t s eps
                       (sigma : X -> term sig Y),
      @derives_scheme sig S X Gamma (t ~[eps] s) ->
      @derives_scheme sig S Y (subst_ctx sigma Gamma)
        (subst_term sigma t ~[eps] subst_term sigma s)
  | DSS_Cut : forall X Gamma Gamma' phi,
      (forall psi, List.In psi Gamma' -> @derives_scheme sig S X Gamma psi) ->
      @derives_scheme sig S X Gamma' phi ->
      @derives_scheme sig S X Gamma phi
  | DSS_Assumpt : forall X Gamma phi,
      List.In phi Gamma ->
      @derives_scheme sig S X Gamma phi
  | DSS_Axiom : forall X Gamma phi,
      S X Gamma phi -> @derives_scheme sig S X Gamma phi.

Arguments DSS_Refl {sig S X Gamma} t.
Arguments DSS_Symm {sig S X Gamma t s eps} _ _.
Arguments DSS_Triang {sig S X Gamma t s u eps eps'} _ _ _ _.
Arguments DSS_NExp {sig S X Gamma f ts ss eps} _ _.
Arguments DSS_Subst {sig S X Y Gamma t s eps} sigma _.
Arguments DSS_Axiom {sig S X Gamma phi} _.

Definition qe_theory {sig X} (S : axiom_set sig X) : axiom_set sig X := 
  derives_S S.

Definition inconsistent {sig X} (S : axiom_set sig X) : Prop :=
  exists x y : X, x <> y /\ S [::] (Var x ~[0] Var y).

Definition consistent {sig X} (S : axiom_set sig X) : Prop :=
  ~ inconsistent S.

(* ============================================================
   Section 3: Quantitative Algebras
   ============================================================ *)

(* QAlgebra definitions and related structures *)

Record QAlgebra (R : realType) (sig : signature) := {
  qa_metric : ext_metric_space R;
  qa_ops : algebra_ops (@arity sig) qa_metric;
  qa_nexp : non_expansive qa_ops;
}.

Definition qa_carrier {R sig} (A : QAlgebra R sig) :=
  carrier (qa_metric A).

Definition degenerate {R sig} (A : QAlgebra R sig) : Prop :=
  forall a b : qa_carrier A, a = b.

Record QAlgHom {R sig} (A B : QAlgebra R sig) := {
  hom_fun : qa_carrier A -> qa_carrier B;
  hom_nexp : forall a b,
    dist (hom_fun a) (hom_fun b) <=
    dist a b;
  hom_compat : forall f (v : 'I_(@arity sig f) -> qa_carrier A),
    hom_fun (qa_ops v) =
    qa_ops (fun i => hom_fun (v i));
}.

Fixpoint eval {R sig X} (A : QAlgebra R sig)
    (rho : X -> qa_carrier A) (t : term sig X) : qa_carrier A :=
  match t with
  | Var x => rho x
  | App f args => qa_ops (fun i => @eval R sig X A rho (args i))
  end.

Lemma eval_subst {R sig X Y} (A : QAlgebra R sig)
    (rho : Y -> qa_carrier A) (sigma : X -> term sig Y) t :
  eval rho (subst_term sigma t) =
  eval (eval rho \o sigma) t.
Proof.
  elim: t => [x | f args IH] //=.
  congr (qa_ops _).
  apply functional_extensionality => i.
  exact: IH.
Qed.

(* ============================================================
   Section 4: Algebraic Semantics for Quantitative Equations
   ============================================================ *)

Definition qdist_le {R : realType} {sig X} (A : QAlgebra R sig)
    (rho : X -> qa_carrier A) (phi : qeq sig X) : Prop :=
  dist_le 
    (eval rho (lhs phi)) 
    (eval rho (rhs phi))
    (ratr (eps phi)).

Definition satisfies_inf {R : realType} {sig X} 
    (A : QAlgebra R sig)
    (Gamma : ctx sig X) 
    (phi : qeq sig X) : Prop :=
  forall rho,
    (forall psi, List.In psi Gamma -> @qdist_le R sig X A rho psi) ->
    @qdist_le R sig X A rho phi.

Definition models {R : realType} {sig X}
    (A : QAlgebra R sig) (S : axiom_set sig X) : Prop :=
  forall Gamma phi, S Gamma phi -> satisfies_inf A Gamma phi.

Definition nnrat : Type := {eps : rat | Qnn eps}.

Definition nnrat_val (eps : nnrat) : rat := proj1_sig eps.

Definition nnrat_embed {R : realType} : nnrat -> R :=
  ratr \o nnrat_val.

Lemma nnrat_embed_ge0 {R : realType} :
  forall eps, Qnn (@nnrat_embed R eps).
Proof.
  move => [eps Heps] /=.
  by rewrite ler0q.
Qed.

(* ============================================================
   Section 5: The Induced Pseudometric
   ============================================================ *)

Definition d_U {R : realType} {sig X} (U : axiom_set sig X)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nnrat_embed R) (
    fun eps => derives_S U [::] (s ~[nnrat_val eps] t)
  ).

Definition gamma_U {R : realType} {sig X} (U : axiom_set sig X)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nnrat_embed R) (
    fun eps => forall Gamma, derives_S U Gamma (s ~[nnrat_val eps] t)
  ).

Definition delta_U {R : realType} {sig X} (U : axiom_set sig X)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nnrat_embed R) (
    fun eps => exists Gamma, derives_S U Gamma (s ~[nnrat_val eps] t)
  ).

Lemma delta_U_context_witness {sig X} (U : axiom_set sig X)
    (s t : term sig X) (eps : nnrat) :
  exists Gamma, derives_S U Gamma (s ~[nnrat_val eps] t).
Proof.
  exists [:: s ~[nnrat_val eps] t].
  apply: DS_Assumpt.
  by left.
Qed.

Proposition delta_U_zero {R : realType} {sig X}
    (U : axiom_set sig X) (s t : term sig X) :
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
                derives_S U Gamma (s ~[nnrat_val eps] t))))%E.
    { apply/ereal_infP => y Himg.
      case: Himg => r Hb <-.
      case: Hb => eps [_ Hr].
      rewrite Hr.
      apply: lee_tofin.
      exact: nnrat_embed_ge0.
    }
    exact Hlb.
Qed.

Proposition gamma_U_eq_d_U {R : realType} {sig X}
    (U : axiom_set sig X) (s t : term sig X) :
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
        exact: derives_S_empty_cut Hderive.
      * exact Hx.
    + exact Hfin.
Qed.

(* ============================================================
   Metric-enriched Lawvere theories
   ============================================================ *)

Definition lawvere_op (sig : signature) (n m : nat) : Type :=
  'I_m -> term sig 'I_n.

Definition lawvere_id (sig : signature) (n : nat) : lawvere_op sig n n :=
  fun i => Var i.

Definition lawvere_comp (sig : signature) {n m k : nat}
    (g : lawvere_op sig m k) (f : lawvere_op sig n m) :
    lawvere_op sig n k :=
  fun i => subst_term f (g i).

Lemma subst_term_var {sig X} (t : term sig X) :
  subst_term Var t = t.
Proof.
  elim: t => [x | f args IH] //=.
  congr App.
  apply functional_extensionality => i.
  exact: IH.
Qed.

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

Record QuantitativeLawvereTheory := {
  qlt_sig : signature;
  qlt_rule : axiom_scheme qlt_sig;
}.

Arguments qlt_sig _ : clear implicits.
Arguments qlt_rule _ : clear implicits.

Definition qlt_derives (U : QuantitativeLawvereTheory) (X : Type) :
    ctx (qlt_sig U) X -> qeq (qlt_sig U) X -> Prop :=
  @derives_scheme (qlt_sig U) (qlt_rule U) X.

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

Lemma subst_term_nexp {sig X} (U : axiom_set sig X)
    (eps : rat) (sigma tau : X -> term sig X) (t : term sig X) :
  Qnn eps ->
  (forall x, derives_S U [::] (sigma x ~[eps] tau x)) ->
  derives_S U [::] (subst_term sigma t ~[eps] subst_term tau t).
Proof.
  move=> Heps Hvars.
  elim: t => [x | f args IH] //=.
  apply: DS_NExp; first exact Heps.
  move=> i.
  exact: IH.
Qed.

Lemma subst_term_scheme_nexp {sig X Y} (S : axiom_scheme sig)
    (eps : rat) (sigma tau : X -> term sig Y) (t : term sig X) :
  Qnn eps ->
  (forall x, @derives_scheme sig S Y [::] (sigma x ~[eps] tau x)) ->
  @derives_scheme sig S Y [::] (subst_term sigma t ~[eps] subst_term tau t).
Proof.
  move=> Heps Hvars.
  elim: t => [x | f args IH] //=.
  apply: DSS_NExp; first exact Heps.
  move=> i.
  exact: IH.
Qed.

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
    exact: DSS_Refl.
  - move=> eps f g [Heps Hfg].
    split; first exact Heps.
    move=> i.
    exact: (DSS_Symm Heps (Hfg i)).
  - move=> eps eps' f g h [Heps Hfg] [Heps' Hgh].
    split; first exact: Qnn_add.
    move=> i.
    exact: (DSS_Triang Heps Heps' (Hfg i) (Hgh i)).
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
  apply: (DSS_Triang Hg_nn Hf_nn).
  - exact: (DSS_Subst f (Hg i)).
  - apply: subst_term_scheme_nexp; first exact Hf_nn.
    exact Hf.
Defined.

Definition EnrichedLawvereCategory (U : QuantitativeLawvereTheory) :
    EnrichedCategory QSpaceMonoidal.
Proof.
  exact (@Build_EnrichedCategory QSpaceMonoidal
    nat (qlt_hom_object U) (qlt_id_hom U) (qlt_comp_hom U)).
Defined.

(* ============================================================
   QAlgebra-specific categorical infrastructure
   ============================================================ *)

Definition same_hom {R sig} {A B : QAlgebra R sig}
    (h k : QAlgHom A B) : Prop :=
  forall a, hom_fun h a = hom_fun k a.

Definition QAlgHom_id {R sig} (A : QAlgebra R sig) : QAlgHom A A.
Proof.
  refine {| hom_fun := fun a => a |}.
  - move=> a b. exact: lexx.
  - move=> f v. reflexivity.
Defined.

Definition QAlgHom_comp {R sig} {A B C : QAlgebra R sig}
    (g : QAlgHom B C) (h : QAlgHom A B) : QAlgHom A C.
Proof.
  refine {| hom_fun := fun a => hom_fun g (hom_fun h a) |}.
  - move=> a b.
    exact: (le_trans (hom_nexp g (hom_fun h a) (hom_fun h b)) (hom_nexp h a b)).
  - move=> f v /=.
    rewrite !hom_compat.
    reflexivity.
Defined.

Record QSubAlgebra {R sig} (A B : QAlgebra R sig) := {
  sub_embed : qa_carrier B -> qa_carrier A;
  sub_isom : forall b b',
    dist (sub_embed b) (sub_embed b') =
    dist b b';
  sub_closed : forall f (v : 'I_(arity f) -> qa_carrier B),
    sub_embed (qa_ops v) =
    qa_ops (fun i => sub_embed (v i));
}.

Record QAlgSubcategory (R : realType) (sig : signature) := {
  K_obj : QAlgebra R sig -> Prop;
  K_hom : forall {A B : QAlgebra R sig}, QAlgHom A B -> Prop;
  K_hom_dom : forall {A B} (h : QAlgHom A B), K_hom h -> K_obj A;
  K_hom_cod : forall {A B} (h : QAlgHom A B), K_hom h -> K_obj B;
  K_id : forall A, K_obj A -> K_hom (QAlgHom_id A);
  K_comp : forall {A B C} (g : QAlgHom B C) (h : QAlgHom A B),
    K_hom g -> K_hom h -> K_hom (QAlgHom_comp g h);
}.

Definition initial_in {R sig} (K : QAlgSubcategory R sig)
    (A : QAlgebra R sig) : Prop :=
  K_obj K A /\
  forall B, K_obj K B ->
    exists h : QAlgHom A B,
      K_hom K h /\
      forall k : QAlgHom A B, K_hom K k -> same_hom k h.

Record FunctorFromQAlgSubcat {R sig}
    (K : QAlgSubcategory R sig) (C : Category) := {
  fobj : QAlgebra R sig -> obj C;
  fmap : forall {A B : QAlgebra R sig} (h : QAlgHom A B)
      (Hh : K_hom K h),
    hom (fobj A) (fobj B);
}.

Notation "f <$> e" := (fmap f e)
  (at level 40, left associativity).

Definition universal_morphism {R sig} {C : Category}
    {K : QAlgSubcategory R sig}
    (G : FunctorFromQAlgSubcat K C)
    (C0 : obj C)
    (A : QAlgebra R sig) (HA : K_obj K A)
    (alpha : hom C0 (fobj G A)) : Prop :=
  forall (B : QAlgebra R sig) (HB : K_obj K B)
         (beta : hom C0 (fobj G B)),
    exists h : QAlgHom A B,
      forall (Hh : K_hom K h),
        (G <$> Hh) <| alpha = beta /\
        forall (k : QAlgHom A B) (Hk : K_hom K k),
          (G <$> Hk) <| alpha = beta -> same_hom k h.

Definition has_universal_mapping_property {R sig} {C : Category}
    {K : QAlgSubcategory R sig}
    (G : FunctorFromQAlgSubcat K C)
    (C0 : obj C)
    (A : QAlgebra R sig) (HA : K_obj K A) : Prop :=
  exists alpha : hom C0 (fobj G A),
    @universal_morphism R sig C K G C0 A HA alpha.

Definition eq_class {R : realType} {sig X}
    (U : axiom_set sig X) (A : QAlgebra R sig) : Prop :=
  models A U.

Lemma eq_class_subalgebra {R : realType} {sig X}
    (U : axiom_set sig X) (A B : QAlgebra R sig) :
  QSubAlgebra A B ->
  eq_class U A ->
  eq_class U B.
Proof.
  move => [emb iso_e closed] HA Gamma phi HU rho Hhyp.
  set rhoA := emb \o rho.
  have eval_embed : forall t,
      eval rhoA t = emb (eval rho t).
  { elim => [x | f args IH] //=.
    rewrite closed.
    congr qa_ops; apply functional_extensionality => i.
    by apply IH.
  }
  have HhypA : forall h, List.In h Gamma ->
      @qdist_le R sig X A rhoA h.
  { move => h Hh.
    rewrite /qdist_le /dist_le.
    rewrite !eval_embed iso_e.
    by apply (Hhyp h Hh).
  }
  move: (HA Gamma phi HU rhoA HhypA).
  rewrite /qdist_le /dist_le.
  rewrite !eval_embed iso_e.
  by [].
Qed.

(* ============================================================
   Section 7: Free Quantitative Algebras
   ============================================================ *)

(* Induced term pseudometric properties - continuation of Section 5 *)

Section InducedMetric.

  Context {sig : signature} {X : Type} (U : axiom_set sig X).

  Definition term_equiv (s t : term sig X) : Prop :=
    derives_S U [::] (s ~[(0 : rat)] t).

  Lemma term_equiv_refl : forall t, term_equiv t t.
  Proof. exact: DS_Refl. Qed.

  Lemma term_equiv_symm : forall s t, term_equiv s t -> term_equiv t s.
  Proof. move => s t H. exact: (DS_Symm Qnn_zero H). Qed.

  Lemma term_equiv_trans : forall s t u,
      term_equiv s t -> term_equiv t u -> term_equiv s u.
  Proof.
    move => s t u Hst Htu.
    exact: DS_Triang Qnn_zero Qnn_zero Hst Htu.
  Qed.

End InducedMetric.

(* Free algebra constructions - main content of Section 7 *)

Section FreeAlgebra.

  Context {sig : signature} {X : Type} (U : axiom_set sig X).

  Definition free_carrier := term sig X.

  Definition free_dist (s t : free_carrier) : rat -> Prop :=
    fun eps => derives_S U [::] (s ~[eps] t).

  Lemma free_dist_zero_refl : forall t, free_dist t t (0 : rat).
  Proof. by apply DS_Refl. Qed.

  Lemma free_dist_symm : forall s t eps,
      Qnn eps -> free_dist s t eps -> free_dist t s eps.
  Proof. move=> s t eps Heps H. apply (DS_Symm Heps H). Qed.

  Lemma free_dist_tri : forall s t u eps eps',
      Qnn eps -> Qnn eps' ->
      free_dist s t eps -> free_dist t u eps' ->
      free_dist s u (eps + eps').
  Proof.
    move=> s t u eps eps' Heps Heps' Hst Htu.
    apply: (DS_Triang Heps Heps' Hst Htu).
  Qed.

  Lemma free_ops_nexp :
    forall (f : sym sig) (ts ss : 'I_(arity f) -> term sig X) eps,
    Qnn eps ->
    (forall i, free_dist (ts i) (ss i) eps) ->
    free_dist (App f ts) (App f ss) eps.
  Proof.
    move=> f ts ss eps Heps Hcomp.
    apply: (DS_NExp Heps Hcomp).
  Qed.

  Lemma free_equiv_congruence :
    forall (f : sym sig) (xs ys : 'I_(arity f) -> term sig X),
    (forall i, term_equiv U (xs i) (ys i)) ->
    term_equiv U (App f xs) (App f ys).
  Proof.
    move=> f xs ys H.
    apply: (DS_NExp Qnn_zero H).
  Qed.

  Theorem free_algebra_is_model :
    forall (Gamma : ctx sig X) (phi : qeq sig X),
    U Gamma phi ->
    forall (sigma : X -> term sig X),
    (forall h, List.In h Gamma ->
      free_dist (subst_term sigma (lhs h))
                (subst_term sigma (rhs h))
                (eps h)) ->
    free_dist (subst_term sigma (lhs phi))
              (subst_term sigma (rhs phi))
              (eps phi).
  Proof.
    move=> Gamma [phi_lhs phi_rhs phi_eps] HU sigma Hhyp /=.
    rewrite /free_dist.
    apply: (DS_Cut (Gamma' := subst_ctx sigma Gamma)).
    - move=> psi Hpsi.
      rewrite /subst_ctx in Hpsi.
      move/List.in_map_iff: Hpsi => [h [<- Hh]].
      apply: (Hhyp h Hh).
    - apply: (@DS_Subst sig X U Gamma phi_lhs phi_rhs phi_eps sigma
        (@DS_Axiom sig X U Gamma (phi_lhs ~[phi_eps] phi_rhs) HU)).
  Qed.

End FreeAlgebra.
