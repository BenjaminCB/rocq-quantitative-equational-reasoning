(* ============================================================
   Quantitative Algebraic Reasoning, MathComp-style core

   This is a parallel rewrite of the core of QET.v.  It avoids
   Vector.t and the Stdlib-Reals metric layer, using:
   - MathComp seq for finite contexts,
   - ordinal-indexed operation arguments,
   - MathComp Analysis extended reals through MCMetric.v.
   ============================================================ *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Lists.List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp Require Import all_classical reals ereal.
From Template Require Import MCMetric.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ereal_scope.

Notation Qnn q := (0 <= q)%R.

Lemma Qnn_add : forall p q : rat, Qnn p -> Qnn q -> Qnn (p + q).
Proof. exact: addr_ge0. Qed.

Lemma Qnn_zero : Qnn (0 : rat).
Proof. exact: lexx. Qed.

(* ============================================================
   Signatures and terms
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

Fixpoint subst_term {sig X} (sigma : X -> term sig X)
    (t : term sig X) : term sig X :=
  match t with
  | Var x => sigma x
  | App f args => App f (fun i => subst_term sigma (args i))
  end.

Definition subst_comp {sig X}
    (sigma tau : X -> term sig X) : X -> term sig X :=
  fun x => subst_term sigma (tau x).

Lemma subst_term_comp {sig X}
    (sigma tau : X -> term sig X) (t : term sig X) :
  subst_term sigma (subst_term tau t) = subst_term (subst_comp sigma tau) t.
Proof.
  elim: t => [x | f args IH] //=.
  congr App.
  apply functional_extensionality => i.
  exact: IH.
Qed.

(* ============================================================
   Quantitative equations and deduction
   ============================================================ *)

Record qeq (sig : signature) (X : Type) := {
  lhs : term sig X;
  rhs : term sig X;
  eps : rat;
}.

Notation "t ~[ e ] s" := {| lhs := t; rhs := s; eps := e |}
  (at level 70, no associativity).

Definition subst_qeq {sig X}
    (sigma : X -> term sig X) (q : qeq sig X) : qeq sig X :=
  {| lhs := subst_term sigma (lhs q);
     rhs := subst_term sigma (rhs q);
     eps := eps q |}.

Definition ctx sig X := seq (qeq sig X).

Definition subst_ctx {sig X}
    (sigma : X -> term sig X) (Gamma : ctx sig X) : ctx sig X :=
  map (subst_qeq sigma) Gamma.

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
      Qnn eps -> (0 < eps')%R ->
      Gamma |- (t ~[eps] s) ->
      Gamma |- (t ~[eps + eps'] s)
  | D_EpsEq : forall Gamma t s eps delta,
      eps = delta ->
      Gamma |- (t ~[eps] s) ->
      Gamma |- (t ~[delta] s)
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
  - move=> psi Hpsi. by inversion Hpsi.
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
  | DS_EpsEq : forall Gamma t s eps delta,
      eps = delta ->
      derives_S S Gamma (t ~[eps] s) ->
      derives_S S Gamma (t ~[delta] s)
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

Definition qe_theory {sig X} (S : axiom_set sig X) : axiom_set sig X :=
  fun Gamma phi => derives_S S Gamma phi.

Definition inconsistent {sig X} (U : axiom_set sig X) : Prop :=
  exists x y : X, x <> y /\ U [::] (Var x ~[0] Var y).

Definition consistent {sig X} (U : axiom_set sig X) : Prop :=
  ~ inconsistent U.

(* ============================================================
   MathComp-backed quantitative algebras and semantics
   ============================================================ *)

Record QAlgebra (R : realType) (sig : signature) := {
  qa_metric : ext_metric_space R;
  qa_ops : @mc_algebra_ops R (sym sig) (@arity sig) qa_metric;
  qa_nexp : @mc_non_expansive R (sym sig) (@arity sig) qa_metric qa_ops;
}.

Definition qa_carrier {R sig} (A : QAlgebra R sig) :=
  mc_carrier (qa_metric A).

Definition degenerate {R sig} (A : QAlgebra R sig) : Prop :=
  forall a b : qa_carrier A, a = b.

Record QAlgHom {R sig} (A B : QAlgebra R sig) := {
  hom_fun : qa_carrier A -> qa_carrier B;
  hom_nexp : forall a b,
    @mc_dist R (qa_metric B) (hom_fun a) (hom_fun b) <=
    @mc_dist R (qa_metric A) a b;
  hom_compat : forall f (v : 'I_(@arity sig f) -> qa_carrier A),
    hom_fun (@qa_ops R sig A f v) =
    @qa_ops R sig B f (fun i => hom_fun (v i));
}.

Fixpoint eval {R sig X} (A : QAlgebra R sig)
    (rho : X -> qa_carrier A) (t : term sig X) : qa_carrier A :=
  match t with
  | Var x => rho x
  | App f args => @qa_ops R sig A f (fun i => @eval R sig X A rho (args i))
  end.

Lemma eval_subst {R sig X} (A : QAlgebra R sig)
    (rho : X -> qa_carrier A) (sigma : X -> term sig X) t :
  @eval R sig X A rho (subst_term sigma t) =
  @eval R sig X A (fun x => @eval R sig X A rho (sigma x)) t.
Proof.
  elim: t => [x | f args IH] //=.
  congr (@qa_ops R sig A f _).
  apply functional_extensionality => i.
  exact: IH.
Qed.

Definition qdist_le {R : realType} {sig X} (embed : rat -> R) (A : QAlgebra R sig)
    (rho : X -> qa_carrier A) (phi : qeq sig X) : Prop :=
  @mc_dist_le R (qa_metric A)
    (@eval R sig X A rho (lhs phi)) (@eval R sig X A rho (rhs phi))
    (embed (eps phi)).

Definition satisfies_inf {R : realType} {sig X} (embed : rat -> R) (A : QAlgebra R sig)
    (Gamma : ctx sig X) (phi : qeq sig X) : Prop :=
  forall rho,
    (forall h, List.In h Gamma -> @qdist_le R sig X embed A rho h) ->
    @qdist_le R sig X embed A rho phi.

Definition models {R : realType} {sig X} (embed : rat -> R)
    (A : QAlgebra R sig) (U : axiom_set sig X) : Prop :=
  forall Gamma phi, U Gamma phi -> @satisfies_inf R sig X embed A Gamma phi.

Definition provable_eps {sig X} (U : axiom_set sig X)
    (s t : term sig X) : rat -> Prop :=
  fun eps => derives_S U [::] (s ~[eps] t).

Definition d_U {R : realType} {sig X} (embed : rat -> R) (U : axiom_set sig X)
    (s t : term sig X) : \bar R :=
  extended_infimum embed (provable_eps U s t).
