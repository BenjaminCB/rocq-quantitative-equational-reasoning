Require Import Coq.Vectors.Vector.
Import VectorNotations.
Require Import QArith.
Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.

Record signature := {
  sym: Type;
  arity: sym -> nat;
}.

Inductive term (sig : signature) (X : Type) : Type :=
  | Var : X -> term sig X
  | App : forall (f : sym sig),
    Vector.t (term sig X) (arity sig f) -> term sig X.

Arguments Var {sig X} _.
Arguments App {sig X} _ _.

Definition subst (sig : signature) (X : Type) := 
  X -> term sig X.

Fixpoint subst_term {sig X} (subst : X -> term sig X) (t : term sig X) :=
  match t with
  | Var x => subst x
  | App f v => App f (Vector.map (subst_term subst) v)
  end.

Definition Qpos := { q : Q | 0 <= q }.
Definition mkQpos (q : Q) (H : 0 <= q) : Qpos := exist _ q H.

Record qeq (sig : signature) (X : Type) := {
  lhs : term sig X;
  rhs : term sig X;
  eps : Q; (* we use this for now it needs to be the positive rationals later *)
}.

Definition subst_qeq {sig X} (subst : X -> term sig X) (q : qeq sig X) : qeq sig X :=
  {| 
    lhs := subst_term subst (lhs q);
    rhs := subst_term subst (rhs q);
    eps := eps q;
  |}.

Notation "x ~[ e ] y" := {| lhs := x; rhs := y; eps := e |} (at level 71).

(* the order of a list will probably come back to bite me *)
Definition context sig X := list (qeq sig X).

Reserved Notation "ctx |- phi" (at level 72).

Inductive derives (sig : signature) (X : Type)
  : context sig X -> qeq sig X -> Prop :=
  | Refl : forall ctx t, ctx |- t ~[0] t
  | Symm : forall ctx t s eps, 
    In (t ~[eps] s) ctx -> 
    ctx |- s ~[eps] t
  | Triang : forall ctx t s u eps eps',
    In (t ~[eps] s) ctx ->
    In (s ~[eps'] u) ctx ->
    ctx |- t ~[eps + eps'] u
  | Max : forall ctx t s eps eps',
    0 < eps' ->
    In (t ~[eps] s) ctx ->
    ctx |- t ~[eps + eps'] s
  | Arch : forall ctx t s eps,
    (forall eps', eps < eps' -> In (t ~[eps'] s) ctx) ->
    ctx |- t ~[eps] s
  | NExp : forall ctx f (ts ss : Vector.t (term sig X) (arity sig f)) eps,
    (forall i, In (Vector.nth ts i ~[eps] Vector.nth ss i) ctx) ->
    ctx |- App f ts ~[eps] App f ss
  | Subst : forall ctx t s eps subst,
    ctx |- t ~[eps] s ->
    (map (subst_qeq subst) ctx) |- subst_term subst t ~[eps] subst_term subst s
  | Cut : forall ctx ctx' phi,
    (forall psi, In psi ctx' -> ctx |- psi) ->
    ctx' |- phi ->
    ctx |- phi
  | Assumpt : forall ctx phi, In phi ctx -> ctx |- phi

  where "ctx |- phi" := (derives ctx phi).

Definition theory sig X := context sig X -> qeq sig X -> Prop.




    