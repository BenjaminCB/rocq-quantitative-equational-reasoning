(* ============================================================
   Signatures, terms, and substitution
   ============================================================ *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record signature := {
  sym : Type;
  arity : sym -> nat;
}.

Inductive term (sig : signature) (X : Type) : Type :=
  | Var : X -> term sig X
  | App : forall f : sym sig, ('I_(arity f) -> term sig X) -> term sig X.

Arguments Var {sig X} _.
Arguments App {sig X} _ _.

Definition algebra_ops (sig : signature) (A : Type) : Type :=
  forall f : sym sig, (ordinal (arity f) -> A) -> A.

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
