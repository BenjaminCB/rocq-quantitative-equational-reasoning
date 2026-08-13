From mathcomp Require Import ssrbool ssralg ssrnum reals.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq choice fintype.
From Stdlib Require Import Logic.FunctionalExtensionality.

From Template Require Import Signature.

Set Implicit Arguments.

Local Open Scope ring_scope.

Record fuzzy_space (R : realType) := {
    fcarrier : Type;
    frel : fcarrier -> fcarrier -> R;
    frel_range :
      forall x y, (0 <= frel x y <= 1)%R;
}.

Definition frel_nonexpansive {R : realType}
    (A B : fuzzy_space R)
    (f : fcarrier A -> fcarrier B) : Prop :=
  forall x y,
    (frel B (f x) (f y) <= frel A x y)%R.

Record FuzzyAlgebra (R : realType) (sig : signature) := {
  fa_space : fuzzy_space R;
  fa_ops : algebra_ops sig (fcarrier fa_space)
}.

Inductive judgement {R : realType} (sig : signature) (X : Type) :=
  | EqJ : term sig X -> term sig X -> judgement sig X
  | QEqJ : R -> term sig X -> term sig X -> judgement sig X.

Record interpretation {R : realType} {sig : signature}
    (X : fuzzy_space R) (A : FuzzyAlgebra R sig) := {
  interpretation_fun :> fcarrier X -> fcarrier (fa_space A);

  interpretation_nexp :
    frel_nonexpansive X (fa_space A) interpretation_fun;
}.

Fixpoint fuzzy_eval {R : realType} {sig X}
    (A : FuzzyAlgebra R sig)
    (rho : X -> fcarrier (fa_space A))
    (t : term sig X) : fcarrier (fa_space A) :=
  match t with
  | Var x => rho x
  | App f args => fa_ops A f (fun i => fuzzy_eval A rho (args i))
  end.

Definition satisfies {R : realType} {sig}
    (A : FuzzyAlgebra R sig)
    (X : fuzzy_space R)
    (phi : judgement sig (fcarrier X)) : Prop :=
  forall rho : interpretation X A,
    match phi with
    | EqJ s t => fuzzy_eval A rho s = fuzzy_eval A rho t
    | QEqJ eps s t => 
      (frel (fa_space A)
        (fuzzy_eval A rho s)
        (fuzzy_eval A rho t) <= eps)%R
    end.

Lemma fuzzy_eval_subst
    {R : realType} {sig : signature}
    {X Y : Type}
    (A : FuzzyAlgebra R sig)
    (rho : Y -> fcarrier (fa_space A))
    (sigma : X -> term sig Y)
    (t : term sig X) :
  fuzzy_eval A rho (subst_term sigma t) =
  fuzzy_eval A
    (fun x => fuzzy_eval A rho (sigma x))
    t.
Proof.
  induction t; first by [].
  rewrite //=.
  apply f_equal.
  apply functional_extensionality.
  apply H.
Qed.