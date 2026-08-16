(* ============================================================
   Deduction over fuzzy relations
   ============================================================ *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssralg ssrnum reals fintype.

From Template Require Import Signature FuzzyRelation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** Apply a term substitution to either form of judgment. *)
Definition subst_judgement {R : realType} {sig X Y}
    (sigma : X -> term sig Y) (phi : @judgement R sig X) :
    @judgement R sig Y :=
  match phi with
  | EqJ s t => EqJ (subst_term sigma s) (subst_term sigma t)
  | QEqJ eps s t =>
      QEqJ eps (subst_term sigma s) (subst_term sigma t)
  end.

(** The mode is an index of the derivation relation.  Only the full mode has
    an order-completeness constructor. *)
Inductive frel_derivation_mode :=
  | FRelFinite
  | FRelFull.

(** The finitary rules are shared by both modes.  Quantitative reflexivity,
    symmetry, transitivity, and operation nonexpansiveness are deliberately
    absent because an arbitrary fuzzy relation need not satisfy them. *)
Inductive frel_derives {R : realType} {sig : signature}
    (E : fuzzy_theory R sig) :
    frel_derivation_mode ->
    forall X : fuzzy_space R,
      @judgement R sig (fcarrier X) -> Prop :=
  | FD_Init : forall mode X phi,
      E X phi ->
      frel_derives E mode phi
  | FD_EqRefl : forall mode X (s : term sig (fcarrier X)),
      frel_derives E mode (EqJ s s)
  | FD_EqSym : forall mode X (s t : term sig (fcarrier X)),
      frel_derives E mode (EqJ s t) ->
      frel_derives E mode (EqJ t s)
  | FD_EqTrans : forall mode X (s t u : term sig (fcarrier X)),
      frel_derives E mode (EqJ s t) ->
      frel_derives E mode (EqJ t u) ->
      frel_derives E mode (EqJ s u)
  | FD_EqCong : forall mode X (f : sym sig)
      (s t : 'I_(arity f) -> term sig (fcarrier X)),
      (forall i, frel_derives E mode  ( EqJ (s i) (t i) ) ) ->
      frel_derives E mode (EqJ (App f s) (App f t))
  | FD_UseVariables : forall mode X (x y : fcarrier X),
      frel_derives E mode
        (QEqJ (frel X x y) (Var x) (Var y))
  | FD_Subst : forall mode X Y phi
      (sigma : fcarrier X -> term sig (fcarrier Y)),
      @frel_derives R sig E mode X phi ->
      (forall x y,
        @frel_derives R sig E mode Y
          (@QEqJ R sig (fcarrier Y) (frel X x y)
            (sigma x) (sigma y))) ->
      @frel_derives R sig E mode Y (subst_judgement sigma phi)
  | FD_QEqReplaceL : forall mode X eps
      (s t u : term sig (fcarrier X)),
      frel_derives E mode (EqJ s t) ->
      frel_derives E mode (QEqJ eps t u) ->
      frel_derives E mode (QEqJ eps s u)
  | FD_QEqReplaceR : forall mode X eps
      (s t u : term sig (fcarrier X)),
      frel_derives E mode (QEqJ eps s t) ->
      frel_derives E mode (EqJ t u) ->
      frel_derives E mode (QEqJ eps s u)
  | FD_Up : forall mode X eps delta
      (s t : term sig (fcarrier X)),
      (eps <= delta)%R ->
      frel_derives E mode (QEqJ eps s t) ->
      frel_derives E mode (QEqJ delta s t)
  | FD_Max : forall mode X (s t : term sig (fcarrier X)),
      frel_derives E mode
        (QEqJ 1 s t)
  | FD_OrderComplete : forall X eps (s t : term sig (fcarrier X)),
      (forall delta, (eps < delta)%R ->
        frel_derives E FRelFull (QEqJ delta s t)) ->
      frel_derives E FRelFull (QEqJ eps s t).

Definition derives_fin {R : realType} {sig : signature}
    (E : fuzzy_theory R sig) (X : fuzzy_space R)
    (phi : @judgement R sig (fcarrier X)) : Prop :=
  frel_derives E FRelFinite phi.

Definition derives_full {R : realType} {sig : signature}
    (E : fuzzy_theory R sig) (X : fuzzy_space R)
    (phi : @judgement R sig (fcarrier X)) : Prop :=
  frel_derives E FRelFull phi.

Lemma derives_fin_to_full
    {R : realType} {sig : signature}
    (E : fuzzy_theory R sig)
    (X : fuzzy_space R)
    (phi : @judgement R sig (fcarrier X)) :
  derives_fin E phi ->
  derives_full E phi.
Proof.
  rewrite /derives_fin /derives_full.
  move => H.
  induction H; eauto using frel_derives.
Qed. 

Definition fuzzy_theory_incl
    {R : realType} {sig : signature}
    (E F : fuzzy_theory R sig) : Prop :=
  forall (X : fuzzy_space R)
    (phi : @judgement R sig (fcarrier X)),
    E X phi -> F X phi.

Lemma frel_derives_weakening
    {R : realType} {sig : signature}
    (E F : fuzzy_theory R sig)
    (mode : frel_derivation_mode)
    (X : fuzzy_space R)
    (phi : @judgement R sig (fcarrier X)) :
  fuzzy_theory_incl E F ->
  frel_derives E mode phi ->
  frel_derives F mode phi.
Proof.
  rewrite /fuzzy_theory_incl.
  move => Hincl H.
  induction H.
  - apply: FD_Init.
    apply: Hincl.
    exact: H.
  all: eauto using frel_derives.
Qed. 

(** Replace each use of an [E]-axiom by an [F]-derivation. *)
Lemma frel_derives_cut
    {R : realType} {sig : signature}
    (E F : fuzzy_theory R sig)
    (mode : frel_derivation_mode)
    (X : fuzzy_space R)
    (phi : @judgement R sig (fcarrier X)) :
  (forall (Y : fuzzy_space R)
    (psi : @judgement R sig (fcarrier Y)),
    E Y psi -> frel_derives F mode psi) ->
  frel_derives E mode phi ->
  frel_derives F mode phi.
Proof.
  move => Hcut Hderive.
  induction Hderive.
  - apply: Hcut X phi H.
  all: eauto using frel_derives.
Qed.

(** Semantic substitution.  The quantitative premises say that
    evaluating [sigma] under any interpretation produces a nonexpansive map
    out of [X]. *)
Lemma satisfies_subst
    {R : realType} {sig : signature}
    (A : FuzzyAlgebra R sig)
    (X Y : fuzzy_space R)
    (sigma : fcarrier X -> term sig (fcarrier Y))
    (phi : @judgement R sig (fcarrier X)) :
  satisfies A X phi ->
  (forall x y,
    satisfies A Y
      (@QEqJ R sig (fcarrier Y) (frel X x y) (sigma x) (sigma y))) ->
  satisfies A Y (subst_judgement sigma phi).
Admitted.

(** Soundness of the calculus without order completeness. *)
Theorem derives_fin_sound
    {R : realType} {sig : signature}
    (A : FuzzyAlgebra R sig)
    (E : fuzzy_theory R sig)
    (X : fuzzy_space R)
    (phi : @judgement R sig (fcarrier X)) :
  fuzzy_models A E ->
  @derives_fin R sig E X phi ->
  satisfies A X phi.
Admitted.

(** A scalar is below [eps] when it is below every strict upper
    approximation of [eps]. *)
Lemma le_of_all_strict_upper_bounds
    {R : realType} (a eps : R) :
  (forall delta, (eps < delta)%R -> (a <= delta)%R) ->
  (a <= eps)%R.
Admitted.

(** Soundness of the full calculus.  Its additional induction
    case uses [le_of_all_strict_upper_bounds]. *)
Theorem derives_full_sound
    {R : realType} {sig : signature}
    (A : FuzzyAlgebra R sig)
    (E : fuzzy_theory R sig)
    (X : fuzzy_space R)
    (phi : @judgement R sig (fcarrier X)) :
  fuzzy_models A E ->
  @derives_full R sig E X phi ->
  satisfies A X phi.
Admitted.
