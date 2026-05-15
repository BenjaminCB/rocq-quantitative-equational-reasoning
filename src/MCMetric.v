(* ============================================================
   MathComp Analysis backend for quantitative metric structure

   This file intentionally keeps MathComp Analysis imports separate
   from QET.v.  The main development currently uses Stdlib Reals and
   QArith notations; importing MathComp Analysis globally there causes
   notation conflicts.  This backend is the target infrastructure for
   the metric/infimum parts of the full formalization.
   ============================================================ *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat all_algebra finmap.
From mathcomp Require Import all_classical reals ereal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

(** Extended non-negative real-valued metric space, using MathComp's
    extended reals [\bar R].  This is the library-backed version of
    paper Definition 3.1's metric component. *)
Record ext_metric_space (R : realType) := {
  mc_carrier : Type;
  mc_dist : mc_carrier -> mc_carrier -> \bar R;
  mc_dist_ge0 : forall a b, 0 <= mc_dist a b;
  mc_dist_refl : forall a, mc_dist a a = 0;
  mc_dist_eq0 : forall a b, mc_dist a b = 0 -> a = b;
  mc_dist_symm : forall a b, mc_dist a b = mc_dist b a;
  mc_dist_tri : forall a b c,
    mc_dist a c <= mc_dist a b + mc_dist b c;
}.

Definition mc_dist_le {R : realType} (M : ext_metric_space R)
    (a b : mc_carrier M) (eps : R) : Prop :=
  @mc_dist R M a b <= eps%:E.

Definition mc_algebra_ops {R : realType} (Sym : Type) (arity : Sym -> nat)
    (M : ext_metric_space R) : Type :=
  forall f : Sym, (ordinal (arity f) -> mc_carrier M) -> mc_carrier M.

Definition mc_non_expansive {R : realType} {Sym : Type} {arity : Sym -> nat}
    (M : ext_metric_space R) (ops : mc_algebra_ops arity M) : Prop :=
  forall f (xs ys : ordinal (arity f) -> mc_carrier M) (eps : R),
    (0 <= eps)%R ->
    (forall i, @mc_dist_le R M (xs i) (ys i) eps) ->
    @mc_dist_le R M (ops f xs) (ops f ys) eps.

(** The set of real bounds associated to a proof-indexed family of
    bounds.  Later, the QET rational bound relation can be transported
    here by choosing an embedding [Q -> R]. *)
Definition bound_set {R : realType} {I : Type}
    (embed : I -> R) (P : I -> Prop) : set R :=
  [set r | exists i, P i /\ r = embed i].

Definition extended_infimum {R : realType} {I : Type}
    (embed : I -> R) (P : I -> Prop) : \bar R :=
  ereal_inf (EFin @` bound_set embed P).

Definition has_bound_infimum {R : realType} {I : Type}
    (embed : I -> R) (P : I -> Prop) (r : \bar R) : Prop :=
  r = extended_infimum embed P.

Definition finite_support {T : choiceType} : Type := {fset T}.
