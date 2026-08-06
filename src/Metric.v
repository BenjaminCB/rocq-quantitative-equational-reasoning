(* ============================================================
   MathComp Analysis backend for quantitative metric structure

   This file provides the MathComp Analysis infrastructure shared by
   the extended-real-indexed quantitative equations and their induced
   metrics.
   ============================================================ *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool choice fintype.
From mathcomp Require Import order ssralg ssrnum archimedean finmap reals ereal.
From mathcomp Require Import classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

(* ============================================================
   Section 3: Quantitative Algebras (metric infrastructure)
   ============================================================ *)

(** Extended non-negative real-valued metric space, using MathComp's
    extended reals [\bar R].  This is the library-backed version of
    paper Definition 3.1's metric component. *)
Record ext_metric_space (R : realType) := {
  carrier : Type;
  dist : carrier -> carrier -> \bar R;
  dist_ge0 : forall a b, 0 <= dist a b;
  dist_refl : forall a, dist a a = 0;
  dist_eq0 : forall a b, dist a b = 0 -> a = b;
  dist_symm : forall a b, dist a b = dist b a;
  dist_tri : forall a b c,
    dist a c <= dist a b + dist b c;
}.

Definition dist_le {R : realType} (M : ext_metric_space R)
    (a b : carrier M) (eps : \bar R) : Prop :=
  dist a b <= eps.

Definition algebra_ops {R : realType} (Sym : Type) (arity : Sym -> nat)
    (M : ext_metric_space R) : Type :=
  forall f : Sym, (ordinal (arity f) -> carrier M) -> carrier M.

Definition non_expansive {R : realType} {Sym : Type} {arity : Sym -> nat}
    (M : ext_metric_space R) (ops : algebra_ops arity M) : Prop :=
  forall f (xs ys : ordinal (arity f) -> carrier M) (eps : \bar R),
    (0 <= eps)%E ->
    (forall i, dist_le (xs i) (ys i) eps) ->
    dist_le (ops f xs) (ops f ys) eps.

(** The set of extended-real bounds associated to a proof-indexed
    family.  For quantitative equations the index type is the
    non-negative part of [\bar R] and [embed] is its first projection. *)
Definition bound_set {R : realType} {I : Type}
    (embed : I -> \bar R) (P : I -> Prop) : set (\bar R) :=
  [set r | exists i, P i /\ r = embed i].

Definition extended_infimum {R : realType} {I : Type}
    (embed : I -> \bar R) (P : I -> Prop) : \bar R :=
  ereal_inf (bound_set embed P).

Definition has_bound_infimum {R : realType} {I : Type}
    (embed : I -> \bar R) (P : I -> Prop) (r : \bar R) : Prop :=
  r = extended_infimum embed P.

Definition finite_support {T : choiceType} : Type := {fset T}.
