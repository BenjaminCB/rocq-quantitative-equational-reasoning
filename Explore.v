(* Broad environment for interactive Search, Check, About, and Print queries.
   This file is intentionally excluded from _CoqProject. *)

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
