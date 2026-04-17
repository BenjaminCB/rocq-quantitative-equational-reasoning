From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(* We use finite types from MathComp *)
Section FiniteDistribution.

Variable A : finType.

(* A distribution is just a function A -> R *)
Definition dist := {ffun A -> R}.

(* Sum over finite type *)
Definition total (d : dist) := \sum_(x in A) d x.

(* Valid probability distribution *)
Definition is_distribution (d : dist) :=
  [&& (forall x, 0 <= d x) & total d == 1].

(* Example: Boolean distribution *)

Definition bool_dist : {ffun bool -> R} :=
  [ffun b => if b then 0.3 else 0.7].

Example bool_dist_nonneg : forall b, 0 <= bool_dist b.
Proof.
move=> b; rewrite ffunE; case: b; lra.
Qed.

Example bool_dist_sum1 : total bool_dist = 1.
Proof.
rewrite /total.
rewrite (big_enum bool).
rewrite !ffunE /=.
lra.
Qed.

(* Putting it together *)
Example bool_is_distribution : is_distribution bool_dist.
Proof.
apply/andP; split.
- exact: bool_dist_nonneg.
- rewrite /total (big_enum bool) !ffunE /=; apply/eqP; lra.
Qed.

End FiniteDistribution.
