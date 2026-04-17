(* src/Basics.v *)
From Stdlib Require Import Arith Lia List.
Import ListNotations.

Fixpoint mysum (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => x + mysum xs'
  end.

Lemma sum_app :
  forall xs ys, mysum (xs ++ ys) = mysum xs + mysum ys.
Proof.
  induction xs as [|x xs IH]; intros ys.
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.
