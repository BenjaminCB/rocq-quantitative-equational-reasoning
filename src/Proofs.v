(* src/Proofs.v *)
From Stdlib Require Import Arith Lia List.
Import ListNotations.

Print LoadPath.

From Template Require Import Basics.

Lemma sum_singleton :
  forall n, mysum [n] = n.
Proof.
  intro n. simpl. lia.
Qed.

Lemma sum_cons_ge :
  forall x xs, mysum (x :: xs) >= x.
Proof.
  intros x xs. simpl. lia.
Qed.
