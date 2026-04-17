Require Import Reals Psatz.
Open Scope R_scope.
Generalizable All Variables.
Set Implicit Arguments.

Class BaryAlg (X : Type) := {
  mix : R -> X -> X -> X;

  b1 : forall x y, mix 1 x y = x;
  b2 : forall t x, mix t x x = x;
  sc : forall t x y, mix t x y = mix (1 - t) y x;
  sa : forall t s x y z,
    0 < s /\ s < 1 ->
    0 < t /\ t < 1 ->
    mix t (mix s x y) z =
    mix (t * s) x (mix ((s - t * s) / (1 - t * s)) y z);
}.

Notation "x +[ t ] y" := (mix t x y)
  (at level 50, left associativity).

Lemma mix_congr_left `{BaryAlg X} (t : R) (x x' y : X) :
  x = x' ->
  x +[t] y = x' +[t] y.
Proof.
  intros.
  subst.
  reflexivity.
Qed.

Lemma blend_comm `{BaryAlg X} (x y : X) :
  x +[0.8] y = y +[0.2] x.
Proof.
  replace (0.2) with (1 - 0.8) by lra.
  apply sc.
Qed.

Reserved Notation "x ~[ e ] y" (at level 70).

Inductive QBase {X : Type} {b : BaryAlg X} : R -> X -> X -> Prop :=

  | q_eq : forall (x y : X),
      x = y ->
      x ~[0] y

  | q_sym : forall (x y : X) e,
      x ~[e] y ->
      y ~[e] x

  | q_trans : forall (x y z : X) e1 e2,
      x ~[e1] y ->
      y ~[e2] z ->
      x ~[e1 + e2] z

  | q_mono : forall (x y : X) e e',
      x ~[e] y ->
      e <= e' ->
      x ~[e'] y

  where "x ~[ e ] y" := (QBase e x y).

Lemma q_eq_x_x_0 : forall (X : Type) (b :BaryAlg X) (x : X),
  x ~[0] x.
Proof. 
  intros.
  apply q_eq. 
  reflexivity.
Qed.

(** LI quantitative barycentric theory *)
Inductive LIQEq {X : Type} {b : BaryAlg X} : R -> X -> X -> Prop :=

  | li_base : forall (x y : X) e,
      QBase e x y ->
      LIQEq e x y

  | li : forall t (x x' y : X) e,
      LIQEq e x x' ->
      LIQEq e (x +[t] y) (x' +[t] y).

(** LI quantitative barycentric theory *)
Inductive BIQEq {X : Type} {b : BaryAlg X} : R -> X -> X -> Prop :=

  | bi_base : forall (x y : X) e,
      QBase e x y ->
      BIQEq e x y

  | bi : forall t (x x' y y' : X) e e',
      BIQEq e x y ->
      BIQEq e' x' y' ->
      BIQEq (t * e + (1 - t) * e') (x +[t] x') (y +[t] y').

Ltac replace_mix_t_goal q :=
  match goal with
  | |- context[?x +[ ?t ] ?y] =>
      replace t with q by lra
  end.

Ltac replace_mix_t_in H q :=
  match type of H with
  | context[?x +[ ?t ] ?y] =>
      replace t with q in H by lra
  end.

Example bi_ex_1 : forall (X : Type) (b : BaryAlg X) (x y : X),
  BIQEq 0.5 x y -> BIQEq 0.2 (x +[0.8] y) (x +[0.4] y).
Proof.
  intros.

  (* rewrite LHS *)
  replace (x +[ 0.8] y) with ((x +[0.5] x) +[0.8] y).
  2: {
    apply mix_congr_left.
    apply b2.
  }

  (* rewrite RHS *)
  replace (x +[ 0.4] y) with ((x +[0.5] y) +[0.8] y).
  2: {
    rewrite sa; [ | lra | lra ].
    rewrite b2.
    replace_mix_t_goal 0.4.
    reflexivity.
  }

  pose proof (q_eq_x_x_0 b x) as Hxx.
  apply bi_base in Hxx.
  pose proof (q_eq_x_x_0 b y) as Hyy.
  apply bi_base in Hyy.

  eassert (Hxx_xy : BIQEq _ (x +[0.5] x) (x +[0.5] y)).
  {
    apply bi.
    - exact Hxx.
    - exact H.
  }

  eassert (Hxx_xy__yy : BIQEq _ ((x +[0.5] x) +[0.8] y) ((x +[0.5] y) +[0.8] y)).
  {
    apply bi. 
    - apply Hxx_xy.
    - apply Hyy. 
  }

  replace (0.8 * (0.5 * 0 + (1 - 0.5) * 0.5) + (1 - 0.8) * 0)
    with 0.2 in Hxx_xy__yy by lra.

  apply Hxx_xy__yy.
Qed.







