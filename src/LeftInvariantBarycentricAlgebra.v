(* ============================================================
   Left-invariant barycentric algebras as a quantitative
   enriched Lawvere theory
   ============================================================ *)

From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp Require Import all_classical reals ereal.

From Template Require Import QET Category Metric.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition unit_interval (e : rat) : Prop :=
  (0 <= e <= 1)%R.

Record bary_weight := {
  bw : rat;
  bw_unit : unit_interval bw;
}.

Definition one_weight : bary_weight.
Proof.
  refine {| bw := 1 |}.
  rewrite /unit_interval.
  by split; rewrite ?ler01 ?lexx.
Defined.

Inductive bary_sym : Type :=
  | bary_plus : bary_weight -> bary_sym.

Definition bary_arity (_ : bary_sym) : nat := 2.

Definition bary_sig : signature :=
  {| sym := bary_sym; arity := bary_arity |}.

Definition bary {X : Type} (e : bary_weight)
    (x y : term bary_sig X) : term bary_sig X :=
  @App bary_sig X (bary_plus e)
    (fun i => if ((i : nat) == 0) then x else y).

Notation "x <+ e +> y" := (bary e x y)
  (at level 40, e at next level, left associativity).

Definition LIB_category : Category :=
  LawvereCategory bary_sig.

Inductive LIB_rule {X : Type} : ctx bary_sig X -> qeq bary_sig X -> Prop :=
  | LIB_B1 : forall x y,
      LIB_rule [::]
        (Var x <+ one_weight +> Var y ~[0] Var x)
  | LIB_B2 : forall (e : bary_weight) x,
      LIB_rule [::]
        (Var x <+ e +> Var x ~[0] Var x)
  | LIB_SC : forall (e e' : bary_weight) x y,
      bw e' = 1 - bw e ->
      LIB_rule [::]
        (Var x <+ e +> Var y ~[0] Var y <+ e' +> Var x)
  | LIB_SA : forall (e e' ee' skew : bary_weight) x y z,
      (0 < bw e)%R ->
      (bw e < 1)%R ->
      (0 < bw e')%R ->
      (bw e' < 1)%R ->
      bw ee' = bw e * bw e' ->
      bw skew = (bw e' - bw e * bw e') / (1 - bw e * bw e') ->
      LIB_rule [::]
        ((Var x <+ e +> Var y) <+ e' +> Var z ~[0]
         Var x <+ ee' +> (Var y <+ skew +> Var z))
  | LIB_LI : forall (e : bary_weight) eps x x' x'',
      Qnn eps ->
      (bw e <= eps)%R ->
      LIB_rule [::]
        (Var x' <+ e +> Var x ~[eps] Var x'' <+ e +> Var x).

Definition LIB_d {R : realType} {n m : nat}
    (f g : lawvere_op bary_sig n m) : \bar R :=
  ereal_inf [set r : \bar R |
    (0%:E <= r)%E /\
    forall i : 'I_m, (d_U (fun X => @LIB_rule X) (f i) (g i) <= r)%E].

Definition LIB_zero_equiv {R : realType} {n m : nat}
    (f g : lawvere_op bary_sig n m) : Prop :=
  @LIB_d R n m f g = 0.

Definition LIB_hom_dist {R : realType} {n m : nat}
    (f g : lawvere_op bary_sig n m) : \bar R :=
  @LIB_d R n m f g.

(*
Previous raw-carrier attempt, kept here as proof progress/reference.
This cannot finish as an ext_metric_space because dist_eq0 is too strong
before quotienting by LIB_zero_equiv.

Definition LIB_hom_metric_space (R : realType) (n m : nat) : ext_metric_space R.
Proof.
  refine {|
    carrier := lawvere_op bary_sig n m;
    dist := @LIB_hom_dist R n m
  |}.
  - move => a b.
    rewrite /LIB_hom_dist /LIB_d.
    apply/ereal_infP => y Hy.
    by case: Hy => Hy0 _.
  - move => a.
    rewrite /LIB_hom_dist /LIB_d.
    apply: Order.POrderTheory.le_anti; apply /andP; split.
    + apply: ge_ereal_inf; exists 0; last by apply lexx.
      rewrite /mkset; split; first by apply lexx.
      move => i.
      rewrite /d_U /extended_infimum.
      apply: ge_ereal_inf; exists 0; last by apply lexx.
      rewrite /bound_set /mkset.
      exists (0 : R)%R; last by [].
      exists (exist _ (0 : rat) Qnn_zero).
      split.
      * exact: D_Refl.
      * rewrite /nnrat_embed /nnrat_val /=.
        symmetry.
        exact: (ratr_nat R 0).
    + apply/ereal_infP => y Hy.
      by case: Hy => Hy0 _.
  - move => a b H.
    rewrite /LIB_hom_dist /LIB_d in H.
    apply: Order.POrderTheory.le_anti in .
    (* dist_eq0:
       This is the quotient step from the paper. On the raw lawvere_op
       carrier this obligation is too strong; it should become true after
       quotienting by LIB_zero_equiv. *)
  - (* dist_symm:
       Use d_U_symm componentwise and extensionality of the upper-bound
       sets defining LIB_d. *)
  - (* dist_tri:
       Use d_U_tri componentwise. If r bounds f/g and s bounds g/h,
       then r + s bounds f/h, so the supremum-style LIB_d satisfies
       the triangle inequality. *)
Defined.
*)

Record LIB_hom_metric_quotient (R : realType) (n m : nat) := {
  LIB_hom_qspace :> ext_metric_space R;
  LIB_hom_qclass :
    lawvere_op bary_sig n m -> carrier LIB_hom_qspace;
  LIB_hom_qclass_surj :
    forall x : carrier LIB_hom_qspace,
      exists f : lawvere_op bary_sig n m, LIB_hom_qclass f = x;
  LIB_hom_qdist :
    forall f g : lawvere_op bary_sig n m,
      dist (LIB_hom_qclass f) (LIB_hom_qclass g) =
      @LIB_hom_dist R n m f g;
  LIB_hom_qzero_exact :
    forall f g : lawvere_op bary_sig n m,
      @LIB_zero_equiv R n m f g <-> LIB_hom_qclass f = LIB_hom_qclass g;
}.

Definition LIB_metric_quotient (R : realType) : Type :=
  forall n m : nat, LIB_hom_metric_quotient R n m.

Definition LIB_hom_metric_space {R : realType}
    (Q : LIB_metric_quotient R) (n m : nat) : ext_metric_space R :=
  LIB_hom_qspace (Q n m).