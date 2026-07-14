(* ============================================================
   Left-invariant barycentric algebras as a quantitative
   enriched Lawvere theory
   ============================================================ *)

From Stdlib Require Import Lists.List.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp Require Import all_classical reals ereal.

From Template Require Import QET Category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

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

Definition LIB_rule_at (n : nat) :
    ctx bary_sig 'I_n -> qeq bary_sig 'I_n -> Prop :=
  @LIB_rule 'I_n.

Definition LIB_QLT : QuantitativeLawvereTheory :=
  {| qlt_sig := bary_sig; qlt_rule := fun X => @LIB_rule X |}.

Definition LIB_enriched_category : EnrichedCategory QSpaceMonoidal :=
  EnrichedLawvereCategory LIB_QLT.

Definition LIB_op : nat -> nat -> Type :=
  qlt_op LIB_QLT.

Definition LIB_hom_object (n m : nat) : QuantitativeSpace :=
  qlt_hom_object LIB_QLT n m.

Definition LIB_arrow_rel (n m : nat) (eps : rat)
    (f g : LIB_op n m) : Prop :=
  @qlt_arrow_rel LIB_QLT n m eps f g.

Definition LIB_single {n : nat} (t : term bary_sig 'I_n) : LIB_op n 1 :=
  fun _ => t.

Lemma LIB_B1_arrow_rel (n : nat) (x y : 'I_n) :
  @LIB_arrow_rel n 1 (0 : rat)
    (LIB_single (Var x <+ one_weight +> Var y))
    (LIB_single (Var x)).
Proof.
  split; first exact: Qnn_zero.
  move=> i.
  apply: DSS_Axiom.
  apply: LIB_B1.
Qed.

Lemma LIB_B2_arrow_rel (n : nat) (e : bary_weight) (x : 'I_n) :
  @LIB_arrow_rel n 1 (0 : rat)
    (LIB_single (Var x <+ e +> Var x))
    (LIB_single (Var x)).
Proof.
  split; first exact: Qnn_zero.
  move=> i.
  apply: DSS_Axiom.
  apply: LIB_B2.
Qed.

Definition LIB_id (n : nat) : LIB_op n n :=
  @qlt_id LIB_QLT n.

Definition LIB_comp {n m k : nat}
    (g : LIB_op m k) (f : LIB_op n m) : LIB_op n k :=
  @qlt_comp LIB_QLT n m k g f.

Definition LIB_derives (n : nat) :
    ctx bary_sig 'I_n -> qeq bary_sig 'I_n -> Prop :=
  fun Gamma phi => derives_S (@LIB_rule_at n) Gamma phi.
