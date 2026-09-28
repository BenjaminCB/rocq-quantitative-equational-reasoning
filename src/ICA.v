From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssralg ssrnum ssrint reals fintype.
From mathcomp Require Import interval interval_inference.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import preorder.Order.PreorderTheory Num.Theory GRing.Theory.

From Template Require Import Signature FuzzyRelation FRelDeduction.
From Template Require Import ProbabilityDistribution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** An ICA weight is a real number known, by construction, to lie in the
    *open* unit interval.  Mathcomp's canonical-structure interval machinery
    ([mathcomp.algebra.interval_inference]) already provides the closed unit
    interval as [{i01 R}] and the generic [{itv R & i}] family for an
    arbitrary interval [i]; the open unit interval is simply
    [{itv R & `]0,1[}], so no hand-rolled sigma type is needed for the
    interval itself. *)
Notation ica_weight R := {itv R & `]0%Z, 1%Z[}.

Section ICAWeight.
Context {R : realType}.

Lemma itv_oo01_subdef (x : R) (x0 : 0 < x) (x1 : x < 1) :
  Itv.spec (@Itv.num_sem R) (Itv.Real `]0%Z, 1%Z[) x.
Proof. by apply/and3P; split; rewrite ?bnd_simp// gtr0_real. Qed.

(** The only piece of interval-membership plumbing this file has to build
    by hand: a smart constructor for [{itv R & `]0,1[}], in the style of
    mathcomp's own [Itv01]/[PosNum]/[NngNum]. *)
Definition mk_ica_weight (x : R) (x0 : 0 < x) (x1 : x < 1) : ica_weight R :=
  Itv.mk (itv_oo01_subdef x0 x1).
Arguments mk_ica_weight x x0 x1 : clear implicits.

Definition ica_weight_val (p : ica_weight R) : R := p%:num.

Lemma ica_weight_open (p : ica_weight R) :
  (0 < ica_weight_val p < 1)%R.
Proof. by rewrite /ica_weight_val; apply/andP; split; [exact: gt0 | exact: lt1]. Qed.

(** [{itv R & `]0,1[}] widens to [{i01 R}] = [probability_weight R] for
    free, via mathcomp's canonical sub-interval inference. *)
Definition ica_probability_weight (p : ica_weight R) : probability_weight R :=
  widen_itv p.

Lemma ica_probability_weightE (p : ica_weight R) :
  (ica_probability_weight p)%:num = ica_weight_val p.
Proof. by []. Qed.

(** [1 - p], [p * q] land back in [`]0,1[} automatically: mathcomp's
    canonical instances for negation/multiplication on interval subtypes
    infer this on their own, so [%:itv] does all the work. *)
Definition ica_weight_complement (p : ica_weight R) : ica_weight R :=
  (1 - p%:num)%:itv.

Lemma ica_weight_complementP (p : ica_weight R) :
  ica_probability_weight (ica_weight_complement p) =
  (1 - (ica_probability_weight p)%:num)%:i01.
Proof. by apply: val_inj. Qed.

Definition ica_weight_product (p q : ica_weight R) : ica_weight R :=
  (p%:num * q%:num)%:itv.

(** The division below is not automatically bounded by mathcomp's generic
    inference (it has no way to know the numerator is dominated by the
    denominator), so this one genuinely needs the numeric argument -- the
    same argument as before, just packaged through [mk_ica_weight] instead
    of a hand-rolled record. *)
Definition ica_weight_assoc_inner (p q : ica_weight R) : ica_weight R.
Proof.
  refine (mk_ica_weight (((1 - p%:num) * q%:num) / (1 - p%:num * q%:num)) _ _).
  - have /andP [Hpq_C0 Hpq_C1] :=
      ica_weight_open (ica_weight_complement (ica_weight_product p q)).
    rewrite /ica_weight_val /ica_weight_complement /ica_weight_product /=
      in Hpq_C0 Hpq_C1.
    by apply: divr_gt0.
  - have /andP [Hpq_C0 Hpq_C1] :=
      ica_weight_open (ica_weight_complement (ica_weight_product p q)).
    rewrite /ica_weight_val /ica_weight_complement /ica_weight_product /=
      in Hpq_C0 Hpq_C1.
    rewrite (ltr_pdivrMr _ _ Hpq_C0) mul1r.
    rewrite mulrBl mul1r.
    rewrite ltrBlDr subrK.
    have /andP [_ Hq1] := ica_weight_open q.
    rewrite /ica_weight_val in Hq1.
    apply: Hq1.
Defined.

End ICAWeight.

Inductive ica_sym (R : realType) : Type :=
  | ica_plus : ica_weight R -> ica_sym R.

Definition ica_arity {R : realType} (_ : ica_sym R) : nat := 2.

Definition ica_signature {R : realType} : signature :=
  {| sym := ica_sym R; arity := ica_arity |}.


Definition ica_op {R : realType} {X : Type} (p : ica_weight R)
    (x y : term ica_signature X) : term ica_signature X :=
  @App ica_signature X (ica_plus p)
    (fun i => if (Nat.eqb (i : nat) 0) then x else y).

Notation "x <+ p +> y" := (ica_op p x y)
  (at level 40, p at next level, left associativity).

Definition ica_full_space (R : realType) (n : nat) : fuzzy_space R.
Proof.
  refine {| fcarrier := 'I_n; frel := fun _ _ => 1 |}.
  by move => i j; rewrite ler01 lexx.
Defined.

(*
[ 1, 1, eps, 1     ]
[ 1, 1, 1,   delta ]
[ 1, 1, 1,   1     ]
[ 1, 1, 1,   1     ]
*)
Definition ica_interp_rel {R : realType}
    (eps delta : R) (a b : 'I_4) : R :=
  match nat_of_ord a, nat_of_ord b with
  | 0, 2 => eps
  | 1, 3 => delta
  | _, _ => 1
  end.

Definition ica_interp_space (R : realType)
  (eps delta : R)
  (Heps : (0 <= eps <= 1)%R)
  (Hdelta : (0 <= delta <= 1)%R) : fuzzy_space R.
Proof.
  refine {| fcarrier := 'I_4; frel := ica_interp_rel eps delta |}.
  move => i j.
  rewrite /ica_interp_rel.
  case: (nat_of_ord i) => [ | [ | i' ] ];
  case: (nat_of_ord j) => [ | [ | [ | [ | j' ] ] ] ] /=.
  3: apply: Heps.
  8: apply: Hdelta.
  all: by rewrite ler01 lexx.
Defined.

Inductive ica_theory (R : realType) : fuzzy_theory R (@ica_signature R) :=
  | ICA_Idem (p : ica_weight R) :
      @ica_theory R (ica_full_space R 1)
        (EqJ
          ((Var (inord 0)) <+ p +> (Var (inord 0)))
          (Var (inord 0)))
  | ICA_Skew_Comm (p : ica_weight R) :
      @ica_theory R (ica_full_space R 2)
        (EqJ
          ((Var (inord 0)) <+ p +> (Var (inord 1)))
          ((Var (inord 1)) <+ ica_weight_complement p +>
            (Var (inord 0))))
  | ICA_Skew_Assoc (p q : ica_weight R) :
      @ica_theory R (ica_full_space R 3)
        (EqJ
          (((Var (inord 0)) <+ p +> (Var (inord 1))) <+ q +>
            (Var (inord 2)))
          ((Var (inord 0)) <+ ica_weight_product p q +>
            ((Var (inord 1)) <+ ica_weight_assoc_inner p q +>
              (Var (inord 2)))))
  | ICA_Interp (p : ica_weight R) (eps delta : R)
      (Heps : (0 <= eps <= 1)%R)
      (Hdelta : (0 <= delta <= 1)%R) :
      @ica_theory R (@ica_interp_space R eps delta Heps Hdelta)
        (QEqJ
          (weighted_sum (ica_probability_weight p) eps delta)
          ((Var (inord 0)) <+ p +> (Var (inord 1)))
          ((Var (inord 2)) <+ p +> (Var (inord 3)))).

Lemma ica_idem_subst
    {R : realType}
    (mode : frel_derivation_mode)
    (X : fuzzy_space R)
    (p : ica_weight R)
    (t : term (@ica_signature R) (fcarrier X)) :
  @frel_derives R ica_signature (@ica_theory R)
    mode X
    (subst_judgement
      (fun _ : fcarrier (ica_full_space R 1) => t)
      (EqJ
        ((Var (inord 0)) <+ p +> (Var (inord 0)))
        (Var (inord 0)))).
Proof.
  apply: (FD_Subst
    (X := ica_full_space R 1)
    (phi := EqJ
      ((Var (inord 0)) <+ p +> (Var (inord 0)))
      (Var (inord 0)))
    (sigma := fun _ => t)).
  - apply: FD_Init.
    exact: ICA_Idem p.
  - move => x y.
    apply: FD_Max.
Qed.

Lemma ica_idem_instance
    {R : realType}
    (mode : frel_derivation_mode)
    (X : fuzzy_space R)
    (p : ica_weight R)
    (t : term (@ica_signature R) (fcarrier X)) :
  @frel_derives R ica_signature (@ica_theory R)
    mode X
    (EqJ (t <+ p +> t) t).
Proof.
  have H := ica_idem_subst mode p t.
  rewrite /subst_judgement /= /ica_op /comp in H.
  have Hargs :
      (fun i : 'I_(ica_arity (ica_plus p)) =>
        subst_term
          (fun _ : fcarrier (ica_full_space R 1) => t)
          (if Nat.eqb (i : nat) 0
           then Var (inord 0)
           else Var (inord 0))) =
      (fun _ : 'I_(ica_arity (ica_plus p)) => t).
  - apply: functional_extensionality => i.
    by case: (Nat.eqb (i : nat) 0).
  rewrite Hargs in H.
  rewrite /ica_op /=.
  have Htarget :
      (fun i : 'I_(ica_arity (ica_plus p)) =>
        if Nat.eqb (i : nat) 0 then t else t) =
      (fun _ : 'I_(ica_arity (ica_plus p)) => t).
  - apply: functional_extensionality => i.
    by case: (Nat.eqb (i : nat) 0).
  rewrite Htarget.
  exact H.
Qed.
