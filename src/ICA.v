From mathcomp Require Import ssreflect ssrfun ssrbool ssralg ssrnum reals fintype.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import preorder.Order.PreorderTheory Num.Theory GRing.Theory.

From Template Require Import Signature FuzzyRelation FRelDeduction.
From Template Require Import ProbabilityDistribution.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Record ica_weight (R : realType) := {
  ica_weight_val : R;
  ica_weight_open : (0 < ica_weight_val < 1)%R;
}.

Definition ica_probability_weight {R : realType}
    (p : ica_weight R) : probability_weight R.
Proof.
  refine {| weight := ica_weight_val p |}.
  have /andP [Hp0 Hp1] := ica_weight_open p.
  apply/andP; split.
  - apply: ltW Hp0.
  - apply: ltW Hp1.
Defined.

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

Definition ica_weight_complement {R : realType} 
  (p : ica_weight R) : ica_weight R.
Proof.
  refine {| ica_weight_val := 1 - ica_weight_val p |}.
  have /andP [Hp0 Hp1] := ica_weight_open p.
  apply/andP; split.
    - rewrite subr_gt0; apply Hp1.
    - rewrite gtrBl; apply Hp0.
Defined. 

Definition ica_weight_product {R : realType}
  (p q : ica_weight R) : ica_weight R.
Proof.
  refine {| ica_weight_val := ica_weight_val p * ica_weight_val q |}.
  have /andP [Hp0 Hp1] := ica_weight_open p.
  have /andP [Hq0 Hq1] := ica_weight_open q.
  apply/andP; split.
  - by apply mulr_gt0. 
  - move: (ltW Hp0) => {}Hp0.
    move: (ltW Hq0) => {}Hq0.
    by apply mulr_ilt1.
Defined. 

Definition ica_weight_assoc_inner {R : realType}
  (p q : ica_weight R) : ica_weight R.
Proof.
  refine {| 
    ica_weight_val := 
      ((1 - ica_weight_val p) * ica_weight_val q) / 
      (1 - ica_weight_val p * ica_weight_val q) 
  |}.
  have /andP [Hpq_C0 Hpq_C1] := 
    ica_weight_open (ica_weight_complement (ica_weight_product p q)).
  rewrite /ica_weight_product /= in Hpq_C0 Hpq_C1.
  have /andP [HCpq0 HCpq1] := 
    ica_weight_open (ica_weight_product (ica_weight_complement p) q).
  rewrite /ica_weight_product /= in HCpq0 HCpq1.
  apply/andP; split.
  - by apply divr_gt0.
  - rewrite (ltr_pdivrMr _ _ Hpq_C0) mul1r.
    rewrite mulrBl mul1r.
    rewrite ltrBlDr subrK.
    have /andP [_ Hq1] := ica_weight_open q.
    apply: Hq1.
Qed.


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