(* ============================================================
   Metric quotient scaffolding for quantitative Lawvere theories
   ============================================================ *)

From mathcomp Require Import all_ssreflect_compat all_algebra.
From mathcomp Require Import all_classical reals ereal.

From Template Require Import Metric QET.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

(** Hom-wise pseudometric induced by a quantitative equational theory.

    A raw arrow [n -> m] is an [m]-tuple of terms in [n] variables.  Its
    distance is the least extended real bound that bounds the induced
    term pseudometric [d_U] componentwise. *)
Definition qlt_hom_d {R : realType} {sig : signature}
    (U : axiom_scheme sig) {n m : nat}
    (f g : lawvere_op sig n m) : \bar R :=
  ereal_inf [set r : \bar R |
    (0%:E <= r)%E /\
    forall i : 'I_m, (@d_U R sig 'I_n U (f i) (g i) <= r)%E].

Definition qlt_hom_zero_equiv {R : realType} {sig : signature}
    (U : axiom_scheme sig) {n m : nat}
    (f g : lawvere_op sig n m) : Prop :=
  @qlt_hom_d R sig U n m f g = 0.

(** Abstract quotient of the paper's term pseudometric.

    In the paper, [d~] is the metric induced on equivalence classes by the
    pseudometric [d_U], characterized by

      d~ ([s], [t]) = d_U s t.

    The actual quotient carrier is left abstract here.  This record packages
    exactly the data needed downstream: a separated metric space, the quotient
    map, and the characterization of its metric and equality on representatives. *)
Record TermMetricQuotient (R : realType) (sig : signature) (X : Type)
    (U : axiom_scheme sig) := {
  tmq_space :> ext_metric_space R;
  tmq_class : term sig X -> carrier tmq_space;
  tmq_class_surj :
    forall x : carrier tmq_space, exists t : term sig X, tmq_class t = x;
  tmq_d_tilde_class :
    forall s t : term sig X,
      dist (tmq_class s) (tmq_class t) = @d_U R sig X U s t;
  tmq_zero_exact :
    forall s t : term sig X,
      @d_U R sig X U s t = 0 <-> tmq_class s = tmq_class t;
}.

Definition term_d_tilde {R : realType} {sig : signature} {X : Type}
    {U : axiom_scheme sig} (Q : @TermMetricQuotient R sig X U)
    (x y : carrier Q) : \bar R :=
  dist x y.

Lemma term_d_tilde_class {R : realType} {sig : signature} {X : Type}
    {U : axiom_scheme sig} (Q : @TermMetricQuotient R sig X U)
    (s t : term sig X) :
  @term_d_tilde R sig X U Q
    (@tmq_class R sig X U Q s) (@tmq_class R sig X U Q t) =
  @d_U R sig X U s t.
Proof. exact: (@tmq_d_tilde_class R sig X U Q s t). Qed.

(** Hom-object quotient for the metric-enriched Lawvere category.

    This is the Lawvere-arrow analogue of [TermMetricQuotient], using the
    componentwise hom pseudometric [qlt_hom_d]. *)
Record HomMetricQuotient (R : realType) (sig : signature)
    (U : axiom_scheme sig) (n m : nat) := {
  hmq_space :> ext_metric_space R;
  hmq_class : lawvere_op sig n m -> carrier hmq_space;
  hmq_class_surj :
    forall x : carrier hmq_space, exists f : lawvere_op sig n m,
      hmq_class f = x;
  hmq_d_tilde_class :
    forall f g : lawvere_op sig n m,
      dist (hmq_class f) (hmq_class g) =
      @qlt_hom_d R sig U n m f g;
  hmq_zero_exact :
    forall f g : lawvere_op sig n m,
      @qlt_hom_zero_equiv R sig U n m f g <->
      hmq_class f = hmq_class g;
}.

Definition hom_d_tilde {R : realType} {sig : signature}
    {U : axiom_scheme sig} {n m : nat}
    (Q : @HomMetricQuotient R sig U n m)
    (x y : carrier Q) : \bar R :=
  dist x y.

Lemma hom_d_tilde_class {R : realType} {sig : signature}
    {U : axiom_scheme sig} {n m : nat}
    (Q : @HomMetricQuotient R sig U n m)
    (f g : lawvere_op sig n m) :
  @hom_d_tilde R sig U n m Q
    (@hmq_class R sig U n m Q f) (@hmq_class R sig U n m Q g) =
  @qlt_hom_d R sig U n m f g.
Proof. exact: (@hmq_d_tilde_class R sig U n m Q f g). Qed.

(** Data still needed to build the quotient Lawvere algebra/category.

    The quotient spaces alone do not yet give composition: substitution has to
    respect zero-distance classes, and the descended composition has to satisfy
    the metric estimate chosen for the monoidal tensor.  The additive estimate
    below is the one suggested by substitution plus triangle-style bounds. *)
Record MetricLawvereQuotient (R : realType) (sig : signature)
    (U : axiom_scheme sig) := {
  mlq_hom : forall n m : nat, @HomMetricQuotient R sig U n m;
  mlq_comp_wd :
    forall n m k
      (f f' : lawvere_op sig n m) (g g' : lawvere_op sig m k),
      @qlt_hom_zero_equiv R sig U n m f f' ->
      @qlt_hom_zero_equiv R sig U m k g g' ->
      @qlt_hom_zero_equiv R sig U n k
        (lawvere_comp g f) (lawvere_comp g' f');
  mlq_comp_nexp_additive :
    forall n m k
      (f f' : lawvere_op sig n m) (g g' : lawvere_op sig m k),
      @qlt_hom_d R sig U n k
        (lawvere_comp g f) (lawvere_comp g' f') <=
      @qlt_hom_d R sig U m k g g' + @qlt_hom_d R sig U n m f f';
}.

Definition mlq_hom_space {R : realType} {sig : signature}
    {U : axiom_scheme sig} (Q : @MetricLawvereQuotient R sig U)
    (n m : nat) : ext_metric_space R :=
  @hmq_space R sig U n m (@mlq_hom R sig U Q n m).

Definition mlq_hom_d_tilde {R : realType} {sig : signature}
    {U : axiom_scheme sig} (Q : @MetricLawvereQuotient R sig U)
    {n m : nat} (x y : carrier (mlq_hom_space Q n m)) : \bar R :=
  @hom_d_tilde R sig U n m (@mlq_hom R sig U Q n m) x y.

(** Quotient term algebra scaffold.

    The operation field is intentionally stated with a representative law:
    to construct this record, prove that operations are well-defined on
    zero-distance classes, then define the operations on quotient classes. *)
Definition quotient_algebra_ops {R : realType} {sig : signature}
    {X : Type} {U : axiom_scheme sig}
    (Q : @TermMetricQuotient R sig X U) : Type :=
  forall f : sym sig, ('I_(arity f) -> carrier Q) -> carrier Q.

Record QuotientAlgebra (R : realType) (sig : signature) (X : Type)
    (U : axiom_scheme sig) := {
  qa_terms :> @TermMetricQuotient R sig X U;
  qa_ops : quotient_algebra_ops qa_terms;
  qa_ops_class :
    forall (f : sym sig) (args : 'I_(arity f) -> term sig X),
      @qa_ops f (fun i => @tmq_class R sig X U qa_terms (args i)) =
      @tmq_class R sig X U qa_terms (App f args);
  qa_ops_non_expansive :
    @non_expansive R (sym sig) (@arity sig) qa_terms qa_ops;
}.
