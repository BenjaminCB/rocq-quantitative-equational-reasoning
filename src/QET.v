(* ============================================================
   Quantitative Algebraic Reasoning
   Mardare, Panangaden, Plotkin — LICS 2016

   Formalization in Rocq (Coq)
   ============================================================

   OVERVIEW OF CHANGES / DESIGN DECISIONS vs. your original file
   --------------------------------------------------------------
   1. eps is kept as Q but we add a side-condition (0 <= eps) at
      every rule that needs it, rather than a sigma-type, to keep
      pattern-matching simple.  A separate Qnn ("non-negative Q")
      notation is introduced for readability.

   2. The deducibility rules in the paper have the form
        Gamma ` phi
      where the *hypotheses* Gamma are drawn from a fixed ambient
      context and the rule fires when those hypotheses are
      *provable* (not merely syntactically present).  Your
      original encoding used `In h ctx` which makes the rules
      too weak (only closed under the ambient list, not under
      derivability).  We fix this by requiring `ctx |- h` for
      hypothesis occurrences inside Triang / Max / Arch / NExp.

   3. Definition 2.2 (quantitative equational theory induced by
      a set S of basic inferences) is added as `qe_theory`.

   4. Section 3: quantitative algebras.

   5. Section 4: satisfaction / semantic entailment.

   6. Section 5: induced pseudometric on terms.

   7. Section 6: free quantitative algebra (term quotient).

   Sections 7–11 (continuous / metric-space free algebras,
   barycentric algebras, Wasserstein metrics) are outlined with
   definitions and statement skeletons; filling in all proofs is
   left for future work, as they depend on substantial real-
   analysis infrastructure.
   ============================================================ *)

Require Import Coq.Vectors.Vector.
Import VectorNotations.
Require Import QArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Reals Psatz.

Set Implicit Arguments.

(* ============================================================
   §0  Utilities
   ============================================================ *)

(** Non-negative rationals as a predicate.  We deliberately keep
    eps : Q everywhere and add (0 <= eps) side-conditions so that
    dependent pattern-matching stays tractable. *)
Notation Qnn q := (0 <= q).

Lemma Qnn_add : forall p q, Qnn p -> Qnn q -> Qnn (p + q).
Proof. intros. lra. Qed.

Lemma Qnn_zero : Qnn 0.
Proof. lra. Qed.

(* ============================================================
   §1  Signatures and terms  (your original code, lightly cleaned)
   ============================================================ *)

Record signature := {
  sym   : Type;
  arity : sym -> nat;
}.

Inductive term (sig : signature) (X : Type) : Type :=
  | Var : X -> term sig X
  | App : forall (f : sym sig),
      Vector.t (term sig X) (arity sig f) -> term sig X.

Arguments Var {sig X} _.
Arguments App {sig X} _ _.

(** Substitution: a map X → term sig X, extended homomorphically. *)
Fixpoint subst_term {sig X} (sigma : X -> term sig X) (t : term sig X) : term sig X :=
  match t with
  | Var x   => sigma x
  | App f v => App f (Vector.map (subst_term sigma) v)
  end.

(** Composition of substitutions. *)
Definition subst_comp {sig X} (sigma tau : X -> term sig X) : X -> term sig X :=
  fun x => subst_term sigma (tau x).

(** Substitution is a homomorphism (standard). *)
Lemma subst_term_comp {sig X} (sigma tau : X -> term sig X) (t : term sig X) :
  subst_term sigma (subst_term tau t) = subst_term (subst_comp sigma tau) t.
Proof.
  induction t.
  - reflexivity.
  - simpl. f_equal.
    apply Vector.eq_nth_iff; intros i j Hij.
    admit.
    (* 
    rewrite !Vector.nth_map.
    apply IH.
    *)
Admitted.

(* ============================================================
   §2  Quantitative equations and deducibility  (Def 2.1)
   ============================================================ *)

(** A quantitative equation  t =_epsilon s  over terms. *)
Record qeq (sig : signature) (X : Type) := {
  lhs : term sig X;
  rhs : term sig X;
  eps : Q;
}.

Notation "t ~[ e ] s" := {| lhs := t; rhs := s; eps := e |}
  (at level 70, no associativity).

(** Lift substitution to equations. *)
Definition subst_qeq {sig X} (sigma : X -> term sig X) (q : qeq sig X) : qeq sig X :=
  {| lhs := subst_term sigma (lhs q);
     rhs := subst_term sigma (rhs q);
     eps := eps q |}.

(** A *context* is a (finite) list of quantitative equations used
    as hypotheses.  (The paper writes Gamma ⊆ V(TX).) *)
Definition ctx sig X := list (qeq sig X).

(** Apply a substitution to every equation in a context. *)
Definition subst_ctx {sig X} (sigma : X -> term sig X) (Gamma : ctx sig X) : ctx sig X :=
  List.map (subst_qeq sigma) Gamma.

(** ----------------------------------------------------------------
    Definition 2.1 — Deducibility relation

    We define a single inductive `derives` that corresponds to the
    smallest deducibility relation.  The rules follow the paper
    exactly; we add non-negativity guards where the paper implicitly
    requires epsilon, epsilon' ∈ Q⁺.

    Key fix vs. your original: the premises of Triang / Max / Arch
    / NExp require the hypotheses to be *derivable* from Gamma (i.e.
    `Gamma |- h`), not merely syntactically present in Gamma.  Using `In`
    would only give a *monotone* relation, not closure under Cut.
    ---------------------------------------------------------------- *)

Reserved Notation "Gamma |- phi" (at level 72).

Inductive derives (sig : signature) (X : Type)
    : ctx sig X -> qeq sig X -> Prop :=

  (** (Refl)  ∅ ⊢ t =_0 t *)
  | D_Refl : forall Gamma t,
      Gamma |- (t ~[0] t)

  (** (Symm)  {t =_epsilon s} ⊢ s =_epsilon t *)
  | D_Symm : forall Gamma t s epsilon,
      Qnn epsilon ->
      Gamma |- (t ~[epsilon] s) ->
      Gamma |- (s ~[epsilon] t)

  (** (Triang)  {t =_epsilon s, s =_epsilon' u} ⊢ t =_{epsilon+epsilon'} u *)
  | D_Triang : forall Gamma t s u epsilon epsilon',
      Qnn epsilon -> Qnn epsilon' ->
      Gamma |- (t ~[epsilon]  s) ->
      Gamma |- (s ~[epsilon'] u) ->
      Gamma |- (t ~[epsilon + epsilon'] u)

  (** (Max)  for epsilon' > 0,  {t =_epsilon s} ⊢ t =_{epsilon+epsilon'} s *)
  | D_Max : forall Gamma t s epsilon epsilon',
      Qnn epsilon ->
      0 < epsilon' ->
      Gamma |- (t ~[epsilon] s) ->
      Gamma |- (t ~[epsilon + epsilon'] s)

  (** (Arch)  for epsilon ≥ 0,  {t =_{epsilon'} s | epsilon' > epsilon} ⊢ t =_epsilon s
      We encode the infinitary premise as a universally quantified
      Rocq hypothesis. *)
  | D_Arch : forall Gamma t s epsilon,
      Qnn epsilon ->
      (forall epsilon', epsilon < epsilon' -> Gamma |- (t ~[epsilon'] s)) ->
      Gamma |- (t ~[epsilon] s)

  (** (NExp)  f is non-expansive: if each t_i =_epsilon s_i then
              f(t_1,…,t_n) =_epsilon f(s_1,…,s_n). *)
  | D_NExp : forall Gamma (f : sym sig)
               (ts ss : Vector.t (term sig X) (arity sig f)) epsilon,
      Qnn epsilon ->
      (forall i, Gamma |- (Vector.nth ts i ~[epsilon] Vector.nth ss i)) ->
      Gamma |- (App f ts ~[epsilon] App f ss)

  (** (Subst)  if Gamma ⊢ t =_epsilon s then sigma(Gamma) ⊢ sigma(t) =_epsilon sigma(s). *)
  | D_Subst : forall Gamma t s epsilon (sigma : X -> term sig X),
      Gamma |- (t ~[epsilon] s) ->
      (subst_ctx sigma Gamma) |- (subst_term sigma t ~[epsilon] subst_term sigma s)

  (** (Cut)  if Gamma ⊢ psi for all psi ∈ Gamma', and Gamma' ⊢ phi, then Gamma ⊢ phi. *)
  | D_Cut : forall Gamma Gamma' phi,
      (forall psi, In psi Gamma' -> Gamma |- psi) ->
      Gamma' |- phi ->
      Gamma  |- phi

  (** (Assumpt)  if phi ∈ Gamma then Gamma ⊢ phi. *)
  | D_Assumpt : forall Gamma phi,
      In phi Gamma ->
      Gamma |- phi

  where "Gamma |- phi" := (derives Gamma phi).

(* ----------------------------------------------------------------
   Basic consequences of the rules
   ---------------------------------------------------------------- *)

(** Weakening: if Gamma ⊢ phi and Gamma ⊆ Gamma' then Gamma' ⊢ phi. *)
Lemma derives_weaken {sig X} (Gamma Gamma' : ctx sig X) phi :
  (forall psi, In psi Gamma -> In psi Gamma') ->
  Gamma  |- phi ->
  Gamma' |- phi.
Proof.
  intros Hsub Hd.
  apply D_Cut with (Gamma' := Gamma).
  - intros psi HIn. apply D_Assumpt. apply Hsub. exact HIn.
  - exact Hd.
Qed.

(** The empty context can derive anything derivable from Gamma via Cut. *)
Lemma derives_empty_cut {sig X} (Gamma : ctx sig X) phi :
  [] |- phi ->
  Gamma  |- phi.
Proof.
  intro H.
  apply D_Cut with (Gamma' := []).
  - intros psi HIn. inversion HIn.
  - exact H.
Qed.

(* ============================================================
   §2  Definition 2.2 — Quantitative Equational Theory
   ============================================================

   Given a set S ⊆ E(TX) of basic quantitative inferences, the
   theory induced by S is the smallest deducibility relation
   containing S.

   We represent a "basic quantitative inference" as a pair
       (hypotheses : ctx sig X,  conclusion : qeq sig X)
   where hypotheses may only contain equations between *variables*
   (the paper's E(X) ⊆ E(TX)).  For the full S ⊆ E(TX) version
   we simply lift to arbitrary contexts.

   The quantitative equational theory U induced by S is then:
       U = { (Gamma, phi) | Gamma |-_S phi }
   where |-_S is the smallest deducibility relation extending the
   rules of Def 2.1 *and* every element of S.

   We encode this by adding one extra constructor to `derives`. *)

(** A set of axiom schemes (basic inferences). *)
Definition axiom_set (sig : signature) (X : Type) :=
  ctx sig X -> qeq sig X -> Prop.

(** `derives_S S Gamma phi` is the deducibility relation generated by
    the rules of Def 2.1 plus S as extra axioms. *)
Inductive derives_S {sig X} (S : axiom_set sig X)
    : ctx sig X -> qeq sig X -> Prop :=

  | DS_Refl   : forall Gamma t,          derives_S S Gamma (t ~[0] t)
  | DS_Symm   : forall Gamma t s epsilon,
      Qnn epsilon -> derives_S S Gamma (t ~[epsilon] s) ->
      derives_S S Gamma (s ~[epsilon] t)
  | DS_Triang : forall Gamma t s u epsilon epsilon',
      Qnn epsilon -> Qnn epsilon' ->
      derives_S S Gamma (t ~[epsilon]  s) ->
      derives_S S Gamma (s ~[epsilon'] u) ->
      derives_S S Gamma (t ~[epsilon + epsilon'] u)
  | DS_Max    : forall Gamma t s epsilon epsilon',
      Qnn epsilon -> 0 < epsilon' ->
      derives_S S Gamma (t ~[epsilon] s) ->
      derives_S S Gamma (t ~[epsilon + epsilon'] s)
  | DS_Arch   : forall Gamma t s epsilon,
      Qnn epsilon ->
      (forall epsilon', epsilon < epsilon' -> derives_S S Gamma (t ~[epsilon'] s)) ->
      derives_S S Gamma (t ~[epsilon] s)
  | DS_NExp   : forall Gamma (f : sym sig)
                  (ts ss : Vector.t (term sig X) (arity sig f)) epsilon,
      Qnn epsilon ->
      (forall i, derives_S S Gamma (Vector.nth ts i ~[epsilon] Vector.nth ss i)) ->
      derives_S S Gamma (App f ts ~[epsilon] App f ss)
  | DS_Subst  : forall Gamma t s epsilon (sigma : X -> term sig X),
      derives_S S Gamma (t ~[epsilon] s) ->
      derives_S S (subst_ctx sigma Gamma) (subst_term sigma t ~[epsilon] subst_term sigma s)
  | DS_Cut    : forall Gamma Gamma' phi,
      (forall psi, In psi Gamma' -> derives_S S Gamma psi) ->
      derives_S S Gamma' phi ->
      derives_S S Gamma phi
  | DS_Assumpt : forall Gamma phi,
      In phi Gamma -> derives_S S Gamma phi

  (** The new constructor: every element of S is an axiom. *)
  | DS_Axiom  : forall Gamma phi,
      S Gamma phi -> derives_S S Gamma phi.

(** Definition 2.2.
    The quantitative equational theory induced by S is the set of
    all unconditional inferences (Gamma, phi) derivable via derives_S. *)
Definition qe_theory {sig X} (S : axiom_set sig X) : axiom_set sig X :=
  fun Gamma phi => derives_S S Gamma phi.

(** Consistency (Def 2.3): U is inconsistent if it derives x =_0 y
    for two distinct variables x y.  We parameterise over the
    variable type X and require two *provably distinct* elements. *)
Definition inconsistent {sig X} (U : axiom_set sig X) : Prop :=
  exists (x y : X), x <> y /\ U [] (Var x ~[0] Var y).

Definition consistent {sig X} (U : axiom_set sig X) : Prop :=
  ~ inconsistent U.

(* ============================================================
   §3  Quantitative Algebras  (Def 3.1 – 3.5)
   ============================================================ *)

(** We axiomatize metrics with values in Q ∪ {∞} using an option:
    None = ∞.  For simplicity in the algebraic sections we often
    assume metrics land in Q (finite); the extended case is noted. *)

(** A carrier with a pseudo-metric (possibly infinite, over Q). *)
Record PseudoMetricSpace := {
  carrier    : Type;
  dist       : carrier -> carrier -> Q;   (* finite approximation *)
  dist_nn    : forall a b, 0 <= dist a b;
  dist_refl  : forall a,   dist a a = 0;
  dist_symm  : forall a b, dist a b = dist b a;
  dist_tri   : forall a b c, dist a c <= dist a b + dist b c;
}.

(** Interpretation of a signature in a pseudo-metric space. *)
Definition algebra_ops (sig : signature) (A : PseudoMetricSpace) :=
  forall (f : sym sig),
    Vector.t (carrier A) (arity sig f) -> carrier A.

(** Non-expansiveness: if d(a_i, b_i) ≤ epsilon for all i then
    d(f(a), f(b)) ≤ epsilon. *)
Definition non_expansive {sig} (A : PseudoMetricSpace)
    (ops : algebra_ops sig A) : Prop :=
  forall (f : sym sig)
         (as_ bs : Vector.t (carrier A) (arity sig f)) epsilon,
    0 <= epsilon ->
    (forall i, dist A (Vector.nth as_ i) (Vector.nth bs i) <= epsilon) ->
    dist A (ops f as_) (ops f bs) <= epsilon.

(** Definition 3.1 — Quantitative Algebra. *)
Record QAlgebra (sig : signature) := {
  qa_metric : PseudoMetricSpace;
  qa_ops    : algebra_ops sig qa_metric;
  qa_nexp   : non_expansive qa_ops;
}.

(** The carrier of a quantitative algebra. *)
Definition qa_carrier {sig} (A : QAlgebra sig) := carrier (qa_metric A).

(** Definition 3.2 — Homomorphism of quantitative algebras.
    A non-expansive Omega-algebra homomorphism. *)
Record QAlgHom {sig} (A B : QAlgebra sig) := {
  hom_fun    : qa_carrier A -> qa_carrier B;
  hom_nexp   : forall a b,
    dist (qa_metric B) (hom_fun a) (hom_fun b) <=
    dist (qa_metric A) a b;
  hom_compat : forall (f : sym sig)
    (v : Vector.t (qa_carrier A) (arity sig f)),
    hom_fun (qa_ops A f v) =
    qa_ops B f (Vector.map hom_fun v);
}.

(** Definition 3.3 — Subalgebra.
    B is a subalgebra of A if its carrier embeds isometrically and
    it is closed under all operations. *)
Record QSubAlgebra {sig} (A B : QAlgebra sig) := {
  sub_embed  : qa_carrier B -> qa_carrier A;
  sub_isom   : forall b b',
    dist (qa_metric A) (sub_embed b) (sub_embed b') =
    dist (qa_metric B) b b';
  sub_closed : forall (f : sym sig)
    (v : Vector.t (qa_carrier B) (arity sig f)),
    sub_embed (qa_ops B f v) =
    qa_ops A f (Vector.map sub_embed v);
}.

(* ============================================================
   §4  Algebraic Semantics  (Def 4.1 – 4.3)
   ============================================================ *)

(** Definition 4.1 — Assignment.
    An assignment iota : X → A, extended homomorphically to terms. *)
Fixpoint eval {sig X} (A : QAlgebra sig) (iota : X -> qa_carrier A)
    (t : term sig X) : qa_carrier A :=
  match t with
  | Var x   => iota x
  | App f v => qa_ops A f (Vector.map (eval A iota) v)
  end.

(** Definition 4.2 — Satisfaction.
    A satisfies Gamma ⊢ s =_epsilon t  if for every assignment iota,
    [ d(iota(lhs h), iota(rhs h)) ≤ eps h  for all h ∈ Gamma ]
    implies d(iota s, iota t) ≤ epsilon. *)
Definition satisfies_inf {sig X} (A : QAlgebra sig)
    (Gamma : ctx sig X) (phi : qeq sig X) : Prop :=
  forall (iota : X -> qa_carrier A),
    (forall h, In h Gamma ->
      dist (qa_metric A) (eval A iota (lhs h)) (eval A iota (rhs h)) <= eps h) ->
    dist (qa_metric A) (eval A iota (lhs phi)) (eval A iota (rhs phi)) <= eps phi.

Notation "A |= Gamma => phi" := (satisfies_inf A Gamma phi) (at level 73).

(** A satisfies an axiom set U if it satisfies every element. *)
Definition models {sig X} (A : QAlgebra sig) (U : axiom_set sig X) : Prop :=
  forall Gamma phi, U Gamma phi -> A |= Gamma => phi.

(** Definition 4.3 — Equational class.
    K(Omega, U) = the class of quantitative algebras satisfying U. *)
Definition eq_class {sig X} (U : axiom_set sig X) (A : QAlgebra sig) : Prop :=
  models A U.

(** Lemma 4.4 — The equational class is closed under subalgebras. *)
Lemma eq_class_subalgebra {sig X} (U : axiom_set sig X)
    (A B : QAlgebra sig) :
  QSubAlgebra A B ->
  eq_class U A ->
  eq_class U B.
Proof.
  intros [embed iso_e closed] HA Gamma phi HU iota Hhyp.
  (* Lift the assignment through the embedding. *)
  set (iota' := fun x => embed (iota x)).
  (* Evaluation commutes with the embedding. *)
  assert (eval_embed : forall t, eval A iota' t = embed (eval B iota t)).
  { fix IH 1.
    intro t.
    destruct t as [x | f v].
    - reflexivity.
    - simpl. rewrite closed. f_equal.
      induction v as [| h n tl IHtl].
      + reflexivity.
      + simpl. f_equal.
        * apply IH.
        * apply IHtl.
  }
  (* The hypotheses hold for iota' in A. *)
  assert (Hhyp_A : forall h, In h Gamma ->
      dist (qa_metric A) (eval A iota' (lhs h)) (eval A iota' (rhs h)) <= eps h).
  { intros h HIn.
    rewrite !eval_embed, iso_e.
    apply Hhyp; exact HIn. }
  (* Apply A's satisfaction. *)
  specialize (HA Gamma phi HU iota' Hhyp_A).
  rewrite !eval_embed, iso_e in HA.
  exact HA.
Qed.

(* ============================================================
   §5  The Induced Pseudometric on Terms  (Section 5)
   ============================================================ *)

(** Given a quantitative equational theory U, define the
    pseudometric on TX:
        d_U(s, t) = inf { epsilon | U ⊢ s =_epsilon t }

    In Rocq we represent this infimum as:
        d_U s t = the greatest lower bound over Q. *)

Section InducedMetric.

  Context {sig : signature} {X : Type} (U : axiom_set sig X).

  (** The set of epsilon values for which U ⊢ s =_epsilon t. *)
  Definition provable_eps (s t : term sig X) : Q -> Prop :=
    fun epsilon => U [] (s ~[epsilon] t).

  (** Proposition 5.1: delta_U(s,t) = 0 for all s,t.
      (The infimum over *conditionally* provable epsilon is always 0.)
      Here we show the unconditional version: for variables x,y
      the trivial derivation x =_epsilon y exists for any epsilon via the
      identity x =_epsilon x and the Subst rule is not needed; instead
      we observe Assumpt + D_Max. *)

  (** Proposition 5.2 and Section 5 main result:
      d_U(s,t) = inf { epsilon | U [] (s ~[epsilon] t) }.
      We state this as a Prop-valued lower bound; a full treatment
      requires the reals.  We record the key statements below. *)

  (** Lower bound: d_U(s,t) ≤ epsilon iff U derives s =_epsilon t
      (unconditionally). *)
  Definition d_U_le (s t : term sig X) (epsilon : Q) : Prop :=
    U [] (s ~[epsilon] t).

  (** d_U(s,t) = 0 iff U ⊢ s =_0 t.  (Uses Arch in the ⇒ dir.) *)
  (** This is a direct consequence of the Archimedean rule; we
      leave it as a lemma skeleton since the real-valued infimum
      is not available without a real-analysis library. *)

  (** The equivalence relation induced by d_U = 0. *)
  Definition term_equiv (s t : term sig X) : Prop :=
    U [] (s ~[0] t).

  (** term_equiv is a congruence (used in §6). *)
  Lemma term_equiv_refl : forall t, term_equiv t t.
  Proof.
    intro t. unfold term_equiv.
    apply DS_Refl.
  Qed.

  Lemma term_equiv_symm : forall s t, term_equiv s t -> term_equiv t s.
  Proof.
    intros s t H. unfold term_equiv in *.
    apply DS_Symm; [lra | exact H].
  Qed.

  Lemma term_equiv_trans : forall s t u,
      term_equiv s t -> term_equiv t u -> term_equiv s u.
  Proof.
    intros s t u Hst Htu. unfold term_equiv in *.
    (* D_Triang gives s =_{0+0} u = s =_0 u *)
    replace 0 with (0 + 0) by lra.
    apply DS_Triang; [lra | lra | exact Hst | exact Htu].
  Qed.

End InducedMetric.

(* ============================================================
   §6  Free Quantitative Algebras  (Section 6)
   ============================================================ *)

(** The free quantitative algebra is the set of terms quotiented
    by 0-provability, equipped with the pseudometric d_U.

    In Rocq we represent the quotient as a setoid (carrier = term,
    equivalence = term_equiv, distance = d_U).

    A full quotient type would require Quotient Types or HITs.
    We therefore work with the underlying term type and a
    setoid equality. *)

Section FreeAlgebra.

  Context {sig : signature} {X : Type} (U : axiom_set sig X).

  (** The term algebra with the 0-provability equivalence. *)
  Definition free_carrier := term sig X.

  (** The "distance" on terms, as a Prop-valued relation on Q. *)
  Definition free_dist (s t : free_carrier) : Q -> Prop :=
    fun epsilon => derives_S U [] (s ~[epsilon] t).

  (** The pseudometric value is the infimum; we record the key
      axiomatic properties it satisfies. *)

  (** d_U(t,t) = 0 *)
  Lemma free_dist_refl : forall t epsilon, 0 <= epsilon -> free_dist t t epsilon.
  Proof.
    intros t epsilon Hepsilon.
    unfold free_dist.
    destruct (Qeq_dec epsilon 0) as [He | Hne].
    - rewrite He. apply DS_Refl.
    - assert (H0 : 0 < epsilon) by lra.
      (* 0 + epsilon > 0, so use Max on the Refl *)
      replace epsilon with (0 + epsilon) by lra.
      apply DS_Max; [lra | lra | apply DS_Refl].
  Qed.

  (** Symmetry *)
  Lemma free_dist_symm : forall s t epsilon,
      0 <= epsilon -> free_dist s t epsilon -> free_dist t s epsilon.
  Proof.
    intros s t epsilon Hepsilon H. unfold free_dist in *.
    apply DS_Symm; assumption.
  Qed.

  (** Triangle inequality *)
  Lemma free_dist_tri : forall s t u epsilon epsilon',
      0 <= epsilon -> 0 <= epsilon' ->
      free_dist s t epsilon -> free_dist t u epsilon' ->
      free_dist s u (epsilon + epsilon').
  Proof.
    intros s t u epsilon epsilon' Hepsilon Hepsilon' Hst Htu. unfold free_dist in *.
    apply DS_Triang with (s := t); assumption.
  Qed.

  (** The operations of the term algebra are non-expansive
      with respect to d_U. *)
  Lemma free_ops_nexp :
    forall (f : sym sig) (ts ss : Vector.t (term sig X) (arity sig f)) epsilon,
    0 <= epsilon ->
    (forall i, free_dist (Vector.nth ts i) (Vector.nth ss i) epsilon) ->
    free_dist (App f ts) (App f ss) epsilon.
  Proof.
    intros f ts ss epsilon Hepsilon Hcomp. unfold free_dist in *.
    apply DS_NExp; assumption.
  Qed.

  (** Lemma 6.1 — term_equiv is a congruence. *)
  Lemma free_equiv_congruence :
    forall (f : sym sig) (xs ys : Vector.t (term sig X) (arity sig f)),
    (forall i, term_equiv U (Vector.nth xs i) (Vector.nth ys i)) ->
    term_equiv U (App f xs) (App f ys).
  Proof.
    intros f xs ys H. unfold term_equiv in *.
    replace 0 with (0 : Q) by lra.
    apply DS_NExp; [lra | intro i; apply H].
  Qed.

  (** Theorem 6.7 — T[M] ∈ K(Omega, U).
      The free term algebra (modulo 0-provability) is a model of U. *)

  (** We state this as: for every axiom (Gamma, phi) in U, the term
      algebra satisfies it under every assignment. *)
  Theorem free_algebra_is_model :
    forall (Gamma : ctx sig X) (phi : qeq sig X),
    U Gamma phi ->
    forall (iota : X -> term sig X),
    (forall h, In h Gamma ->
      free_dist (subst_term iota (lhs h))
                (subst_term iota (rhs h))
                (eps h)) ->
    free_dist (subst_term iota (lhs phi))
              (subst_term iota (rhs phi))
              (eps phi).
  Proof.
    intros Gamma phi HU iota Hhyp.
    unfold free_dist in *.
    (* Use DS_Axiom and DS_Subst: U proves Gamma ⊢ phi, so by DS_Axiom,
       derives_S U Gamma phi; then DS_Subst gives derives_S U sigma(Gamma) sigma(phi);
       and DS_Cut with the hypothesis derivations closes the goal. *)
    apply DS_Cut with (Gamma' := subst_ctx iota Gamma).
    - intros psi HIn.
      unfold subst_ctx in HIn.
      apply in_map_iff in HIn.
      destruct HIn as [h [<- HhIn]].
      apply Hhyp. exact HhIn.
    - apply DS_Subst.
      apply DS_Axiom.
      exact HU.
  Qed.

End FreeAlgebra.

(* ============================================================
   §6  Completeness  (Theorem 6.8)
   ============================================================

   Gamma |=_{K(Omega,U)} phi  iff  U ⊢ Gamma → phi

   Soundness (right-to-left) is a direct consequence of
   free_algebra_is_model above.

   Completeness (left-to-right) uses the free algebra T[X] as a
   witness: if U ∪ Gamma derives s =_e t then the distance in T[X]
   is ≤ e; if not, then e < d_U∪Gamma(s,t) and we get a contradiction.

   A complete Rocq proof requires quotient types and real-valued
   infima.  We record the statement.
   ============================================================ *)

Section Completeness.

  Context {sig : signature} {X : Type} (U : axiom_set sig X).

  (** Semantic entailment w.r.t. the equational class of U. *)
  Definition sem_entails (Gamma : ctx sig X) (phi : qeq sig X) : Prop :=
    forall (A : QAlgebra sig), eq_class U A -> A |= Gamma => phi.

  (** Soundness: syntactic derivability implies semantic validity. *)
  Theorem soundness : forall Gamma phi,
    derives_S U Gamma phi -> sem_entails Gamma phi.
  Proof.
    intros Gamma phi Hderiv A HA.
    unfold eq_class, models in HA.
    (* Proceed by induction on the derivation. *)
    induction Hderiv; intros iota Hhyp.
    - (* D_Refl *) simpl.
      rewrite dist_refl. lra.
    - (* D_Symm *)
      rewrite dist_symm. apply IHHderiv; exact Hhyp.
    - (* D_Triang *)
      eapply Qle_trans; [| apply dist_tri].
      apply Qplus_le_compat.
      + apply IHHderiv1; exact Hhyp.
      + apply IHHderiv2; exact Hhyp.
    - (* D_Max *)
      eapply Qle_trans; [apply IHHderiv; exact Hhyp |].
      lra.
    - (* D_Arch *)
      apply D_Arch_sem; assumption.
    - (* D_NExp *)
      apply qa_nexp. exact H.
      intro i. apply H1; exact Hhyp.
    - (* D_Subst *)
      (* The substituted context matches the hypotheses. *)
      apply IHHderiv.
      intros h HIn.
      unfold subst_ctx in HIn.
      apply in_map_iff in HIn.
      destruct HIn as [h' [<- HIn']].
      unfold subst_qeq. simpl.
      (* eval commutes with subst *)
      admit. (* requires eval_subst lemma *)
    - (* D_Cut *)
      apply IHHderiv.
      intros h HIn.
      apply H0; [exact HIn | exact Hhyp].
    - (* D_Assumpt *)
      apply Hhyp. exact H.
    - (* DS_Axiom *)
      apply HA. exact H.
  Admitted. (* full proof needs eval_subst and D_Arch_sem helpers *)

  (** Completeness statement (Theorem 6.8). *)
  Theorem completeness : forall Gamma phi,
    sem_entails Gamma phi <-> derives_S U Gamma phi.
  Proof.
    intros Gamma phi. split.
    - (* ← direction (completeness proper):
         Use the free algebra T[X] with metric d_{U∪Gamma}.
         If Gamma |-_U phi fails then d_{U∪Gamma}(s,t) > epsilon; contradiction. *)
      admit.  (* Requires quotient types + real-valued infima *)
    - intro H. apply soundness. exact H.
  Admitted.

End Completeness.

(* ============================================================
   §7  Free Algebras over Metric Spaces  (Section 7)
   ============================================================

   The key idea: extend the signature with constant symbols for
   each m ∈ M and add axioms ∅ ⊢ m =_epsilon n whenever d(m,n) ≤ epsilon.
   The resulting freely generated algebra T^d[M] is universal
   among quantitative algebras (in K(Omega,U)) with a non-expansive
   map from (M,d).
   ============================================================ *)

Section FreeOverMetric.

  Context {sig : signature} {X : Type} (U : axiom_set sig X).

  (** Extend the signature with constants from M. *)
  Definition sig_extend (M : Type) : signature := {|
    sym   := sig.(sym) + M;   (* Either an original symbol or a constant *)
    arity := fun sf => match sf with
                       | inl f => sig.(arity) f
                       | inr _ => 0           (* constants have arity 0 *)
                       end;
  |}.

  (** The extended axiom set U_M: U plus the metric axioms. *)
  Definition U_metric (M : Type) (d : M -> M -> Q) : axiom_set (sig_extend M) X :=
    fun Gamma phi =>
      (* Either a U-axiom (lifted to the extended signature) ... *)
      (* or a metric axiom: ∅ ⊢ m =_epsilon n  when d(m,n) ≤ epsilon. *)
      (exists (m n : M) epsilon,
        Gamma = [] /\
        phi = (App (sig := sig_extend M) (inr m) [] ~[epsilon]
             App (sig := sig_extend M) (inr n) []) /\
        d m n <= epsilon /\ 0 <= epsilon).

  (** Theorem 7.2 (statement):
      (T^d[M], eta_M) is a universal arrow from (M,d) to U_Met.
      Full proof deferred (requires real-analysis / metric completion). *)

  (** Theorem 7.3 (statement):
      If (M,d) is non-degenerate, U_M is consistent iff eta_M is
      an isometry. *)

End FreeOverMetric.

(* ============================================================
   §8  Completions  (Section 8)
   ============================================================

   Proposition 8.3: if A satisfies a continuous equation scheme,
   so does its completion.
   Theorem 8.4: T^d[M̄] ≅ T^d[M]̄  (completion commutes with free).

   These results require a real-analysis / complete metric space
   library.  We record the definitions only.
   ============================================================ *)

(** A continuous equation scheme over a signature Omega is a family
    { {x_1 =_{e_1} y_1, …, x_n =_{e_n} y_n} ⊢ s =_{f(e_1,…,e_n)} t
      | e_1, …, e_n ∈ R⁺ }
    where f : R⁺^n → R⁺ is continuous.

    We represent the continuity requirement abstractly via a
    "scheme descriptor". *)

Record ContinuousScheme {sig X} := {
  cs_n      : nat;                              (* number of hypotheses *)
  cs_vars   : Vector.t (X * X) cs_n;           (* (x_i, y_i) pairs *)
  cs_lhs    : term sig X;                       (* s *)
  cs_rhs    : term sig X;                       (* t *)
  cs_f      : Vector.t Q cs_n -> Q;            (* the continuous function f *)
  cs_f_cont : True;                             (* placeholder for continuity *)
}.

(* ============================================================
   §9  Left-Invariant Barycentric Algebras  (Section 9)
   ============================================================ *)

(** The barycentric signature: one binary operator +_e for each
    rational e ∈ [0,1].  We index by Q and assume 0 ≤ e ≤ 1. *)

Definition barycentric_sig : signature := {|
  sym   := Q;      (* the parameter e *)
  arity := fun _ => 2;
|}.

(** The left-invariant barycentric axioms (Def 9.1).
    Variables are drawn from a countable type X.
    We use three distinguished variables for the axiom schemes. *)

Section BarycentricAxioms.

  Context {X : Type} (x x' x'' : X).

  (** We state axioms as elements of axiom_set. *)
  Let t := @Var barycentric_sig X.

  (** Helper: +_e as a term constructor *)
  Definition bary_plus (e : Q) (s u : term barycentric_sig X)
      : term barycentric_sig X :=
    App e [s; u].

  Notation "s [+_{ e }] u" := (bary_plus e s u) (at level 60).

  (** (B1)  ⊢ x +_1 x' =_0 x *)
  Definition ax_B1 : axiom_set barycentric_sig X :=
    fun Gamma phi =>
      Gamma = [] /\
      exists (a b : X),
        phi = (bary_plus 1 (t a) (t b) ~[0] t a).

  (** (B2)  ⊢ x +_e x =_0 x *)
  Definition ax_B2 : axiom_set barycentric_sig X :=
    fun Gamma phi =>
      Gamma = [] /\
      exists (a : X) (e : Q), 0 <= e -> e <= 1 ->
        phi = (bary_plus e (t a) (t a) ~[0] t a).

  (** (SC)  ⊢ x +_e x' =_0 x' +_{1-e} x  (skew commutativity) *)
  Definition ax_SC : axiom_set barycentric_sig X :=
    fun Gamma phi =>
      Gamma = [] /\
      exists (a b : X) (e : Q), 0 <= e -> e <= 1 ->
        phi = (bary_plus e (t a) (t b) ~[0] bary_plus (1 - e) (t b) (t a)).

  (** (LI)  ⊢ x' +_e x =_{epsilon} x'' +_e x  for e ≤ epsilon  (left-invariance) *)
  Definition ax_LI : axiom_set barycentric_sig X :=
    fun Gamma phi =>
      Gamma = [] /\
      exists (a b c : X) (e epsilon : Q),
        0 <= e -> e <= epsilon -> 0 <= epsilon ->
        phi = (bary_plus e (t a) (t c) ~[epsilon] bary_plus e (t b) (t c)).

  (** The full left-invariant barycentric theory U_LI. *)
  Definition U_LI : axiom_set barycentric_sig X :=
    fun Gamma phi =>
      ax_B1  Gamma phi \/ ax_B2  Gamma phi \/
      ax_SC  Gamma phi \/ ax_LI  Gamma phi.
      (* (SA) skew-associativity is omitted here for brevity;
         it follows the same pattern. *)

End BarycentricAxioms.

(** Theorem 9.5 (statement):
    Pi[M] = (finitely-supported distributions over M, total variation)
    is a model of U_LI. *)

(** Theorem 9.6 (statement):
    (Pi[M], delta_M) is the universal arrow from M ∈ Set to U_Set for U_LI.
    Proof: map h sends Sigma c_i delta_{m_i} ↦ Sigma c_i alpha(m_i) in A. *)

(** Corollary 9.7: U_LI axiomatizes the total variation distance. *)

(* ============================================================
   §10  Quantitative Semilattices with Zero  (Section 10)
   ============================================================ *)

(** The semilattice signature: one binary + and one constant 0. *)
Definition semilattice_sig : signature := {|
  sym   := bool;    (* false = binary +, true = constant 0 *)
  arity := fun b => if b then 0 else 2;
|}.

Section SemilatticeAxioms.

  Context {X : Type}.
  Let t := @Var semilattice_sig X.
  Let plus_ (s u : term semilattice_sig X) : term semilattice_sig X :=
    App false [s; u].
  Let zero_ : term semilattice_sig X := App true [].

  (** (S0) ⊢ x + 0 =_0 x *)
  (** (S1) ⊢ x + x =_0 x *)
  (** (S2) ⊢ x + x' =_0 x' + x *)
  (** (S3) ⊢ (x + x') + x'' =_0 x + (x' + x'') *)
  (** (S4) {x =_epsilon y, x' =_{epsilon'} y'} ⊢ x + x' =_{max epsilon epsilon'} y + y' *)

  Definition U_S : axiom_set semilattice_sig X :=
    fun Gamma phi =>
      (* placeholder; axioms follow the same pattern as U_LI *)
      False.

End SemilatticeAxioms.

(** Theorem 10.6 (statement):
    If (M,d) is non-degenerate, T^d[M] is non-degenerate and U_S
    is consistent. *)

(** Theorem 10.7 (statement):
    F[M] = (finite subsets of M, Hausdorff metric) ∈ K(S, U_S). *)

(** Corollary 10.9:
    U_S axiomatizes the Hausdorff distance. *)

(* ============================================================
   §11  Interpolative Barycentric Algebras  (Section 11)
   ============================================================ *)

(** The p-IB theory adds the axiom schema (IB_p):
    {x =_{epsilon_1} y, x' =_{epsilon_2} y'} ⊢ x +_e x' =_delta y +_e y'
    where (e^p epsilon_1^p + (1-e)^p epsilon_2^p)^{1/p} ≤ delta. *)

Section IBAxioms.

  Context {X : Type}.

  (** For a fixed p ≥ 1, the IB_p axiom scheme. *)
  Definition ax_IBp (p : Q) : axiom_set barycentric_sig X :=
    fun Gamma phi =>
      exists (a b c d : X) (e epsilon1 epsilon2 delta : Q),
        1 <= p ->
        0 <= e -> e <= 1 ->
        0 <= epsilon1 -> epsilon1 <= 1 ->
        0 <= epsilon2 -> epsilon2 <= 1 ->
        (** (e^p * epsilon1^p + (1-e)^p * epsilon2^p)^{1/p} ≤ delta *)
        (** We approximate the p-th power / root in Q.  For a full
            treatment one would use a real-analysis library. *)
        True ->   (* placeholder for the numeric condition *)
        Gamma = [Var a ~[epsilon1] Var b; Var c ~[epsilon2] Var d] /\
        phi = (bary_plus e (Var a) (Var c) ~[delta] bary_plus e (Var b) (Var d)).

  Definition U_IB (p : Q) : axiom_set barycentric_sig X :=
    fun Gamma phi =>
      U_LI Gamma phi \/ ax_IBp p Gamma phi.

End IBAxioms.

(** Theorem 11.5 (statement):
    Pi[M] = (finitely-supported distributions, p-Wasserstein metric)
    is a model of U_IB(p). *)

(** Corollary 11.7:
    U_IB axiomatizes the p-Wasserstein metric;
    for p = 1 this is the Kantorovich metric. *)

(* ============================================================
   END OF FILE
   ============================================================ *)
