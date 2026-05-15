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
        Γ ` φ
      where the *hypotheses* Γ are drawn from a fixed ambient
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
From Equations Require Import Equations.

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
Fixpoint subst_term {sig X} (σ : X -> term sig X) (t : term sig X) : term sig X :=
  match t with
  | Var x   => σ x
  | App f v => App f (Vector.map (subst_term σ) v)
  end.

(** Composition of substitutions. *)
Definition subst_comp {sig X} (σ τ : X -> term sig X) : X -> term sig X :=
  fun x => subst_term σ (τ x).

(** Substitution is a homomorphism (standard). *)
Lemma subst_term_comp {sig X} (σ τ : X -> term sig X) (t : term sig X) :
  subst_term σ (subst_term τ t) = subst_term (subst_comp σ τ) t.
Proof.
  revert t.
  (* I use fix as the induction tactic gives no inductive hypothesis *)
  fix IH 1.
  intro t.
  destruct t as [x | f v].
  - reflexivity.
  - simpl. f_equal.
    apply Vector.eq_nth_iff; intros i j Hij.
    rewrite (Vector.nth_map (subst_term σ) (Vector.map (subst_term τ) v) i i Logic.eq_refl).
    rewrite (Vector.nth_map (subst_term τ) v i i Logic.eq_refl).
    rewrite (Vector.nth_map (subst_term (subst_comp σ τ)) v j j Logic.eq_refl).
    subst j.
    apply IH.
Qed.

(* ============================================================
   §2  Quantitative equations and deducibility  (Def 2.1)
   ============================================================ *)

(** A quantitative equation  t =_ε s  over terms. *)
Record qeq (sig : signature) (X : Type) := {
  lhs : term sig X;
  rhs : term sig X;
  eps : Q;
}.

Notation "t ~[ e ] s" := {| lhs := t; rhs := s; eps := e |}
  (at level 70, no associativity).

(** Lift substitution to equations. *)
Definition subst_qeq {sig X} (σ : X -> term sig X) (q : qeq sig X) : qeq sig X :=
  {| lhs := subst_term σ (lhs q);
     rhs := subst_term σ (rhs q);
     eps := eps q |}.

(** A *context* is a (finite) list of quantitative equations used
    as hypotheses.  (The paper writes Γ ⊆ V(TX).) *)
Definition ctx sig X := list (qeq sig X).

(** Apply a substitution to every equation in a context. *)
Definition subst_ctx {sig X} (σ : X -> term sig X) (Γ : ctx sig X) : ctx sig X :=
  List.map (subst_qeq σ) Γ.

(** ----------------------------------------------------------------
    Definition 2.1 — Deducibility relation

    We define a single inductive `derives` that corresponds to the
    smallest deducibility relation.  The rules follow the paper
    exactly; we add non-negativity guards where the paper implicitly
    requires ε, ε' ∈ Q⁺.

    Key fix vs. your original: the premises of Triang / Max / Arch
    / NExp require the hypotheses to be *derivable* from Γ (i.e.
    `Γ |- h`), not merely syntactically present in Γ.  Using `In`
    would only give a *monotone* relation, not closure under Cut.
    ---------------------------------------------------------------- *)

Reserved Notation "Γ |- φ" (at level 72).

Inductive derives (sig : signature) (X : Type)
    : ctx sig X -> qeq sig X -> Prop :=

  (** (Refl)  ∅ ⊢ t =_0 t *)
  | D_Refl : forall Γ t,
      Γ |- (t ~[0] t)

  (** (Symm)  {t =_ε s} ⊢ s =_ε t *)
  | D_Symm : forall Γ t s ε,
      Qnn ε ->
      Γ |- (t ~[ε] s) ->
      Γ |- (s ~[ε] t)

  (** (Triang)  {t =_ε s, s =_ε' u} ⊢ t =_{ε+ε'} u *)
  | D_Triang : forall Γ t s u ε ε',
      Qnn ε -> Qnn ε' ->
      Γ |- (t ~[ε]  s) ->
      Γ |- (s ~[ε'] u) ->
      Γ |- (t ~[ε + ε'] u)

  (** (Max)  for ε' > 0,  {t =_ε s} ⊢ t =_{ε+ε'} s *)
  | D_Max : forall Γ t s ε ε',
      Qnn ε ->
      0 < ε' ->
      Γ |- (t ~[ε] s) ->
      Γ |- (t ~[ε + ε'] s)

  (** Epsilon equality: Coq's rationals use setoid equality [Qeq],
      so the proof system must be closed under equal rational bounds. *)
  | D_EpsEq : forall Γ t s ε δ,
      Qeq ε δ ->
      Γ |- (t ~[ε] s) ->
      Γ |- (t ~[δ] s)

  (** (Arch)  for ε ≥ 0,  {t =_{ε'} s | ε' > ε} ⊢ t =_ε s
      We encode the infinitary premise as a universally quantified
      Rocq hypothesis. *)
  | D_Arch : forall Γ t s ε,
      Qnn ε ->
      (forall ε', ε < ε' -> Γ |- (t ~[ε'] s)) ->
      Γ |- (t ~[ε] s)

  (** (NExp)  f is non-expansive: if each t_i =_ε s_i then
              f(t_1,…,t_n) =_ε f(s_1,…,s_n). *)
  | D_NExp : forall Γ (f : sym sig)
               (ts ss : Vector.t (term sig X) (arity sig f)) ε,
      Qnn ε ->
      (forall i, Γ |- (Vector.nth ts i ~[ε] Vector.nth ss i)) ->
      Γ |- (App f ts ~[ε] App f ss)

  (** (Subst)  if Γ ⊢ t =_ε s then σ(Γ) ⊢ σ(t) =_ε σ(s). *)
  | D_Subst : forall Γ t s ε (σ : X -> term sig X),
      Γ |- (t ~[ε] s) ->
      (subst_ctx σ Γ) |- (subst_term σ t ~[ε] subst_term σ s)

  (** (Cut)  if Γ ⊢ ψ for all ψ ∈ Γ', and Γ' ⊢ φ, then Γ ⊢ φ. *)
  | D_Cut : forall Γ Γ' φ,
      (forall ψ, In ψ Γ' -> Γ |- ψ) ->
      Γ' |- φ ->
      Γ  |- φ

  (** (Assumpt)  if φ ∈ Γ then Γ ⊢ φ. *)
  | D_Assumpt : forall Γ φ,
      In φ Γ ->
      Γ |- φ

  where "Γ |- φ" := (derives Γ φ).

(* ----------------------------------------------------------------
   Basic consequences of the rules
   ---------------------------------------------------------------- *)

(** Weakening: if Γ ⊢ φ and Γ ⊆ Γ' then Γ' ⊢ φ. *)
Lemma derives_weaken {sig X} (Γ Γ' : ctx sig X) φ :
  (forall ψ, In ψ Γ -> In ψ Γ') ->
  Γ  |- φ ->
  Γ' |- φ.
Proof.
  intros Hsub Hjudge.
  apply D_Cut with (Γ' := Γ).
  - intros ψ HIn. apply D_Assumpt. apply Hsub. apply HIn.
  - apply Hjudge.
Qed.

(** The empty context can derive anything derivable from Γ via Cut. *)
Lemma derives_empty_cut {sig X} (Γ : ctx sig X) φ :
  [] |- φ ->
  Γ  |- φ.
Proof.
  intros H.
  apply D_Cut with (Γ' := []).
  - intros ψ HIn. inversion HIn.
  - apply H.
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
       U = { (Γ, φ) | Γ |-_S φ }
   where |-_S is the smallest deducibility relation extending the
   rules of Def 2.1 *and* every element of S.

   We encode this by adding one extra constructor to `derives`. *)

(** A set of axiom schemes (basic inferences). *)
Definition axiom_set (sig : signature) (X : Type) :=
  ctx sig X -> qeq sig X -> Prop.

(** `derives_S S Γ φ` is the deducibility relation generated by
    the rules of Def 2.1 plus S as extra axioms. *)
Inductive derives_S {sig X} (S : axiom_set sig X)
    : ctx sig X -> qeq sig X -> Prop :=

  | DS_Refl   : forall Γ t,          derives_S S Γ (t ~[0] t)
  | DS_Symm   : forall Γ t s ε,
      Qnn ε -> derives_S S Γ (t ~[ε] s) ->
      derives_S S Γ (s ~[ε] t)
  | DS_Triang : forall Γ t s u ε ε',
      Qnn ε -> Qnn ε' ->
      derives_S S Γ (t ~[ε]  s) ->
      derives_S S Γ (s ~[ε'] u) ->
      derives_S S Γ (t ~[ε + ε'] u)
  | DS_Max    : forall Γ t s ε ε',
      Qnn ε -> 0 < ε' ->
      derives_S S Γ (t ~[ε] s) ->
      derives_S S Γ (t ~[ε + ε'] s)
  | DS_EpsEq  : forall Γ t s ε δ,
      Qeq ε δ ->
      derives_S S Γ (t ~[ε] s) ->
      derives_S S Γ (t ~[δ] s)
  | DS_Arch   : forall Γ t s ε,
      Qnn ε ->
      (forall ε', ε < ε' -> derives_S S Γ (t ~[ε'] s)) ->
      derives_S S Γ (t ~[ε] s)
  | DS_NExp   : forall Γ (f : sym sig)
                  (ts ss : Vector.t (term sig X) (arity sig f)) ε,
      Qnn ε ->
      (forall i, derives_S S Γ (Vector.nth ts i ~[ε] Vector.nth ss i)) ->
      derives_S S Γ (App f ts ~[ε] App f ss)
  | DS_Subst  : forall Γ t s ε (σ : X -> term sig X),
      derives_S S Γ (t ~[ε] s) ->
      derives_S S (subst_ctx σ Γ) (subst_term σ t ~[ε] subst_term σ s)
  | DS_Cut    : forall Γ Γ' φ,
      (forall ψ, In ψ Γ' -> derives_S S Γ ψ) ->
      derives_S S Γ' φ ->
      derives_S S Γ φ
  | DS_Assumpt : forall Γ φ,
      In φ Γ -> derives_S S Γ φ

  (** The new constructor: every element of S is an axiom. *)
  | DS_Axiom  : forall Γ φ,
      S Γ φ -> derives_S S Γ φ.

(** Definition 2.2.
    The quantitative equational theory induced by S is the set of
    all unconditional inferences (Γ, φ) derivable via derives_S. *)
Definition qe_theory {sig X} (S : axiom_set sig X) : axiom_set sig X :=
  fun Γ φ => derives_S S Γ φ.

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

(** The paper uses metrics valued in R+ ∪ {∞}. *)

Inductive ExtR : Type :=
  | Fin : R -> ExtR
  | Inf : ExtR.

Equations ExtR_le (x y : ExtR) : Prop :=
ExtR_le (Fin r) (Fin s) := (r <= s)%R;
ExtR_le (Fin _) Inf := True;
ExtR_le Inf (Fin _) := False;
ExtR_le Inf Inf := True.

Equations ExtR_plus (x y : ExtR) : ExtR :=
ExtR_plus (Fin r) (Fin s) := Fin (r + s)%R;
ExtR_plus Inf _ := Inf;
ExtR_plus _ Inf := Inf.

Declare Scope extR_scope.
Delimit Scope extR_scope with extR.
Infix "<=e" := ExtR_le (at level 70, no associativity) : extR_scope.
Infix "+e" := ExtR_plus (at level 50, left associativity) : extR_scope.

Lemma ExtR_le_refl : forall x, ExtR_le x x.
Proof.
  destruct x; simp ExtR_le; lra.
Qed.

Lemma ExtR_le_trans : forall x y z,
    ExtR_le x y -> ExtR_le y z -> ExtR_le x z.
Proof.
  destruct x, y, z; simp ExtR_le; try tauto; lra.
Qed.

(** Paper-faithful metric space: distances are in R+ ∪ {∞}, and
    identity of indiscernibles is part of the structure. *)
Record ExtMetricSpace := {
  ext_carrier : Type;
  ext_dist : ext_carrier -> ext_carrier -> ExtR;
  ext_dist_nn : forall a b, ExtR_le (Fin 0%R) (ext_dist a b);
  ext_dist_refl : forall a, ext_dist a a = Fin 0%R;
  ext_dist_eq0 : forall a b, ext_dist a b = Fin 0%R -> a = b;
  ext_dist_symm : forall a b, ext_dist a b = ext_dist b a;
  ext_dist_tri : forall a b c,
    ExtR_le (ext_dist a c) (ExtR_plus (ext_dist a b) (ext_dist b c));
}.

Definition algebra_ops (sig : signature) (A : ExtMetricSpace) :=
  forall (f : sym sig),
    Vector.t (ext_carrier A) (arity sig f) -> ext_carrier A.

Definition dist_le_Q (A : ExtMetricSpace) (a b : ext_carrier A) (ε : Q) : Prop :=
  ExtR_le (ext_dist A a b) (Fin (Q2R ε)).

Definition non_expansive {sig} (A : ExtMetricSpace)
    (ops : algebra_ops sig A) : Prop :=
  forall (f : sym sig)
         (as_ bs : Vector.t (ext_carrier A) (arity sig f)) ε,
    0 <= ε ->
    (forall i, dist_le_Q A (Vector.nth as_ i) (Vector.nth bs i) ε) ->
    dist_le_Q A (ops f as_) (ops f bs) ε.

(** Definition 3.1 — Quantitative Algebra. *)
Record QAlgebra (sig : signature) := {
  qa_metric : ExtMetricSpace;
  qa_ops    : algebra_ops sig qa_metric;
  qa_nexp   : non_expansive qa_ops;
}.

(** The carrier of a quantitative algebra. *)
Definition qa_carrier {sig} (A : QAlgebra sig) := ext_carrier (qa_metric A).

(** Definition 3.1 — Degenerate quantitative algebra.
    The paper calls A degenerate when its support is empty or a
    singleton.  Equivalently, any two carrier elements are equal. *)
Definition degenerate {sig} (A : QAlgebra sig) : Prop :=
  forall a b : qa_carrier A, a = b.

(** Definition 3.2 — Homomorphism of quantitative algebras.
    A non-expansive Ω-algebra homomorphism. *)
Record QAlgHom {sig} (A B : QAlgebra sig) := {
  hom_fun    : qa_carrier A -> qa_carrier B;
  hom_nexp   : forall a b,
    ExtR_le (ext_dist (qa_metric B) (hom_fun a) (hom_fun b))
            (ext_dist (qa_metric A) a b);
  hom_compat : forall (f : sym sig)
    (v : Vector.t (qa_carrier A) (arity sig f)),
    hom_fun (qa_ops A f v) =
    qa_ops B f (Vector.map hom_fun v);
}.

(** Equality of homomorphisms is extensional equality of their
    underlying maps.  This avoids relying on proof irrelevance for
    the non-expansiveness and compatibility witnesses. *)
Definition same_hom {sig} {A B : QAlgebra sig}
    (h k : QAlgHom A B) : Prop :=
  forall a, hom_fun h a = hom_fun k a.

(** Identity homomorphism. *)
Definition QAlgHom_id {sig} (A : QAlgebra sig) : QAlgHom A A.
Proof.
  refine {| hom_fun := fun a => a |}.
  - intros a b. apply ExtR_le_refl.
  - intros f v. simpl.
    f_equal.
    apply Vector.eq_nth_iff; intros i j Hij.
    rewrite (Vector.nth_map (fun a : qa_carrier A => a) v j j Logic.eq_refl).
    subst j. reflexivity.
Defined.

(** Composition of homomorphisms. *)
Definition QAlgHom_comp {sig} {A B C : QAlgebra sig}
    (g : QAlgHom B C) (h : QAlgHom A B) : QAlgHom A C.
Proof.
  refine {| hom_fun := fun a => hom_fun g (hom_fun h a) |}.
  - intros a b.
    eapply ExtR_le_trans; [apply hom_nexp | apply hom_nexp].
  - intros f v. simpl.
    rewrite hom_compat.
    rewrite hom_compat.
    f_equal.
    induction v as [| a n v IHv].
    + reflexivity.
    + simpl. f_equal. exact IHv.
Defined.

(** Definition 3.3 — Subalgebra.
    B is a subalgebra of A if its carrier embeds isometrically and
    it is closed under all operations. *)
Record QSubAlgebra {sig} (A B : QAlgebra sig) := {
  sub_embed  : qa_carrier B -> qa_carrier A;
  sub_isom   : forall b b',
    ext_dist (qa_metric A) (sub_embed b) (sub_embed b') =
    ext_dist (qa_metric B) b b';
  sub_closed : forall (f : sym sig)
    (v : Vector.t (qa_carrier B) (arity sig f)),
    sub_embed (qa_ops B f v) =
    qa_ops A f (Vector.map sub_embed v);
}.

(** A subcategory K of Ω-QA, represented by its objects and
    permitted homomorphisms, together with identity and composition
    closure. *)
Record QAlgSubcategory (sig : signature) := {
  K_obj : QAlgebra sig -> Prop;
  K_hom : forall {A B : QAlgebra sig}, QAlgHom A B -> Prop;
  K_hom_dom : forall {A B} (h : QAlgHom A B), K_hom h -> K_obj A;
  K_hom_cod : forall {A B} (h : QAlgHom A B), K_hom h -> K_obj B;
  K_id : forall A, K_obj A -> K_hom (QAlgHom_id A);
  K_comp : forall {A B C} (g : QAlgHom B C) (h : QAlgHom A B),
    K_hom g -> K_hom h -> K_hom (QAlgHom_comp g h);
}.

(** Definition 3.4 — Initiality.
    A is initial in a subcategory K of Ω-QA if A is an object of K
    and every object B of K receives a unique K-homomorphism from A. *)
Definition initial_in {sig} (K : QAlgSubcategory sig) (A : QAlgebra sig) : Prop :=
  K_obj K A /\
  forall B, K_obj K B ->
    exists h : QAlgHom A B,
      K_hom K h /\
      forall k : QAlgHom A B, K_hom K k -> same_hom k h.

(** A small category interface, used only for the statement of
    Definition 3.5.  The laws are included so that functors target
    genuine categories, but no later proof depends on a particular
    category library. *)
Record Category := {
  Obj : Type;
  Hom : Obj -> Obj -> Type;
  id  : forall X, Hom X X;
  comp : forall {X Y Z}, Hom Y Z -> Hom X Y -> Hom X Z;
  comp_assoc : forall {W X Y Z}
      (h : Hom Y Z) (g : Hom X Y) (f : Hom W X),
    comp h (comp g f) = comp (comp h g) f;
  comp_id_l : forall {X Y} (f : Hom X Y), comp (id Y) f = f;
  comp_id_r : forall {X Y} (f : Hom X Y), comp f (id X) = f;
}.

(** A functor from a subcategory K of Ω-QA to an arbitrary category C. *)
Record FunctorFromQAlgSubcat {sig}
    (K : QAlgSubcategory sig) (C : Category) := {
  fobj : QAlgebra sig -> Obj C;
  fmap : forall {A B : QAlgebra sig} (h : QAlgHom A B)
      (Hh : K_hom K h),
    Hom C (fobj A) (fobj B);
}.

(** Definition 3.5 — Universal morphism from C0 to G.
    The equation [Gh ◦ α = β] is expressed using [comp] in the
    target category. *)
Definition universal_morphism {sig} {C : Category}
    {K : QAlgSubcategory sig}
    (G : FunctorFromQAlgSubcat K C)
    (C0 : Obj C)
    (A : QAlgebra sig) (HA : K_obj K A)
    (α : Hom C C0 (fobj G A)) : Prop :=
  forall (B : QAlgebra sig) (HB : K_obj K B)
         (β : Hom C C0 (fobj G B)),
    exists h : QAlgHom A B,
      forall (Hh : K_hom K h),
        comp C (fmap G h Hh) α = β /\
        forall (k : QAlgHom A B) (Hk : K_hom K k),
          comp C (fmap G k Hk) α = β -> same_hom k h.

(** A has the universal mapping property for C0 to G when some
    arrow α : C0 -> G A is universal. *)
Definition has_universal_mapping_property {sig} {C : Category}
    {K : QAlgSubcategory sig}
    (G : FunctorFromQAlgSubcat K C)
    (C0 : Obj C)
    (A : QAlgebra sig) (HA : K_obj K A) : Prop :=
  exists α : Hom C C0 (fobj G A),
    universal_morphism G C0 A HA α.

(* ============================================================
   §4  Algebraic Semantics  (Def 4.1 – 4.3)
   ============================================================ *)

(** Definition 4.1 — Assignment.
    An assignment ι : X → A, extended homomorphically to terms. *)
Fixpoint eval {sig X} (A : QAlgebra sig) (ι : X -> qa_carrier A)
    (t : term sig X) : qa_carrier A :=
  match t with
  | Var x   => ι x
  | App f v => qa_ops A f (Vector.map (eval A ι) v)
  end.

Lemma eval_subst {sig X} (A : QAlgebra sig) (ι : X -> qa_carrier A)
    (σ : X -> term sig X) (t : term sig X) :
  eval A ι (subst_term σ t) = eval A (fun x => eval A ι (σ x)) t.
Proof.
  revert t.
  fix IH 1.
  intro t.
  destruct t as [x | f v].
  - reflexivity.
  - simpl. f_equal.
    apply Vector.eq_nth_iff; intros i j Hij.
    rewrite (Vector.nth_map (eval A ι) (Vector.map (subst_term σ) v) i i Logic.eq_refl).
    rewrite (Vector.nth_map (subst_term σ) v i i Logic.eq_refl).
    rewrite (Vector.nth_map (eval A (fun x : X => eval A ι (σ x))) v j j Logic.eq_refl).
    subst j.
    apply IH.
Qed.

(** Definition 4.2 — Satisfaction.
    A satisfies Γ ⊢ s =_ε t  if for every assignment ι,
    [ d(ι(lhs h), ι(rhs h)) ≤ eps h  for all h ∈ Γ ]
    implies d(ι s, ι t) ≤ ε. *)
Definition satisfies_inf {sig X} (A : QAlgebra sig)
    (Γ : ctx sig X) (φ : qeq sig X) : Prop :=
  forall (ι : X -> qa_carrier A),
    (forall h, In h Γ ->
      dist_le_Q (qa_metric A) (eval A ι (lhs h)) (eval A ι (rhs h)) (eps h)) ->
    dist_le_Q (qa_metric A) (eval A ι (lhs φ)) (eval A ι (rhs φ)) (eps φ).

Notation "A |= Γ => φ" := (satisfies_inf A Γ φ) (at level 73).

(** A satisfies an axiom set U if it satisfies every element. *)
Definition models {sig X} (A : QAlgebra sig) (U : axiom_set sig X) : Prop :=
  forall Γ φ, U Γ φ -> A |= Γ => φ.

(** Definition 4.3 — Equational class.
    K(Ω, U) = the class of quantitative algebras satisfying U. *)
Definition eq_class {sig X} (U : axiom_set sig X) (A : QAlgebra sig) : Prop :=
  models A U.

(** Lemma 4.4 — The equational class is closed under subalgebras. *)
Lemma eq_class_subalgebra {sig X} (U : axiom_set sig X)
    (A B : QAlgebra sig) :
  QSubAlgebra A B ->
  eq_class U A ->
  eq_class U B.
Proof.
  intros [embed iso_e closed] HA Γ φ HU ι Hhyp.
  (* Lift the assignment through the embedding. *)
  set (ι' := fun x => embed (ι x)).
  (* Evaluation commutes with the embedding. *)
  assert (eval_embed : forall t, eval A ι' t = embed (eval B ι t)).
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
  (* The hypotheses hold for ι' in A. *)
  assert (Hhyp_A : forall h, In h Γ ->
      dist_le_Q (qa_metric A) (eval A ι' (lhs h)) (eval A ι' (rhs h)) (eps h)).
  { intros h HIn.
    unfold dist_le_Q.
    rewrite !eval_embed, iso_e.
    apply Hhyp; exact HIn. }
  (* Apply A's satisfaction. *)
  specialize (HA Γ φ HU ι' Hhyp_A).
  unfold dist_le_Q in *.
  rewrite !eval_embed, iso_e in HA.
  exact HA.
Qed.

(* ============================================================
   §5  The Induced Pseudometric on Terms  (Section 5)
   ============================================================ *)

(** Given a quantitative equational theory U, define the
    pseudometric on TX:
        d_U(s, t) = inf { ε | U ⊢ s =_ε t }

    The current file does not construct this infimum as a distance
    value.  Instead it records the set of rational bounds and, when
    needed, a Prop-level statement that a real number is its greatest
    lower bound. *)

Section InducedMetric.

  Context {sig : signature} {X : Type} (U : axiom_set sig X).

  (** The set of ε values for which U ⊢ s =_ε t. *)
  Definition provable_eps (s t : term sig X) : Q -> Prop :=
    fun ε => derives_S U [] (s ~[ε] t).

  Definition lower_bound_Qset (P : Q -> Prop) (r : R) : Prop :=
    forall ε, P ε -> (r <= Q2R ε)%R.

  Definition greatest_lower_bound_Qset (P : Q -> Prop) (r : R) : Prop :=
    lower_bound_Qset P r /\
    forall b, lower_bound_Qset P b -> (b <= r)%R.

  Definition d_U_is_infimum (s t : term sig X) (r : R) : Prop :=
    greatest_lower_bound_Qset (provable_eps s t) r.

  (** Proposition 5.1: δ_U(s,t) = 0 for all s,t.
      (The infimum over *conditionally* provable ε is always 0.)
      Here we show the unconditional version: for variables x,y
      the trivial derivation x =_ε y exists for any ε via the
      identity x =_ε x and the Subst rule is not needed; instead
      we observe Assumpt + D_Max. *)

  (** Proposition 5.2 and Section 5 main result:
      d_U(s,t) = inf { ε | U [] (s ~[ε] t) }.
      We state this through [d_U_is_infimum], not by defining a
      computable distance value. *)

  (** Lower bound: d_U(s,t) ≤ ε iff U derives s =_ε t
      (unconditionally). *)
  Definition d_U_le (s t : term sig X) (ε : Q) : Prop :=
    derives_S U [] (s ~[ε] t).

  (** d_U(s,t) = 0 iff U ⊢ s =_0 t.  (Uses Arch in the ⇒ dir.) *)
  (** This is a direct consequence of the Archimedean rule; we
      leave it as a lemma skeleton since the real-valued infimum
      is not available without a real-analysis library. *)

  (** The equivalence relation induced by d_U = 0. *)
  Definition term_equiv (s t : term sig X) : Prop :=
    derives_S U [] (s ~[0] t).

  (** term_equiv is a congruence (used in §6). *)
  Lemma term_equiv_refl : forall t, term_equiv t t.
  Proof.
    intro t. unfold term_equiv.
    apply DS_Refl.
  Qed.

  Lemma term_equiv_symm : forall s t, term_equiv s t -> term_equiv t s.
  Proof.
    intros s t H. unfold term_equiv in *.
    apply DS_Symm; [lra | apply H].
  Qed.

  Lemma term_equiv_trans : forall s t u,
      term_equiv s t -> term_equiv t u -> term_equiv s u.
  Proof.
    intros s t u Hst Htu. unfold term_equiv in *.
    eapply DS_Triang with (s := t) (ε := 0) (ε' := 0);
      [lra | lra | apply Hst | apply Htu].
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
    fun ε => derives_S U [] (s ~[ε] t).

  (** The pseudometric value is the infimum; we record the key
      axiomatic properties it satisfies. *)

  (** d_U(t,t) = 0 *)
  Lemma free_dist_refl : forall t ε, 0 <= ε -> free_dist t t ε.
  Proof.
    intros t ε Hε.
    unfold free_dist.
    destruct (Qle_lt_or_eq 0 ε Hε) as [Hpos | Hz].
    - eapply DS_EpsEq with (ε := 0 + ε).
      + lra.
      + apply DS_Max; [lra | exact Hpos | apply DS_Refl].
    - eapply DS_EpsEq with (ε := 0).
      + exact Hz.
      + apply DS_Refl.
  Qed.

  (** Symmetry *)
  Lemma free_dist_symm : forall s t ε,
      0 <= ε -> free_dist s t ε -> free_dist t s ε.
  Proof.
    intros s t ε Hε H. unfold free_dist in *.
    apply DS_Symm; assumption.
  Qed.

  (** Triangle inequality *)
  Lemma free_dist_tri : forall s t u ε ε',
      0 <= ε -> 0 <= ε' ->
      free_dist s t ε -> free_dist t u ε' ->
      free_dist s u (ε + ε').
  Proof.
    intros s t u ε ε' Hε Hε' Hst Htu. unfold free_dist in *.
    apply DS_Triang with (s := t); assumption.
  Qed.

  (** The operations of the term algebra are non-expansive
      with respect to d_U. *)
  Lemma free_ops_nexp :
    forall (f : sym sig) (ts ss : Vector.t (term sig X) (arity sig f)) ε,
    0 <= ε ->
    (forall i, free_dist (Vector.nth ts i) (Vector.nth ss i) ε) ->
    free_dist (App f ts) (App f ss) ε.
  Proof.
    intros f ts ss ε Hε Hcomp. unfold free_dist in *.
    apply DS_NExp; assumption.
  Qed.

  (** Lemma 6.1 — term_equiv is a congruence. *)
  Lemma free_equiv_congruence :
    forall (f : sym sig) (xs ys : Vector.t (term sig X) (arity sig f)),
    (forall i, term_equiv U (Vector.nth xs i) (Vector.nth ys i)) ->
    term_equiv U (App f xs) (App f ys).
  Proof.
    intros f xs ys H. unfold term_equiv in *.
    apply DS_NExp; [lra | intro i; apply H].
  Qed.

  (** Theorem 6.7 — T[M] ∈ K(Ω, U).
      The free term algebra (modulo 0-provability) is a model of U. *)

  (** We state this as: for every axiom (Γ, φ) in U, the term
      algebra satisfies it under every assignment. *)
  Theorem free_algebra_is_model :
    forall (Γ : ctx sig X) (φ : qeq sig X),
    U Γ φ ->
    forall (ι : X -> term sig X),
    (forall h, In h Γ ->
      free_dist (subst_term ι (lhs h))
                (subst_term ι (rhs h))
                (eps h)) ->
    free_dist (subst_term ι (lhs φ))
              (subst_term ι (rhs φ))
              (eps φ).
  Proof.
    intros Γ φ HU ι Hhyp.
    destruct φ as [φ_lhs φ_rhs φ_eps]; simpl in *.
    unfold free_dist in *.
    (* Use DS_Axiom and DS_Subst: U proves Γ ⊢ φ, so by DS_Axiom,
       derives_S U Γ φ; then DS_Subst gives derives_S U σ(Γ) σ(φ);
       and DS_Cut with the hypothesis derivations closes the goal. *)
    apply DS_Cut with (Γ' := subst_ctx ι Γ).
    - intros ψ HIn.
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

   Γ |=_{K(Ω,U)} φ  iff  U ⊢ Γ → φ

   Soundness (right-to-left) is a direct consequence of
   free_algebra_is_model above.

   Completeness (left-to-right) uses the free algebra T[X] as a
   witness: if U ∪ Γ derives s =_e t then the distance in T[X]
   is ≤ e; if not, then e < d_U∪Γ(s,t) and we get a contradiction.

   A complete Rocq proof requires quotient types and real-valued
   infima.  We record the statement.
   ============================================================ *)

Section Completeness.

  Context {sig : signature} {X : Type} (U : axiom_set sig X).

  (** Semantic entailment w.r.t. the equational class of U. *)
  Definition sem_entails (Γ : ctx sig X) (φ : qeq sig X) : Prop :=
    forall (A : QAlgebra sig), eq_class U A -> A |= Γ => φ.

  (** Soundness: syntactic derivability implies semantic validity. *)
  Theorem soundness : forall Γ φ,
    derives_S U Γ φ -> sem_entails Γ φ.
  Proof.
    (* The previous proof used the finite Q-valued pseudometric
       directly.  With the paper-faithful R+ ∪ {∞}-valued metric this
       needs the corresponding extended-real order lemmas, especially
       for Triang, Max, EpsEq, and Arch. *)
    admit.
  Admitted.

  (** Completeness statement (Theorem 6.8). *)
  Theorem completeness : forall Γ φ,
    sem_entails Γ φ <-> derives_S U Γ φ.
  Proof.
    intros Γ φ. split.
    - (* ← direction (completeness proper):
         Use the free algebra T[X] with metric d_{U∪Γ}.
         If Γ |-_U φ fails then d_{U∪Γ}(s,t) > ε; contradiction. *)
      admit.  (* Requires quotient types + real-valued infima *)
    - intro H. apply soundness. exact H.
  Admitted.

End Completeness.

(* ============================================================
   §7  Free Algebras over Metric Spaces  (Section 7)
   ============================================================

   The key idea: extend the signature with constant symbols for
   each m ∈ M and add axioms ∅ ⊢ m =_ε n whenever d(m,n) ≤ ε.
   The resulting freely generated algebra T^d[M] is universal
   among quantitative algebras (in K(Ω,U)) with a non-expansive
   map from (M,d).
   ============================================================ *)

Section FreeOverMetric.

  Context {sig : signature} {X : Type} (U : axiom_set sig X).

  (** Extend the signature with constants from M. *)
  Definition sig_extend (M : Type) : signature := {|
    sym   := sig.(sym) + M;   (* Either an original symbol or a constant *)
    arity := fun sf => match sf with
                       | inl f => sig.(arity) f
                       | inr _ => 0%nat       (* constants have arity 0 *)
                       end;
  |}.

  (** The extended axiom set U_M: U plus the metric axioms. *)
  Definition U_metric (M : Type) (d : M -> M -> Q) : axiom_set (sig_extend M) X :=
    fun Γ φ =>
      (* Either a U-axiom (lifted to the extended signature) ... *)
      (* or a metric axiom: ∅ ⊢ m =_ε n  when d(m,n) ≤ ε. *)
      (exists (m n : M) ε,
        Γ = [] /\
        φ = (App (sig := sig_extend M) (inr m) []%vector ~[ε]
             App (sig := sig_extend M) (inr n) []%vector) /\
        d m n <= ε /\ 0 <= ε).

  (** Theorem 7.2 (statement):
      (T^d[M], η_M) is a universal arrow from (M,d) to U_Met.
      Full proof deferred (requires real-analysis / metric completion). *)

  (** Theorem 7.3 (statement):
      If (M,d) is non-degenerate, U_M is consistent iff η_M is
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

(** A continuous equation scheme over a signature Ω is a family
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
  arity := fun _ => 2%nat;
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
    App (sig := barycentric_sig) e [s; u]%vector.

  Notation "s [+_{ e }] u" := (bary_plus e s u) (at level 60).

  (** (B1)  ⊢ x +_1 x' =_0 x *)
  Definition ax_B1 : axiom_set barycentric_sig X :=
    fun Γ φ =>
      Γ = [] /\
      exists (a b : X),
        φ = (bary_plus 1 (t a) (t b) ~[0] t a).

  (** (B2)  ⊢ x +_e x =_0 x *)
  Definition ax_B2 : axiom_set barycentric_sig X :=
    fun Γ φ =>
      Γ = [] /\
      exists (a : X) (e : Q), 0 <= e -> e <= 1 ->
        φ = (bary_plus e (t a) (t a) ~[0] t a).

  (** (SC)  ⊢ x +_e x' =_0 x' +_{1-e} x  (skew commutativity) *)
  Definition ax_SC : axiom_set barycentric_sig X :=
    fun Γ φ =>
      Γ = [] /\
      exists (a b : X) (e : Q), 0 <= e -> e <= 1 ->
        φ = (bary_plus e (t a) (t b) ~[0] bary_plus (1 - e) (t b) (t a)).

  (** (LI)  ⊢ x' +_e x =_{ε} x'' +_e x  for e ≤ ε  (left-invariance) *)
  Definition ax_LI : axiom_set barycentric_sig X :=
    fun Γ φ =>
      Γ = [] /\
      exists (a b c : X) (e ε : Q),
        0 <= e -> e <= ε -> 0 <= ε ->
        φ = (bary_plus e (t a) (t c) ~[ε] bary_plus e (t b) (t c)).

  (** The full left-invariant barycentric theory U_LI. *)
  Definition U_LI : axiom_set barycentric_sig X :=
    fun Γ φ =>
      ax_B1  Γ φ \/ ax_B2  Γ φ \/
      ax_SC  Γ φ \/ ax_LI  Γ φ.
      (* (SA) skew-associativity is omitted here for brevity;
         it follows the same pattern. *)

End BarycentricAxioms.

(** Theorem 9.5 (statement):
    Π[M] = (finitely-supported distributions over M, total variation)
    is a model of U_LI. *)

(** Theorem 9.6 (statement):
    (Π[M], δ_M) is the universal arrow from M ∈ Set to U_Set for U_LI.
    Proof: map h sends Σ c_i δ_{m_i} ↦ Σ c_i α(m_i) in A. *)

(** Corollary 9.7: U_LI axiomatizes the total variation distance. *)

(* ============================================================
   §10  Quantitative Semilattices with Zero  (Section 10)
   ============================================================ *)

(** The semilattice signature: one binary + and one constant 0. *)
Definition semilattice_sig : signature := {|
  sym   := bool;    (* false = binary +, true = constant 0 *)
  arity := fun b => if b then 0%nat else 2%nat;
|}.

Section SemilatticeAxioms.

  Context {X : Type}.
  Let t := @Var semilattice_sig X.
  Let plus_ (s u : term semilattice_sig X) : term semilattice_sig X :=
    App (sig := semilattice_sig) false [s; u]%vector.
  Let zero_ : term semilattice_sig X :=
    App (sig := semilattice_sig) true []%vector.

  (** (S0) ⊢ x + 0 =_0 x *)
  (** (S1) ⊢ x + x =_0 x *)
  (** (S2) ⊢ x + x' =_0 x' + x *)
  (** (S3) ⊢ (x + x') + x'' =_0 x + (x' + x'') *)
  (** (S4) {x =_ε y, x' =_{ε'} y'} ⊢ x + x' =_{max ε ε'} y + y' *)

  Definition U_S : axiom_set semilattice_sig X :=
    fun Γ φ =>
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
    {x =_{ε_1} y, x' =_{ε_2} y'} ⊢ x +_e x' =_δ y +_e y'
    where (e^p ε_1^p + (1-e)^p ε_2^p)^{1/p} ≤ δ. *)

Section IBAxioms.

  Context {X : Type}.

  (** For a fixed p ≥ 1, the IB_p axiom scheme. *)
  Definition ax_IBp (p : Q) : axiom_set barycentric_sig X :=
    fun Γ φ =>
      exists (a b c d : X) (e ε1 ε2 δ : Q),
        1 <= p ->
        0 <= e -> e <= 1 ->
        0 <= ε1 -> ε1 <= 1 ->
        0 <= ε2 -> ε2 <= 1 ->
        (** (e^p * ε1^p + (1-e)^p * ε2^p)^{1/p} ≤ δ *)
        (** We approximate the p-th power / root in Q.  For a full
            treatment one would use a real-analysis library. *)
        True ->   (* placeholder for the numeric condition *)
        Γ = [Var a ~[ε1] Var b; Var c ~[ε2] Var d] /\
        φ = (bary_plus e (Var a) (Var c) ~[δ] bary_plus e (Var b) (Var d)).

  Definition U_IB (p : Q) : axiom_set barycentric_sig X :=
    fun Γ φ =>
      U_LI Γ φ \/ ax_IBp p Γ φ.

End IBAxioms.

(** Theorem 11.5 (statement):
    Π[M] = (finitely-supported distributions, p-Wasserstein metric)
    is a model of U_IB(p). *)

(** Corollary 11.7:
    U_IB axiomatizes the p-Wasserstein metric;
    for p = 1 this is the Kantorovich metric. *)

(* ============================================================
   END OF FILE
   ============================================================ *)
