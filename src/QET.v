(* ============================================================
   Quantitative equational theories as enriched Lawvere theories
   ============================================================ *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Lists.List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq choice fintype.
From mathcomp Require Import order ssralg ssrnum archimedean reals ereal.
From mathcomp Require Import classical_sets.

From Template Require Export Signature.
From Template Require Import Metric Category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

Notation Rnn r := (0 <= r)%R.

Lemma Rnn_add {R : realType} : forall p q : R,
  Rnn p -> Rnn q -> Rnn (p + q).
Proof. apply: addr_ge0. Qed.

Lemma Rnn_zero {R : realType} : Rnn (0 : R).
Proof. apply: lexx. Qed.

Definition nonneg_real (R : realType) := {r : R | Rnn r}.

Definition nonneg_real_val {R : realType} (eps : nonneg_real R) : R :=
  sval eps.

Lemma nonneg_real_val_ge0 {R : realType} (eps : nonneg_real R) :
  (0 <= nonneg_real_val eps)%R.
Proof. exact: (svalP eps). Qed.

(* ============================================================
   Quantitative equations and axiom schemes
   ============================================================ *)

Record qeq (R : realType) (sig : signature) (X : Type) := {
  lhs : term sig X;
  rhs : term sig X;
  eps : R;
}.

Notation "t ~[ e ] s" := {| lhs := t; rhs := s; eps := e |}
  (at level 70, no associativity).

Definition subst_qeq {R : realType} {sig X Y}
    (sigma : X -> term sig Y) (q : qeq R sig X) : qeq R sig Y :=
  {| lhs := subst_term sigma (lhs q);
     rhs := subst_term sigma (rhs q);
     eps := eps q |}.

Definition ctx (R : realType) sig X := seq (qeq R sig X).

Definition subst_ctx {R : realType} {sig X Y}
    (sigma : X -> term sig Y) : ctx R sig X -> ctx R sig Y :=
  map (subst_qeq sigma).

Definition axiom_scheme (R : realType) (sig : signature) :=
  forall (X : Type), ctx R sig X -> qeq R sig X -> Prop.

Inductive derives {R : realType} {sig} (U : axiom_scheme R sig)
    : forall X : Type, ctx R sig X -> qeq R sig X -> Prop :=
  | D_Refl : forall X Gamma t,
      @derives R sig U X Gamma (t ~[0] t)
  | D_Symm : forall X Gamma t s eps,
      Rnn eps ->
      @derives R sig U X Gamma (t ~[eps] s) ->
      @derives R sig U X Gamma (s ~[eps] t)
  | D_Triang : forall X Gamma t s u eps eps',
      Rnn eps -> Rnn eps' ->
      @derives R sig U X Gamma (t ~[eps] s) ->
      @derives R sig U X Gamma (s ~[eps'] u) ->
      @derives R sig U X Gamma (t ~[eps + eps'] u)
  | D_Max : forall X Gamma t s eps eps',
      Rnn eps -> (0 < eps')%R ->
      @derives R sig U X Gamma (t ~[eps] s) ->
      @derives R sig U X Gamma (t ~[eps + eps'] s)
  | D_Arch : forall X Gamma t s eps,
      Rnn eps ->
      (forall eps', (eps < eps')%R ->
        @derives R sig U X Gamma (t ~[eps'] s)) ->
      @derives R sig U X Gamma (t ~[eps] s)
  | D_NExp : forall X Gamma (f : sym sig)
                     (ts ss : 'I_(arity f) -> term sig X) eps,
      Rnn eps ->
      (forall i, @derives R sig U X Gamma (ts i ~[eps] ss i)) ->
      @derives R sig U X Gamma (App f ts ~[eps] App f ss)
  | D_Subst : forall X Y Gamma t s eps
                       (sigma : X -> term sig Y),
      @derives R sig U X Gamma (t ~[eps] s) ->
      @derives R sig U Y (subst_ctx sigma Gamma)
        (subst_term sigma t ~[eps] subst_term sigma s)
  | D_Cut : forall X Gamma Gamma' phi,
      (forall psi, List.In psi Gamma' -> @derives R sig U X Gamma psi) ->
      @derives R sig U X Gamma' phi ->
      @derives R sig U X Gamma phi
  | D_Assumpt : forall X Gamma phi,
      List.In phi Gamma ->
      @derives R sig U X Gamma phi
  | D_Axiom : forall X Gamma phi,
      U X Gamma phi -> @derives R sig U X Gamma phi.

Arguments D_Refl {R sig U X Gamma} t.
Arguments D_Symm {R sig U X Gamma t s eps} _ _.
Arguments D_Triang {R sig U X Gamma t s u eps eps'} _ _ _ _.
Arguments D_NExp {R sig U X Gamma f ts ss eps} _ _.
Arguments D_Subst {R sig U X Y Gamma t s eps} sigma _.
Arguments D_Axiom {R sig U X Gamma phi} _.

Lemma subst_term_nexp {R : realType} {sig X Y} (U : axiom_scheme R sig)
    (eps : R) (sigma tau : X -> term sig Y) (t : term sig X) :
  Rnn eps ->
  (forall x, @derives R sig U Y [::] (sigma x ~[eps] tau x)) ->
  @derives R sig U Y [::] (subst_term sigma t ~[eps] subst_term tau t).
Proof.
  move=> Heps Hvars.
  elim: t => [x | f args IH] //=.
  apply: D_NExp; first exact Heps.
  move=> i.
  exact: IH.
Qed.

(* ============================================================
   Quantitative algebras and semantic interpretation
   ============================================================ *)

(** A quantitative algebra consists of an extended metric space, an
    interpretation of every operation symbol, and a proof that all
    interpreted operations are non-expansive. *)
Record QAlgebra (R : realType) (sig : signature) := {
  qa_metric : ext_metric_space R;
  qa_ops : algebra_ops sig (carrier qa_metric);
  qa_nexp : non_expansive (M := qa_metric) qa_ops;
}.

Definition qa_carrier {R sig} (A : QAlgebra R sig) : Type :=
  carrier (qa_metric A).

Fixpoint eval {R sig X} (A : QAlgebra R sig)
    (rho : X -> qa_carrier A) (t : term sig X) : qa_carrier A :=
  match t with
  | Var x => rho x
  | App f args => qa_ops (fun i => @eval R sig X A rho (args i))
  end.

Lemma eval_subst {R sig X Y} (A : QAlgebra R sig)
    (rho : Y -> qa_carrier A) (sigma : X -> term sig Y)
    (t : term sig X) :
  eval rho (subst_term sigma t) =
  eval (eval rho \o sigma) t.
Proof.
  elim: t => [x | f args IH] //=.
  congr (qa_ops _).
  apply functional_extensionality => i.
  exact: IH.
Qed.

(** Semantic validity of a quantitative equation under a valuation. *)
Definition qdist_le {R : realType} {sig X} (A : QAlgebra R sig)
    (rho : X -> qa_carrier A) (phi : qeq R sig X) : Prop :=
  @dist_le R (qa_metric A)
    (eval rho (lhs phi)) (eval rho (rhs phi)) (eps phi).

(** A conditional equation holds when every valuation satisfying its
    finite premise context also satisfies its conclusion. *)
Definition satisfies_inf {R : realType} {sig X} (A : QAlgebra R sig)
    (Gamma : ctx R sig X) (phi : qeq R sig X) : Prop :=
  forall rho,
    (forall psi, List.In psi Gamma -> @qdist_le R sig X A rho psi) ->
    @qdist_le R sig X A rho phi.

(** A quantitative algebra models an axiom scheme at every variable type. *)
Definition models {R : realType} {sig}
    (A : QAlgebra R sig) (U : axiom_scheme R sig) : Prop :=
  forall X Gamma phi, U X Gamma phi -> @satisfies_inf R sig X A Gamma phi.

(* ============================================================
   The Induced Pseudometric
   ============================================================ *)

Definition d_U {R : realType} {sig X} (U : axiom_scheme R sig)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nonneg_real_val R) (
    fun eps => derives U [::] (s ~[nonneg_real_val eps] t)
  ).

Definition gamma_U {R : realType} {sig X} (U : axiom_scheme R sig)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nonneg_real_val R) (
    fun eps => forall Gamma, derives U Gamma (s ~[nonneg_real_val eps] t)
  ).

Definition delta_U {R : realType} {sig X} (U : axiom_scheme R sig)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nonneg_real_val R) (
    fun eps => exists Gamma, derives U Gamma (s ~[nonneg_real_val eps] t)
  ).

Lemma delta_U_context_witness {R : realType} {sig X}
    (U : axiom_scheme R sig) (s t : term sig X) (eps : nonneg_real R) :
  exists Gamma, derives U Gamma (s ~[nonneg_real_val eps] t).
Proof.
  exists [:: s ~[nonneg_real_val eps] t].
  apply: D_Assumpt.
  by left.
Qed.

Proposition delta_U_zero {R : realType} {sig X}
    (U : axiom_scheme R sig) (s t : term sig X) :
  @delta_U R sig X U s t = 0.
Proof.
  apply: Order.POrderTheory.le_anti.
  rewrite /delta_U /extended_infimum.
  apply/andP; split.
  - apply: ge_ereal_inf.
    exists (0%:E : \bar R); [ | apply lexx].
    exists (0 : R)%R; [ | by []].
    exists (exist _ (0 : R)%R Rnn_zero).
    split.
    + apply: delta_U_context_witness.
    + reflexivity.
  - rewrite /delta_U /extended_infimum.
    have Hlb :
        (0%R <= ereal_inf
          (EFin @` bound_set (@nonneg_real_val R)
            (fun eps : nonneg_real R =>
              exists Gamma : ctx R sig X,
                derives U Gamma (s ~[nonneg_real_val eps] t))))%E.
    { apply/ereal_infP => y Himg.
      case: Himg => r Hb <-.
      case: Hb => eps [_ Hr].
      rewrite Hr.
      apply: lee_tofin.
      exact: nonneg_real_val_ge0.
    }
    exact Hlb.
Qed.

Lemma derives_empty_cut {R : realType} {sig X} (U : axiom_scheme R sig)
    (Gamma : ctx R sig X) phi :
  derives U [::] phi -> derives U Gamma phi.
Proof.
  move=> H.
  apply: (D_Cut (Gamma' := [::])).
  - move=> psi Hpsi. inversion Hpsi.
  - exact H.
Qed.

Proposition gamma_U_eq_d_U {R : realType} {sig X}
    (U : axiom_scheme R sig) (s t : term sig X) :
  @gamma_U R sig X U s t = @d_U R sig X U s t.
Proof.
  rewrite /gamma_U /d_U /extended_infimum /bound_set.
  congr ereal_inf.
  apply/seteqP; split=> r.
  - move=> H.
    case: H => x Hbound Hfin.
    move: Hbound => [eps [Hderive Hx]].
    exists x.
    + exists eps; split.
      * exact: (Hderive [::]).
      * exact Hx.
    + exact Hfin.
  - move=> H.
    case: H => x Hbound Hfin.
    move: Hbound => [eps [Hderive Hx]].
    exists x.
    + exists eps; split.
      * move=> Gamma.
        exact: derives_empty_cut Hderive.
      * exact Hx.
    + exact Hfin.
Qed.

Lemma d_U_refl {R : realType} {sig X}
    (U : axiom_scheme R sig) (s : term sig X) :
    @d_U R sig X U s s = 0.
Proof.
  apply: Order.POrderTheory.le_anti.
  apply /andP; split.
  - rewrite /d_U /extended_infimum.
    apply: ge_ereal_inf.
    exists (0%:E : \bar R); last exact: lexx.
    exists (0 : R)%R; last by [].
    exists (exist _ (0 : R)%R Rnn_zero).
    split.
    + exact: D_Refl.
    + reflexivity.
  - rewrite /d_U /extended_infimum.
    apply/ereal_infP => y Himg.
    case: Himg => r Hb <-.
    case: Hb => eps [_ Hr].
    rewrite Hr.
    apply: lee_tofin.
    exact: nonneg_real_val_ge0.
Qed.

Lemma d_U_symm {R : realType} {sig X}
    (U : axiom_scheme R sig) (s t : term sig X) :
    @d_U R sig X U s t = @d_U R sig X U t s.
Proof.
  rewrite /d_U /extended_infimum /bound_set.
  congr ereal_inf.
  apply/seteqP; split=> r.
  - move=> H.
    case: H => x Hbound Hfin.
    move: Hbound => [eps [Hderive Hx]].
    exists x.
    + exists eps; split.
      * apply: D_Symm; first exact: (svalP eps).
        exact Hderive.
      * exact Hx.
    + exact Hfin.
  - move=> H.
    case: H => x Hbound Hfin.
    move: Hbound => [eps [Hderive Hx]].
    exists x.
    + exists eps; split.
      * apply: D_Symm; first exact: (svalP eps).
        exact Hderive.
      * exact Hx.
    + exact Hfin.
Qed.

Lemma d_U_nonneg {R : realType} {sig X}
    (U : axiom_scheme R sig) (s t : term sig X) :
  0 <= @d_U R sig X U s t.
Proof.
  rewrite /d_U /extended_infimum.
  apply/ereal_infP => y Himg.
  case: Himg => r Hb <-.
  case: Hb => eps [_ Hr].
  rewrite Hr.
  apply: lee_tofin.
  exact: nonneg_real_val_ge0.
Qed.

Lemma d_U_le_derives {R : realType} {sig X}
    (U : axiom_scheme R sig) (s t : term sig X) (eps : R) :
  Rnn eps ->
  derives U [::] (s ~[eps] t) ->
  @d_U R sig X U s t <= eps%:E.
Proof.
  move=> Heps Hderive.
  rewrite /d_U /extended_infimum.
  apply: ge_ereal_inf.
  exists (eps%:E : \bar R); last exact: lexx.
  exists eps; last by [].
  exists (exist _ eps Heps).
  split; first exact Hderive.
  reflexivity.
Qed.

(** Greatest-lower-bound elimination principle for [d_U].  To prove that a
    candidate extended real lies below [d_U U s t], it is enough to prove
    that it lies below every non-negative derivable error bound. *)
Lemma d_U_greatest_lower_bound {R : realType} {sig X}
    (U : axiom_scheme R sig) (s t : term sig X) (b : \bar R) :
  (forall eps : R, Rnn eps ->
    derives U [::] (s ~[eps] t) -> b <= eps%:E) ->
  b <= @d_U R sig X U s t.
Proof.
  move=> Hlower.
  rewrite /d_U /extended_infimum.
  apply/ereal_infP => y Himg.
  case: Himg => r Hb <-.
  case: Hb => eps [Hderive Hr].
  rewrite Hr.
  exact: Hlower (nonneg_real_val_ge0 eps) Hderive.
Qed.

Lemma ene_neq_ninfty {R : realType} (x : \bar R) :
  (0%:E <= x)%E -> x != -oo%E.
Proof.
  move=> Hx.
  rewrite -ltNye.
  exact: (lt_le_trans (ltNyr (0 : R)) Hx).
Qed.

Lemma ene_nonneg_fin_or_pinfty {R : realType} (x : \bar R) :
  (0%:E <= x)%E -> x \is a fin_num \/ x = +oo%E.
Proof.
  move=> Hx.
  case Hfin: (x \is a fin_num); first by left.
  right.
  move/fin_numPn: Hfin => [HxN|HxP]; last exact HxP.
  exfalso.
  move: Hx.
  by rewrite HxN.
Qed.

Lemma adde_eps_split {R : realType} (A B : \bar R) (e : R) :
  A \is a fin_num -> B \is a fin_num ->
  (A + (e / 2)%:E + (B + (e / 2)%:E) = A + B + e%:E)%E.
Proof.
  move=> Afin Bfin.
  rewrite -[A]fineK// -[B]fineK//.
  rewrite -!EFinD /=.
  have -> :
      (fine A + e / 2 + (fine B + e / 2) = fine A + fine B + e)%R.
  { by rewrite addrACA -splitr. }
  reflexivity.
Qed.

Lemma d_U_tri_bound {R : realType} {sig X}
    (U : axiom_scheme R sig) (s t u : term sig X) (eps eps' : R) :
  Rnn eps ->
  Rnn eps' ->
  derives U [::] (s ~[eps] t) ->
  derives U [::] (t ~[eps'] u) ->
  @d_U R sig X U s u <= eps%:E + eps'%:E.
Proof.
  move=> Heps Heps' Hst Htu.
  rewrite -EFinD.
  apply: d_U_le_derives.
  - exact: Rnn_add.
  - exact: (D_Triang Heps Heps' Hst Htu).
Qed.

Lemma d_U_tri {R : realType} {sig X}
    (U : axiom_scheme R sig) (s t u : term sig X) :
  @d_U R sig X U s u <= @d_U R sig X U s t + @d_U R sig X U t u.
Proof.
  set A := @d_U R sig X U s t.
  set B := @d_U R sig X U t u.
  have A0 : (0%:E <= A)%E by rewrite /A; exact: d_U_nonneg.
  have B0 : (0%:E <= B)%E by rewrite /B; exact: d_U_nonneg.
  have [Afin|Aoo] := ene_nonneg_fin_or_pinfty A0.
  - have [Bfin|Boo] := ene_nonneg_fin_or_pinfty B0.
    + apply/lee_addgt0Pr => e e0.
      have e2pos : (0 < e / 2)%R by rewrite divr_gt0// ltr0n.
      have [x HxS Hxlt] := lb_ereal_inf_adherent e2pos Afin.
      have [y HyS Hylt] := lb_ereal_inf_adherent e2pos Bfin.
      rewrite /A /d_U /extended_infimum /bound_set in HxS Hxlt.
      rewrite /B /d_U /extended_infimum /bound_set in HyS Hylt.
      case: HxS Hxlt => rx Hrx <- Hxlt.
      case: Hrx => eps [Hst Hrx].
      rewrite Hrx /nonneg_real_val in Hxlt.
      case: HyS Hylt => ry Hry <- Hylt.
      case: Hry => eps' [Htu Hry].
      rewrite Hry /nonneg_real_val in Hylt.
      apply: (le_trans (@d_U_tri_bound R sig X U s t u
        (nonneg_real_val eps) (nonneg_real_val eps')
        (svalP eps) (svalP eps') Hst Htu)).
      have Hsumlt :
        ((nonneg_real_val eps)%:E +
         (nonneg_real_val eps')%:E <
         (A + (e / 2)%:E) + (B + (e / 2)%:E))%E.
      { apply: lte_leD; last exact: ltW Hylt.
        - by [].
        - exact Hxlt. }
      apply: ltW.
      apply: (lt_le_trans Hsumlt).
      by rewrite -/A -/B adde_eps_split//.
    + have Ane : A != -oo%E by exact: ene_neq_ninfty A0.
      by rewrite Boo addey// leey.
  - have Bne : B != -oo%E by exact: ene_neq_ninfty B0.
    by rewrite Aoo addye// leey.
Qed.
