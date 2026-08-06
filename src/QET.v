(* ============================================================
   Quantitative equational theories as enriched Lawvere theories
   ============================================================ *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Lists.List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq choice fintype.
From mathcomp Require Import order ssralg ssrnum archimedean reals ereal.
From mathcomp Require Import classical_sets.

From Template Require Import Metric Category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

Notation Enn e := (0 <= e)%E.

Lemma Enn_add {R : realType} : forall p q : \bar R,
  Enn p -> Enn q -> Enn (p + q).
Proof. exact: adde_ge0. Qed.

Lemma Enn_zero {R : realType} : Enn (0 : \bar R).
Proof. apply: lexx. Qed.

Definition nonneg_ereal (R : realType) := {e : \bar R | Enn e}.

Definition nonneg_ereal_val {R : realType} (eps : nonneg_ereal R) : \bar R :=
  sval eps.

Lemma nonneg_ereal_val_ge0 {R : realType} (eps : nonneg_ereal R) :
  (0 <= nonneg_ereal_val eps)%E.
Proof. exact: (svalP eps). Qed.

(* ============================================================
   Signatures, terms, and substitution
   ============================================================ *)

Record signature := {
  sym : Type;
  arity : sym -> nat;
}.

Inductive term (sig : signature) (X : Type) : Type :=
  | Var : X -> term sig X
  | App : forall f : sym sig, ('I_(arity f) -> term sig X) -> term sig X.

Arguments Var {sig X} _.
Arguments App {sig X} _ _.

Fixpoint subst_term {sig X Y} (sigma : X -> term sig Y)
    (t : term sig X) : term sig Y :=
  match t with
  | Var x => sigma x
  | App f args => App f (subst_term sigma \o args)
  end.

Definition subst_comp {sig X Y Z}
    (sigma : Y -> term sig Z) (tau : X -> term sig Y) :
    X -> term sig Z :=
  subst_term sigma \o tau.

Lemma subst_term_comp {sig X Y Z}
    (sigma : Y -> term sig Z) (tau : X -> term sig Y)
    (t : term sig X) :
  subst_term sigma (subst_term tau t) = subst_term (subst_comp sigma tau) t.
Proof.
  elim: t => [x | f args IH] //=.
  congr App.
  apply functional_extensionality => i.
  apply: IH.
Qed.

Lemma subst_term_var {sig X} (t : term sig X) :
  subst_term Var t = t.
Proof.
  elim: t => [x | f args IH] //=.
  congr App.
  apply functional_extensionality => i.
  exact: IH.
Qed.

(* ============================================================
   Quantitative equations and axiom schemes
   ============================================================ *)

Record qeq (R : realType) (sig : signature) (X : Type) := {
  lhs : term sig X;
  rhs : term sig X;
  eps : \bar R;
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
      Enn eps ->
      @derives R sig U X Gamma (t ~[eps] s) ->
      @derives R sig U X Gamma (s ~[eps] t)
  | D_Triang : forall X Gamma t s u eps eps',
      Enn eps -> Enn eps' ->
      @derives R sig U X Gamma (t ~[eps] s) ->
      @derives R sig U X Gamma (s ~[eps'] u) ->
      @derives R sig U X Gamma (t ~[eps + eps'] u)
  | D_Max : forall X Gamma t s eps eps',
      Enn eps -> (0 < eps')%E ->
      @derives R sig U X Gamma (t ~[eps] s) ->
      @derives R sig U X Gamma (t ~[eps + eps'] s)
  | D_Arch : forall X Gamma t s eps,
      Enn eps ->
      (forall eps', (eps < eps')%E ->
        @derives R sig U X Gamma (t ~[eps'] s)) ->
      @derives R sig U X Gamma (t ~[eps] s)
  | D_NExp : forall X Gamma (f : sym sig)
                     (ts ss : 'I_(arity f) -> term sig X) eps,
      Enn eps ->
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
    (eps : \bar R) (sigma tau : X -> term sig Y) (t : term sig X) :
  Enn eps ->
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
   The Induced Pseudometric
   ============================================================ *)

Definition d_U {R : realType} {sig X} (U : axiom_scheme R sig)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nonneg_ereal_val R) (
    fun eps => derives U [::] (s ~[nonneg_ereal_val eps] t)
  ).

Definition gamma_U {R : realType} {sig X} (U : axiom_scheme R sig)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nonneg_ereal_val R) (
    fun eps => forall Gamma, derives U Gamma (s ~[nonneg_ereal_val eps] t)
  ).

Definition delta_U {R : realType} {sig X} (U : axiom_scheme R sig)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nonneg_ereal_val R) (
    fun eps => exists Gamma, derives U Gamma (s ~[nonneg_ereal_val eps] t)
  ).

Lemma delta_U_context_witness {R : realType} {sig X}
    (U : axiom_scheme R sig) (s t : term sig X) (eps : nonneg_ereal R) :
  exists Gamma, derives U Gamma (s ~[nonneg_ereal_val eps] t).
Proof.
  exists [:: s ~[nonneg_ereal_val eps] t].
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
    exists (exist _ (0%:E : \bar R) Enn_zero).
    split.
    + apply: delta_U_context_witness.
    + reflexivity.
  - rewrite /delta_U /extended_infimum.
    have Hlb :
        (0%R <= ereal_inf
          (bound_set (@nonneg_ereal_val R)
            (fun eps : nonneg_ereal R =>
              exists Gamma : ctx R sig X,
                derives U Gamma (s ~[nonneg_ereal_val eps] t))))%E.
    { apply/ereal_infP => y Hy.
      case: Hy => eps [_ Hr].
      rewrite Hr.
      exact: nonneg_ereal_val_ge0.
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
  - move=> [eps [Hderive Hr]].
    exists eps; split; last exact Hr.
    exact: (Hderive [::]).
  - move=> [eps [Hderive Hr]].
    exists eps; split; last exact Hr.
    move=> Gamma.
    exact: derives_empty_cut Hderive.
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
    exists (exist _ (0%:E : \bar R) Enn_zero).
    split.
    + exact: D_Refl.
    + reflexivity.
  - rewrite /d_U /extended_infimum.
    apply/ereal_infP => y Hy.
    case: Hy => eps [_ Hr].
    rewrite Hr.
    exact: nonneg_ereal_val_ge0.
Qed.

Lemma d_U_symm {R : realType} {sig X}
    (U : axiom_scheme R sig) (s t : term sig X) :
    @d_U R sig X U s t = @d_U R sig X U t s.
Proof.
  rewrite /d_U /extended_infimum /bound_set.
  congr ereal_inf.
  apply/seteqP; split=> r.
  - move=> [eps [Hderive Hr]].
    exists eps; split; last exact Hr.
    apply: D_Symm; first exact: (svalP eps).
    exact Hderive.
  - move=> [eps [Hderive Hr]].
    exists eps; split; last exact Hr.
    apply: D_Symm; first exact: (svalP eps).
    exact Hderive.
Qed.

Lemma d_U_nonneg {R : realType} {sig X}
    (U : axiom_scheme R sig) (s t : term sig X) :
  0 <= @d_U R sig X U s t.
Proof.
  rewrite /d_U /extended_infimum.
  apply/ereal_infP => y Hy.
  case: Hy => eps [_ Hr].
  rewrite Hr.
  exact: nonneg_ereal_val_ge0.
Qed.

Lemma d_U_le_derives {R : realType} {sig X}
    (U : axiom_scheme R sig) (s t : term sig X) (eps : \bar R) :
  Enn eps ->
  derives U [::] (s ~[eps] t) ->
  @d_U R sig X U s t <= eps.
Proof.
  move=> Heps Hderive.
  rewrite /d_U /extended_infimum.
  apply: ge_ereal_inf.
  exists eps; last exact: lexx.
  exists (exist _ eps Heps).
  split; first exact Hderive.
  reflexivity.
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
    (U : axiom_scheme R sig) (s t u : term sig X) (eps eps' : \bar R) :
  Enn eps ->
  Enn eps' ->
  derives U [::] (s ~[eps] t) ->
  derives U [::] (t ~[eps'] u) ->
  @d_U R sig X U s u <= eps + eps'.
Proof.
  move=> Heps Heps' Hst Htu.
  apply: d_U_le_derives.
  - exact: Enn_add.
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
      case: HxS Hxlt => eps [Hst Hrx] Hxlt.
      rewrite Hrx /nonneg_ereal_val in Hxlt.
      case: HyS Hylt => eps' [Htu Hry] Hylt.
      rewrite Hry /nonneg_ereal_val in Hylt.
      apply: (le_trans (@d_U_tri_bound R sig X U s t u
        (nonneg_ereal_val eps) (nonneg_ereal_val eps')
        (svalP eps) (svalP eps') Hst Htu)).
      have Hsumlt :
        (nonneg_ereal_val eps +
         nonneg_ereal_val eps' <
         (A + (e / 2)%:E) + (B + (e / 2)%:E))%E.
      { apply: lte_leD; last exact: ltW Hylt.
        - rewrite (ge0_fin_numE (svalP eps')).
          apply: (lt_trans Hylt).
          rewrite ltey.
          have Hfin : B + (e / 2)%:E \is a fin_num by
            rewrite fin_numD Bfin.
          by move/fin_numP: Hfin => [_ Hnotpinfty].
        - exact Hxlt. }
      apply: ltW.
      apply: (lt_le_trans Hsumlt).
      by rewrite -/A -/B adde_eps_split//.
    + have Ane : A != -oo%E by exact: ene_neq_ninfty A0.
      by rewrite Boo addey// leey.
  - have Bne : B != -oo%E by exact: ene_neq_ninfty B0.
    by rewrite Aoo addye// leey.
Qed.
