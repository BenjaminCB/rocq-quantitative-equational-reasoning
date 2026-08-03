(* ============================================================
   Quantitative equational theories as enriched Lawvere theories
   ============================================================ *)

From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Lists.List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq choice fintype.
From mathcomp Require Import order ssralg ssrnum archimedean rat reals ereal.
From mathcomp Require Import classical_sets.

From Template Require Import Metric Category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

Notation Qnn q := (0 <= q)%R.

Lemma Qnn_add : forall p q : rat, Qnn p -> Qnn q -> Qnn (p + q).
Proof. apply: addr_ge0. Qed.

Lemma Qnn_zero : Qnn (0 : rat).
Proof. apply: lexx. Qed.

Definition nnrat := {q : rat | Qnn q}.

Definition nnrat_val (eps : nnrat) : rat := sval eps.

Definition nnrat_embed (R : realType) (eps : nnrat) : R :=
  ratr (nnrat_val eps).

Lemma nnrat_embed_ge0 (R : realType) (eps : nnrat) :
  (0 <= nnrat_embed R eps)%R.
Proof.
  case: eps => eps Heps.
  by rewrite /nnrat_embed /nnrat_val /= ler0q.
Qed.

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

Record qeq (sig : signature) (X : Type) := {
  lhs : term sig X;
  rhs : term sig X;
  eps : rat;
}.

Notation "t ~[ e ] s" := {| lhs := t; rhs := s; eps := e |}
  (at level 70, no associativity).

Definition subst_qeq {sig X Y}
    (sigma : X -> term sig Y) (q : qeq sig X) : qeq sig Y :=
  {| lhs := subst_term sigma (lhs q);
     rhs := subst_term sigma (rhs q);
     eps := eps q |}.

Definition ctx sig X := seq (qeq sig X).

Definition subst_ctx {sig X Y}
    (sigma : X -> term sig Y) : ctx sig X -> ctx sig Y :=
  map (subst_qeq sigma).

Definition axiom_scheme (sig : signature) :=
  forall (X : Type), ctx sig X -> qeq sig X -> Prop.

Inductive derives {sig} (U : axiom_scheme sig)
    : forall X : Type, ctx sig X -> qeq sig X -> Prop :=
  | D_Refl : forall X Gamma t,
      @derives sig U X Gamma (t ~[0] t)
  | D_Symm : forall X Gamma t s eps,
      Qnn eps ->
      @derives sig U X Gamma (t ~[eps] s) ->
      @derives sig U X Gamma (s ~[eps] t)
  | D_Triang : forall X Gamma t s u eps eps',
      Qnn eps -> Qnn eps' ->
      @derives sig U X Gamma (t ~[eps] s) ->
      @derives sig U X Gamma (s ~[eps'] u) ->
      @derives sig U X Gamma (t ~[eps + eps'] u)
  | D_Max : forall X Gamma t s eps eps',
      Qnn eps -> (0 < eps')%R ->
      @derives sig U X Gamma (t ~[eps] s) ->
      @derives sig U X Gamma (t ~[eps + eps'] s)
  | D_Arch : forall X Gamma t s eps,
      Qnn eps ->
      (forall eps', (eps < eps')%R ->
        @derives sig U X Gamma (t ~[eps'] s)) ->
      @derives sig U X Gamma (t ~[eps] s)
  | D_NExp : forall X Gamma (f : sym sig)
                     (ts ss : 'I_(arity f) -> term sig X) eps,
      Qnn eps ->
      (forall i, @derives sig U X Gamma (ts i ~[eps] ss i)) ->
      @derives sig U X Gamma (App f ts ~[eps] App f ss)
  | D_Subst : forall X Y Gamma t s eps
                       (sigma : X -> term sig Y),
      @derives sig U X Gamma (t ~[eps] s) ->
      @derives sig U Y (subst_ctx sigma Gamma)
        (subst_term sigma t ~[eps] subst_term sigma s)
  | D_Cut : forall X Gamma Gamma' phi,
      (forall psi, List.In psi Gamma' -> @derives sig U X Gamma psi) ->
      @derives sig U X Gamma' phi ->
      @derives sig U X Gamma phi
  | D_Assumpt : forall X Gamma phi,
      List.In phi Gamma ->
      @derives sig U X Gamma phi
  | D_Axiom : forall X Gamma phi,
      U X Gamma phi -> @derives sig U X Gamma phi.

Arguments D_Refl {sig U X Gamma} t.
Arguments D_Symm {sig U X Gamma t s eps} _ _.
Arguments D_Triang {sig U X Gamma t s u eps eps'} _ _ _ _.
Arguments D_NExp {sig U X Gamma f ts ss eps} _ _.
Arguments D_Subst {sig U X Y Gamma t s eps} sigma _.
Arguments D_Axiom {sig U X Gamma phi} _.

Lemma subst_term_nexp {sig X Y} (U : axiom_scheme sig)
    (eps : rat) (sigma tau : X -> term sig Y) (t : term sig X) :
  Qnn eps ->
  (forall x, @derives sig U Y [::] (sigma x ~[eps] tau x)) ->
  @derives sig U Y [::] (subst_term sigma t ~[eps] subst_term tau t).
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

Definition d_U {R : realType} {sig X} (U : axiom_scheme sig)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nnrat_embed R) (
    fun eps => derives U [::] (s ~[nnrat_val eps] t)
  ).

Definition gamma_U {R : realType} {sig X} (U : axiom_scheme sig)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nnrat_embed R) (
    fun eps => forall Gamma, derives U Gamma (s ~[nnrat_val eps] t)
  ).

Definition delta_U {R : realType} {sig X} (U : axiom_scheme sig)
    (s t : term sig X) : \bar R :=
  extended_infimum (@nnrat_embed R) (
    fun eps => exists Gamma, derives U Gamma (s ~[nnrat_val eps] t)
  ).

Lemma delta_U_context_witness {sig X} (U : axiom_scheme sig)
    (s t : term sig X) (eps : nnrat) :
  exists Gamma, derives U Gamma (s ~[nnrat_val eps] t).
Proof.
  exists [:: s ~[nnrat_val eps] t].
  apply: D_Assumpt.
  by left.
Qed.

Proposition delta_U_zero {R : realType} {sig X}
    (U : axiom_scheme sig) (s t : term sig X) :
  @delta_U R sig X U s t = 0.
Proof.
  apply: Order.POrderTheory.le_anti.
  rewrite /delta_U /extended_infimum.
  apply/andP; split.
  - apply: ge_ereal_inf.
    exists (0%:E : \bar R); [ | apply lexx].
    exists (0 : R)%R; [ | by []].
    exists (exist _ (0 : rat) Qnn_zero).
    split.
    + apply: delta_U_context_witness.
    + rewrite /nnrat_embed /=.
      symmetry.
      apply: (ratr_nat R 0).
  - rewrite /delta_U /extended_infimum.
    have Hlb :
        (0%R <= ereal_inf
          (EFin @` bound_set (@nnrat_embed R)
            (fun eps : nnrat =>
              exists Gamma : ctx sig X,
                derives U Gamma (s ~[nnrat_val eps] t))))%E.
    { apply/ereal_infP => y Himg.
      case: Himg => r Hb <-.
      case: Hb => eps [_ Hr].
      rewrite Hr.
      apply: lee_tofin.
      exact: nnrat_embed_ge0.
    }
    exact Hlb.
Qed.

Lemma derives_empty_cut {sig X} (U : axiom_scheme sig)
    (Gamma : ctx sig X) phi :
  derives U [::] phi -> derives U Gamma phi.
Proof.
  move=> H.
  apply: (D_Cut (Gamma' := [::])).
  - move=> psi Hpsi. inversion Hpsi.
  - exact H.
Qed.

Proposition gamma_U_eq_d_U {R : realType} {sig X}
    (U : axiom_scheme sig) (s t : term sig X) :
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
    (U : axiom_scheme sig) (s : term sig X) : 
    @d_U R sig X U s s = 0.
Proof.
  apply: Order.POrderTheory.le_anti.
  apply /andP; split.
  - rewrite /d_U /extended_infimum.
    apply: ge_ereal_inf.
    exists (0%:E : \bar R); last exact: lexx.
    exists (0 : R)%R; last by [].
    exists (exist _ (0 : rat) Qnn_zero).
    split.
    + exact: D_Refl.
    + rewrite /nnrat_embed /nnrat_val /=.
      symmetry.
      exact: (ratr_nat R 0).
  - rewrite /d_U /extended_infimum.
    apply/ereal_infP => y Himg.
    case: Himg => r Hb <-.
    case: Hb => eps [_ Hr].
    rewrite Hr.
    apply: lee_tofin.
    exact: nnrat_embed_ge0.
Qed.

Lemma d_U_symm {R : realType} {sig X}
    (U : axiom_scheme sig) (s t : term sig X) :
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
    (U : axiom_scheme sig) (s t : term sig X) :
  0 <= @d_U R sig X U s t.
Proof.
  rewrite /d_U /extended_infimum.
  apply/ereal_infP => y Himg.
  case: Himg => r Hb <-.
  case: Hb => eps [_ Hr].
  rewrite Hr.
  apply: lee_tofin.
  exact: nnrat_embed_ge0.
Qed.

Lemma d_U_le_derives {R : realType} {sig X}
    (U : axiom_scheme sig) (s t : term sig X) (eps : rat) :
  Qnn eps ->
  derives U [::] (s ~[eps] t) ->
  @d_U R sig X U s t <= (ratr eps : R)%:E.
Proof.
  move=> Heps Hderive.
  rewrite /d_U /extended_infimum.
  apply: ge_ereal_inf.
  exists ((ratr eps : R)%:E : \bar R); last exact: lexx.
  exists (ratr eps : R); last by [].
  exists (exist _ eps Heps).
  split; first exact Hderive.
  rewrite /nnrat_embed /nnrat_val /=.
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
    (U : axiom_scheme sig) (s t u : term sig X) (eps eps' : rat) :
  Qnn eps ->
  Qnn eps' ->
  derives U [::] (s ~[eps] t) ->
  derives U [::] (t ~[eps'] u) ->
  @d_U R sig X U s u <= (ratr eps : R)%:E + (ratr eps' : R)%:E.
Proof.
  move=> Heps Heps' Hst Htu.
  rewrite -EFinD -rmorphD.
  apply: d_U_le_derives.
  - exact: Qnn_add.
  - exact: (D_Triang Heps Heps' Hst Htu).
Qed.

Lemma d_U_tri {R : realType} {sig X}
    (U : axiom_scheme sig) (s t u : term sig X) :
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
      rewrite Hrx /nnrat_embed /nnrat_val in Hxlt.
      case: HyS Hylt => ry Hry <- Hylt.
      case: Hry => eps' [Htu Hry].
      rewrite Hry /nnrat_embed /nnrat_val in Hylt.
      apply: (le_trans (@d_U_tri_bound R sig X U s t u
        (nnrat_val eps) (nnrat_val eps')
        (svalP eps) (svalP eps') Hst Htu)).
      have Hsumlt :
        ((ratr (nnrat_val eps) : R)%:E +
         (ratr (nnrat_val eps') : R)%:E <
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

(* ============================================================
   Ordinary Lawvere category of a signature
   ============================================================ *)

Definition lawvere_op (sig : signature) (n m : nat) : Type :=
  'I_m -> term sig 'I_n.

Definition lawvere_id (sig : signature) (n : nat) : lawvere_op sig n n :=
  fun i => Var i.

Definition lawvere_comp (sig : signature) {n m k : nat}
    (g : lawvere_op sig m k) (f : lawvere_op sig n m) :
    lawvere_op sig n k :=
  fun i => subst_term f (g i).

Definition LawvereCategory (sig : signature) : Category.
Proof.
  refine {|
    obj := nat;
    hom := lawvere_op sig;
    id := lawvere_id sig;
    comp := fun _ _ _ => @lawvere_comp sig _ _ _
  |}.
  - move=> W X Y Z h g f.
    apply functional_extensionality => i /=.
    symmetry.
    exact: subst_term_comp.
  - move=> X Y f.
    apply functional_extensionality => i /=.
    reflexivity.
  - move=> X Y f.
    apply functional_extensionality => i /=.
    exact: subst_term_var.
Defined.

(* ============================================================
    Qoutient algebra
   ============================================================ *)

Definition term_equiv {R : realType} {sig X}
    (U : axiom_scheme sig) (s t : term sig X) : Prop :=
  @d_U R sig X U s t = 0.

Lemma term_equiv_derives_pos {R : realType} {sig X}
    (U : axiom_scheme sig) (s t : term sig X) (eps : rat) :
  (0 < eps)%R ->
  @term_equiv R sig X U s t ->
  derives U [::] (s ~[eps] t).
Proof.
  move=> Heps Hst.
  rewrite /term_equiv /d_U /extended_infimum in Hst.
  have Reps_pos : (0 < (ratr eps : R))%R by rewrite ltr0q.
  have Hfin : (ereal_inf
      (EFin @` bound_set (@nnrat_embed R)
        (fun eps0 : nnrat =>
          derives U [::] (s ~[nnrat_val eps0] t))) \is a fin_num).
  { by rewrite Hst fin_numE. }
  have [x HxS Hxlt] := lb_ereal_inf_adherent Reps_pos Hfin.
  rewrite Hst add0e in Hxlt.
  rewrite /bound_set in HxS.
  case: HxS Hxlt => rx Hrx <- Hxlt.
  case: Hrx => eps0 [Hderive Hrx].
  rewrite Hrx /nnrat_embed /nnrat_val in Hxlt.
  have Hlt_rat : (nnrat_val eps0 < eps)%R.
  { move: Hxlt; by rewrite lte_fin -(@ltr_rat R). }
  have Hdelta : (0 < eps - nnrat_val eps0)%R by rewrite subr_gt0.
  have -> : eps = (nnrat_val eps0 + (eps - nnrat_val eps0))%R.
  { by rewrite addrC subrK. }
  exact: (@D_Max sig U X [::] s t (nnrat_val eps0)
    (eps - nnrat_val eps0)%R (svalP eps0) Hdelta Hderive).
Qed.

Lemma term_equiv_congruence {R : realType} {sig X}
    (U : axiom_scheme sig) (f : sym sig) 
    (xs ys : 'I_(arity f) -> term sig X):
  (forall i : 'I_(arity f), @term_equiv R sig X U (xs i) (ys i)) ->
  @term_equiv R sig X U (App f xs) (App f ys).
Proof.
  move=> H.
  rewrite /term_equiv.
  apply: Order.POrderTheory.le_anti; apply/andP; split.
  - have Hderive0 : derives U [::] (App f xs ~[0] App f ys).
    { apply: D_Arch; first exact: Qnn_zero.
      move=> eps' Heps'.
      apply: D_NExp; first exact: ltW Heps'.
      move=> i.
      exact: term_equiv_derives_pos Heps' (H i). }
    have Hle := @d_U_le_derives R sig X U
      (App f xs) (App f ys) 0 Qnn_zero Hderive0.
    rewrite (ratr_nat R 0) in Hle.
    exact Hle.
  - exact: d_U_nonneg.
Qed.

Lemma d_U_term_equiv_left {R : realType} {sig X}
    (U : axiom_scheme sig) (s s' t : term sig X) :
  @term_equiv R sig X U s s' ->
  @d_U R sig X U s t = @d_U R sig X U s' t.
Proof.
  move=> Hss'.
  apply: Order.POrderTheory.le_anti; apply/andP; split.
  - have Htri := @d_U_tri R sig X U s s' t.
    by rewrite Hss' add0e in Htri.
  - have Htri := @d_U_tri R sig X U s' s t.
    rewrite (@d_U_symm R sig X U s' s) Hss' add0e in Htri.
    exact Htri.
Qed.

Lemma d_U_term_equiv_right {R : realType} {sig X}
    (U : axiom_scheme sig) (s t t' : term sig X) :
  @term_equiv R sig X U t t' ->
  @d_U R sig X U s t = @d_U R sig X U s t'.
Proof.
  move=> Htt'.
  rewrite (@d_U_symm R sig X U s t).
  rewrite (@d_U_term_equiv_left R sig X U t t' s Htt').
  exact: (@d_U_symm R sig X U t' s).
Qed.

(* ============================================================
    Symbol lifting to the quotient term algebra
   ============================================================ *)

Record TermQuotient (R : realType) (sig : signature) (X : Type)
    (U : axiom_scheme sig) := {
  tq_carrier : Type;
  tq_class : term sig X -> tq_carrier;
  tq_repr : tq_carrier -> term sig X;
  tq_reprK : forall x : tq_carrier, tq_class (tq_repr x) = x;
  tq_zero_exact :
    forall s t : term sig X,
      @term_equiv R sig X U s t <-> tq_class s = tq_class t;
}.

Definition symbol_lifting {R : realType} {sig X}
    {U : axiom_scheme sig} (Q : @TermQuotient R sig X U)
    (f : sym sig) (xs : 'I_(arity f) -> tq_carrier Q) :
    tq_carrier Q :=
  @tq_class R sig X U Q
    (App f (fun i => @tq_repr R sig X U Q (xs i))).

Lemma symbol_lifting_class {R : realType} {sig X}
    {U : axiom_scheme sig} (Q : @TermQuotient R sig X U)
    (f : sym sig) (xs : 'I_(arity f) -> term sig X) :
  @symbol_lifting R sig X U Q f
    (fun i => @tq_class R sig X U Q (xs i)) =
  @tq_class R sig X U Q (App f xs).
Proof.
  apply/(proj1 (@tq_zero_exact R sig X U Q _ _)).
  apply: term_equiv_congruence => i.
  apply/(proj2 (@tq_zero_exact R sig X U Q _ _)).
  exact: (@tq_reprK R sig X U Q (@tq_class R sig X U Q (xs i))).
Qed.

Lemma derives_zero_term_equiv {R : realType} {sig X}
    (U : axiom_scheme sig) (s t : term sig X) :
  derives U [::] (s ~[0] t) -> @term_equiv R sig X U s t.
Proof.
  move=> Hderive.
  rewrite /term_equiv.
  apply: Order.POrderTheory.le_anti; apply/andP; split.
  - have Hle := @d_U_le_derives R sig X U s t 0 Qnn_zero Hderive.
    rewrite (ratr_nat R 0) in Hle.
    exact Hle.
  - exact: d_U_nonneg.
Qed.

Lemma term_quotient_sound_zero_derives {R : realType} {sig X}
    {U : axiom_scheme sig} (Q : @TermQuotient R sig X U)
    (s t : term sig X) :
  derives U [::] (s ~[0] t) ->
  @tq_class R sig X U Q s = @tq_class R sig X U Q t.
Proof.
  move=> Hderive.
  apply/(proj1 (@tq_zero_exact R sig X U Q s t)).
  exact: (@derives_zero_term_equiv R sig X U s t Hderive).
Qed.

Definition term_d_tilde {R : realType} {sig X}
    {U : axiom_scheme sig} (Q : @TermQuotient R sig X U)
    (x y : tq_carrier Q) : \bar R :=
  @d_U R sig X U
    (@tq_repr R sig X U Q x) (@tq_repr R sig X U Q y).

Lemma term_d_tilde_class {R : realType} {sig X}
    {U : axiom_scheme sig} (Q : @TermQuotient R sig X U)
    (s t : term sig X) :
  @term_d_tilde R sig X U Q
    (@tq_class R sig X U Q s) (@tq_class R sig X U Q t) =
  @d_U R sig X U s t.
Proof.
  rewrite /term_d_tilde.
  have Hs : @term_equiv R sig X U
      (@tq_repr R sig X U Q (@tq_class R sig X U Q s)) s.
  { apply/(proj2 (@tq_zero_exact R sig X U Q _ _)).
    exact: (@tq_reprK R sig X U Q (@tq_class R sig X U Q s)). }
  have Ht : @term_equiv R sig X U
      (@tq_repr R sig X U Q (@tq_class R sig X U Q t)) t.
  { apply/(proj2 (@tq_zero_exact R sig X U Q _ _)).
    exact: (@tq_reprK R sig X U Q (@tq_class R sig X U Q t)). }
  rewrite (@d_U_term_equiv_left R sig X U _ _ _ Hs).
  exact: (@d_U_term_equiv_right R sig X U _ _ _ Ht).
Qed.

(* ============================================================
   Metric quotient of the Lawvere theory

   The hom distance is the supremum of the component term
   distances.  The optional index contributes zero when the
   codomain arity is empty.
   ============================================================ *)

Definition lawvere_hom_d {R : realType} {sig}
    {n m : nat} (U : axiom_scheme sig)
    (f g : lawvere_op sig n m) : \bar R :=
  ereal_sup (range (fun oi : option 'I_m =>
    match oi with
    | Some i => @d_U R sig 'I_n U (f i) (g i)
    | None => 0
    end)).

Lemma lawvere_hom_d_ubound {R : realType} {sig}
    {n m : nat} (U : axiom_scheme sig)
    (f g : lawvere_op sig n m) (oi : option 'I_m) :
  (match oi with
   | Some i => @d_U R sig 'I_n U (f i) (g i)
   | None => 0
   end) <= @lawvere_hom_d R sig n m U f g.
Proof.
  apply: ereal_sup_ubound.
  by exists oi.
Qed.

Lemma lawvere_hom_d_nonneg {R : realType} {sig}
    {n m : nat} (U : axiom_scheme sig)
    (f g : lawvere_op sig n m) :
  0 <= @lawvere_hom_d R sig n m U f g.
Proof.
  exact: (@lawvere_hom_d_ubound R sig n m U f g None).
Qed.

(* The zero-distance relation whose quotient is used in Section 6 of the
   paper.  Here it is applied hom-wise to tuples of terms. *)
Definition lawvere_hom_zero_equiv {R : realType} {sig}
    {n m : nat} (U : axiom_scheme sig)
    (f g : lawvere_op sig n m) : Prop :=
  @lawvere_hom_d R sig n m U f g = 0.

(* A single hom-object quotient.  Keeping this separate from
   [LawvereMetricQuotient] makes the construction modular: first construct
   the metric quotient for every pair [n, m], then prove the one composition
   estimate needed to assemble the enriched Lawvere theory. *)
Record LawvereHomMetricQuotient (R : realType)
    (sig : signature) (U : axiom_scheme sig) (n m : nat) := {
  lhmq_hom : ext_metric_space R;
  lhmq_class :
    lawvere_op sig n m -> carrier lhmq_hom;
  lhmq_repr :
    carrier lhmq_hom -> lawvere_op sig n m;
  lhmq_reprK : forall x : carrier lhmq_hom,
    lhmq_class (lhmq_repr x) = x;
  lhmq_qdist : forall f g : lawvere_op sig n m,
    dist (lhmq_class f) (lhmq_class g) =
    @lawvere_hom_d R sig n m U f g
}.

Record LawvereMetricQuotient (R : realType)
    (sig : signature) (U : axiom_scheme sig) := {
  lmq_hom : forall n m : nat, ext_metric_space R;
  lmq_class : forall n m,
    lawvere_op sig n m -> carrier (lmq_hom n m);
  lmq_repr : forall n m,
    carrier (lmq_hom n m) -> lawvere_op sig n m;
  lmq_reprK : forall n m (x : carrier (lmq_hom n m)),
    @lmq_class n m (@lmq_repr n m x) = x;
  lmq_qdist : forall n m (f g : lawvere_op sig n m),
    dist (@lmq_class n m f) (@lmq_class n m g) =
    @lawvere_hom_d R sig n m U f g;
  lmq_comp_nexp : forall n m k
      (g g' : lawvere_op sig m k)
      (f f' : lawvere_op sig n m),
    (@lawvere_hom_d R sig n k U
        (lawvere_comp g f) (lawvere_comp g' f') <=
      @lawvere_hom_d R sig m k U g g' +
      @lawvere_hom_d R sig n m U f f')%E
}.

Definition assemble_lawvere_metric_quotient
    {R : realType} {sig : signature} {U : axiom_scheme sig}
    (Qhom : forall n m, @LawvereHomMetricQuotient R sig U n m)
    (Hcomp : forall n m k
      (g g' : lawvere_op sig m k)
      (f f' : lawvere_op sig n m),
      (@lawvere_hom_d R sig n k U
          (lawvere_comp g f) (lawvere_comp g' f') <=
        @lawvere_hom_d R sig m k U g g' +
        @lawvere_hom_d R sig n m U f f')%E) :
    @LawvereMetricQuotient R sig U.
Proof.
  refine {|
    lmq_hom := fun n m =>
      @lhmq_hom R sig U n m (Qhom n m);
    lmq_class := fun n m =>
      @lhmq_class R sig U n m (Qhom n m);
    lmq_repr := fun n m =>
      @lhmq_repr R sig U n m (Qhom n m);
    lmq_reprK := fun n m =>
      @lhmq_reprK R sig U n m (Qhom n m);
    lmq_qdist := fun n m =>
      @lhmq_qdist R sig U n m (Qhom n m);
    lmq_comp_nexp := Hcomp
  |}.
Defined.

Lemma lawvere_hom_d_refl {R : realType} {sig}
    {n m : nat} (U : axiom_scheme sig)
    (f : lawvere_op sig n m) :
  @lawvere_hom_d R sig n m U f f = 0.
Proof.
  rewrite /lawvere_hom_d.
  apply: Order.POrderTheory.le_anti; apply /andP; split.
  - apply ge_ereal_sup.
    move => x [i _ <-].
    case: i => [ i | ]; [ by rewrite d_U_refl | by [] ].
  - apply: ereal_sup_ubound.
    by exists None.
Qed.

Lemma lawvere_hom_d_ge0 {R : realType} {sig}
    {n m : nat} (U : axiom_scheme sig)
    (f g : lawvere_op sig n m) :
  0 <= @lawvere_hom_d R sig n m U f g.
Proof.
  apply: ereal_sup_ubound.
  by exists None.
Qed.

Lemma lawvere_hom_d_symm {R : realType} {sig}
    {n m : nat} (U : axiom_scheme sig)
    (f g : lawvere_op sig n m) :
  @lawvere_hom_d R sig n m U f g = 
  @lawvere_hom_d R sig n m U g f.
Proof.
  apply: Order.POrderTheory.le_anti; apply /andP; split.
  - apply ge_ereal_sup.
    move => x [i _ <-].
    case: i => [ i | ]; last by apply lawvere_hom_d_ge0.
    rewrite /lawvere_hom_d; apply ereal_sup_ubound.
    by exists (Some i) => //=; rewrite d_U_symm.
  - apply ge_ereal_sup.
    move => x [i _ <-].
    case: i => [ i | ]; last by apply lawvere_hom_d_ge0.
    rewrite /lawvere_hom_d; apply ereal_sup_ubound.
    by exists (Some i) => //=; rewrite d_U_symm.
Qed.

Lemma lawvere_hom_d_tri {R : realType} {sig}
    {n m : nat} (U : axiom_scheme sig)
    (f g h : lawvere_op sig n m) :
  @lawvere_hom_d R sig n m U f h <=
  @lawvere_hom_d R sig n m U f g +
  @lawvere_hom_d R sig n m U g h.
Proof.
  rewrite {1}/lawvere_hom_d.
  apply ge_ereal_sup => x [i _ <-].
  case: i => [ i | ].
  - apply: (le_trans (d_U_tri U (f i) (g i) (h i))).
    exact: leeD
      (lawvere_hom_d_ubound U f g (Some i))
      (lawvere_hom_d_ubound U g h (Some i)).
  - apply: adde_ge0; exact: lawvere_hom_d_ge0.
Qed. 

(* ============================================================
   Zero-distance equivalence and the hom-wise metric quotient
   ============================================================ *)

Lemma lawvere_hom_zero_equiv_refl {R : realType} {sig}
    {n m : nat} (U : axiom_scheme sig)
    (f : lawvere_op sig n m) :
  @lawvere_hom_zero_equiv R sig n m U f f.
Proof.
  exact: lawvere_hom_d_refl.
Qed.

Lemma lawvere_hom_zero_equiv_symm {R : realType} {sig}
    {n m : nat} (U : axiom_scheme sig)
    (f g : lawvere_op sig n m) :
  @lawvere_hom_zero_equiv R sig n m U f g ->
  @lawvere_hom_zero_equiv R sig n m U g f.
Proof.
  rewrite /lawvere_hom_zero_equiv.
  move=> Hfg.
  by rewrite lawvere_hom_d_symm.
Qed.

Lemma lawvere_hom_zero_equiv_trans {R : realType} {sig}
    {n m : nat} (U : axiom_scheme sig)
    (f g h : lawvere_op sig n m) :
  @lawvere_hom_zero_equiv R sig n m U f g ->
  @lawvere_hom_zero_equiv R sig n m U g h ->
  @lawvere_hom_zero_equiv R sig n m U f h.
Proof.
  rewrite /lawvere_hom_zero_equiv.
  move=> Hfg Hgh.
  apply: Order.POrderTheory.le_anti; apply/andP; split.
  - apply: (le_trans (lawvere_hom_d_tri U f g h)).
    by rewrite Hfg Hgh add0e.
  - exact: lawvere_hom_d_ge0.
Qed.

Lemma lawvere_hom_d_zero_left {R : realType} {sig}
    {n m : nat} (U : axiom_scheme sig)
    (f f' g : lawvere_op sig n m) :
  @lawvere_hom_zero_equiv R sig n m U f f' ->
  @lawvere_hom_d R sig n m U f g =
  @lawvere_hom_d R sig n m U f' g.
Proof.
  rewrite /lawvere_hom_zero_equiv.
  move=> Hff'.
  apply: Order.POrderTheory.le_anti; apply/andP; split.
  - have Htri := @lawvere_hom_d_tri R sig n m U f f' g.
    by rewrite Hff' add0e in Htri.
  - have Htri := @lawvere_hom_d_tri R sig n m U f' f g.
    rewrite (@lawvere_hom_d_symm R sig n m U f' f)
      Hff' add0e in Htri.
    exact Htri.
Qed.

Lemma lawvere_hom_d_zero_right {R : realType} {sig}
    {n m : nat} (U : axiom_scheme sig)
    (f g g' : lawvere_op sig n m) :
  @lawvere_hom_zero_equiv R sig n m U g g' ->
  @lawvere_hom_d R sig n m U f g =
  @lawvere_hom_d R sig n m U f g'.
Proof.
  move=> Hgg'.
  rewrite (@lawvere_hom_d_symm R sig n m U f g).
  rewrite (@lawvere_hom_d_zero_left R sig n m U g g' f Hgg').
  exact: (@lawvere_hom_d_symm R sig n m U g' f).
Qed.

(* TODO: construct the quotient of [lawvere_op sig n m] by
   [lawvere_hom_zero_equiv U], choose representatives, and equip it with
   the metric induced by [lawvere_hom_d U]. *)
Definition lawvere_hom_metric_quotient {R : realType} {sig}
    (U : axiom_scheme sig) (n m : nat) :
    @LawvereHomMetricQuotient R sig U n m.
Proof.
Admitted.

(* TODO: this is the remaining compatibility estimate needed to descend
   Lawvere composition to the metric quotients. *)
Lemma lawvere_hom_d_comp_nexp {R : realType} {sig}
    (U : axiom_scheme sig) (n m k : nat)
    (g g' : lawvere_op sig m k)
    (f f' : lawvere_op sig n m) :
  (@lawvere_hom_d R sig n k U
      (lawvere_comp g f) (lawvere_comp g' f') <=
    @lawvere_hom_d R sig m k U g g' +
    @lawvere_hom_d R sig n m U f f')%E.
Proof.
Admitted.

Definition canonical_lawvere_metric_quotient {R : realType} {sig}
    (U : axiom_scheme sig) : @LawvereMetricQuotient R sig U.
Proof.
  apply: assemble_lawvere_metric_quotient.
  - exact: (fun n m => lawvere_hom_metric_quotient U n m).
  - exact: lawvere_hom_d_comp_nexp.
Defined.

Lemma lmq_class_eq_iff_zero {R : realType} {sig}
    {U : axiom_scheme sig} (Q : @LawvereMetricQuotient R sig U)
    {n m : nat} (f g : lawvere_op sig n m) :
  @lmq_class R sig U Q n m f = @lmq_class R sig U Q n m g <->
  @lawvere_hom_d R sig n m U f g = 0.
Proof.
  split.
  - move=> H.
    rewrite -(@lmq_qdist R sig U Q n m f g) H.
    exact: dist_refl.
  - move=> H.
    apply: (@dist_eq0 R (@lmq_hom R sig U Q n m)).
    by rewrite (@lmq_qdist R sig U Q n m f g).
Qed.

Definition quotient_lawvere_comp {R : realType} {sig}
    {U : axiom_scheme sig} (Q : @LawvereMetricQuotient R sig U)
    {n m k : nat}
    (g : carrier (lmq_hom Q m k))
    (f : carrier (lmq_hom Q n m)) :
    carrier (lmq_hom Q n k) :=
  @lmq_class R sig U Q n k
    (lawvere_comp
      (@lmq_repr R sig U Q m k g)
      (@lmq_repr R sig U Q n m f)).

Lemma quotient_lawvere_comp_class {R : realType} {sig}
    {U : axiom_scheme sig} (Q : @LawvereMetricQuotient R sig U)
    {n m k : nat}
    (g : lawvere_op sig m k) (f : lawvere_op sig n m) :
  @quotient_lawvere_comp R sig U Q n m k
      (@lmq_class R sig U Q m k g)
      (@lmq_class R sig U Q n m f) =
    @lmq_class R sig U Q n k (lawvere_comp g f).
Proof.
  apply/(proj2 (@lmq_class_eq_iff_zero R sig U Q n k _ _)).
  apply: Order.POrderTheory.le_anti.
  apply/andP; split.
  - apply: (le_trans (@lmq_comp_nexp R sig U Q n m k
      (@lmq_repr R sig U Q m k (@lmq_class R sig U Q m k g)) g
      (@lmq_repr R sig U Q n m (@lmq_class R sig U Q n m f)) f)).
    have Hg :
        @lawvere_hom_d R sig m k U
          (@lmq_repr R sig U Q m k (@lmq_class R sig U Q m k g))
          g = 0.
    { apply/(proj1 (@lmq_class_eq_iff_zero R sig U Q m k _ _)).
      exact: (@lmq_reprK R sig U Q m k
        (@lmq_class R sig U Q m k g)). }
    have Hf :
        @lawvere_hom_d R sig n m U
          (@lmq_repr R sig U Q n m (@lmq_class R sig U Q n m f))
          f = 0.
    { apply/(proj1 (@lmq_class_eq_iff_zero R sig U Q n m _ _)).
      exact: (@lmq_reprK R sig U Q n m
        (@lmq_class R sig U Q n m f)). }
    by rewrite Hg Hf add0e.
  - exact: lawvere_hom_d_nonneg.
Qed.

Definition quotient_lawvere_eid {R : realType} {sig}
    {U : axiom_scheme sig} (Q : @LawvereMetricQuotient R sig U)
    (n : nat) :
    Metric_hom met_t_unit (lmq_hom Q n n).
Proof.
  refine (@Build_Metric_hom R met_t_unit (lmq_hom Q n n)
    (fun _ : carrier met_t_unit =>
      @lmq_class R sig U Q n n (@lawvere_id sig n)) _).
  by move=> u v; rewrite !dist_refl.
Defined.

Definition quotient_lawvere_ecomp {R : realType} {sig}
    {U : axiom_scheme sig} (Q : @LawvereMetricQuotient R sig U)
    (n m k : nat) :
    Metric_hom
      (met_add_t_obj (lmq_hom Q m k) (lmq_hom Q n m))
      (lmq_hom Q n k).
Proof.
  refine (@Build_Metric_hom R
    (met_add_t_obj (lmq_hom Q m k) (lmq_hom Q n m))
    (lmq_hom Q n k)
    (fun gf : carrier
        (met_add_t_obj (lmq_hom Q m k) (lmq_hom Q n m)) =>
      @quotient_lawvere_comp R sig U Q n m k gf.1 gf.2) _).
  move=> [g f] [g' f'].
  change
    (dist
      (@lmq_class R sig U Q n k
        (lawvere_comp
          (@lmq_repr R sig U Q m k g)
          (@lmq_repr R sig U Q n m f)))
      (@lmq_class R sig U Q n k
        (lawvere_comp
          (@lmq_repr R sig U Q m k g')
          (@lmq_repr R sig U Q n m f'))) <=
     dist g g' + dist f f')%E.
  rewrite (@lmq_qdist R sig U Q n k).
  have Hg := @lmq_qdist R sig U Q m k
    (@lmq_repr R sig U Q m k g)
    (@lmq_repr R sig U Q m k g').
  rewrite !(@lmq_reprK R sig U Q m k) in Hg.
  have Hf := @lmq_qdist R sig U Q n m
    (@lmq_repr R sig U Q n m f)
    (@lmq_repr R sig U Q n m f').
  rewrite !(@lmq_reprK R sig U Q n m) in Hf.
  rewrite Hg Hf.
  exact: (@lmq_comp_nexp R sig U Q n m k).
Defined.

Definition QuotientEnrichedLawvereTheory {R : realType} {sig}
    {U : axiom_scheme sig} (Q : @LawvereMetricQuotient R sig U) :
    EnrichedCategory (@MetAddMonoidal R).
Proof.
  refine (@Build_EnrichedCategory (@MetAddMonoidal R)
    nat (lmq_hom Q)
    (quotient_lawvere_eid Q)
    (quotient_lawvere_ecomp Q) _ _ _).
  - move=> l n m k.
    apply Metric_hom_ext => hgf.
    case: hgf => hg f.
    case: hg => h g.
    cbn.
    rewrite -[h](@lmq_reprK R sig U Q k l h).
    rewrite -[g](@lmq_reprK R sig U Q m k g).
    rewrite -[f](@lmq_reprK R sig U Q n m f).
    rewrite !quotient_lawvere_comp_class.
    apply f_equal.
    symmetry.
    exact: (@comp_assoc (LawvereCategory sig) n m k l
      (@lmq_repr R sig U Q k l h)
      (@lmq_repr R sig U Q m k g)
      (@lmq_repr R sig U Q n m f)).
  - move=> n m.
    apply Metric_hom_ext => uf.
    case: uf => u f.
    case: u.
    cbn.
    rewrite -[f](@lmq_reprK R sig U Q n m f).
    rewrite quotient_lawvere_comp_class.
    apply f_equal.
    exact: (@comp_id_l (LawvereCategory sig) n m
      (@lmq_repr R sig U Q n m f)).
  - move=> n m.
    apply Metric_hom_ext => fu.
    case: fu => f u.
    case: u.
    cbn.
    rewrite -[f](@lmq_reprK R sig U Q n m f).
    rewrite quotient_lawvere_comp_class.
    apply f_equal.
    exact: (@comp_id_r (LawvereCategory sig) n m
      (@lmq_repr R sig U Q n m f)).
Defined.

(* The quotient algebra on [n] generators is the hom-object [L(n, 1)].
   Its model is the enriched representable functor [L(n, -)]. *)

Definition QuotientTermAlgebra {R : realType} {sig}
    {U : axiom_scheme sig} (Q : @LawvereMetricQuotient R sig U)
    (n : nat) : ext_metric_space R :=
  lmq_hom Q n 1.

Definition quotient_term_model {R : realType} {sig}
    {U : axiom_scheme sig} (Q : @LawvereMetricQuotient R sig U)
    (n : nat) :
    EnrichedFunctor
      (QuotientEnrichedLawvereTheory Q)
      (MetSelfEnriched R) :=
  @enriched_representable R
    (@QuotientEnrichedLawvereTheory R sig U Q) n.

Lemma quotient_term_model_at_one {R : realType} {sig}
    {U : axiom_scheme sig} (Q : @LawvereMetricQuotient R sig U)
    (n : nat) :
  @e_f_obj (@MetAddMonoidal R)
    (@QuotientEnrichedLawvereTheory R sig U Q)
    (MetSelfEnriched R)
    (@quotient_term_model R sig U Q n) (1 : nat) =
  @QuotientTermAlgebra R sig U Q n.
Proof. reflexivity. Qed.

Theorem quotient_algebra_is_enriched_model {R : realType} {sig}
    {U : axiom_scheme sig} (Q : @LawvereMetricQuotient R sig U)
    (n : nat) :
  exists M : EnrichedFunctor
      (QuotientEnrichedLawvereTheory Q)
      (MetSelfEnriched R),
    @e_f_obj (@MetAddMonoidal R)
      (@QuotientEnrichedLawvereTheory R sig U Q)
      (MetSelfEnriched R) M (1 : nat) =
    @QuotientTermAlgebra R sig U Q n.
Proof.
  exists (@quotient_term_model R sig U Q n).
  exact: quotient_term_model_at_one.
Qed.
