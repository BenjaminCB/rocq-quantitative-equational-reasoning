(** * Completeness of the quantitative rules

    Theorem 5 of the notes: if [T(⟦s⟧, ⟦t⟧) <= ε] for state terms [s] and
    [t] then [s =_ε t] is derivable. An optimal coupling is a layered
    graph, and the derivation is read off the graph: every layer is
    written in the bases in which it is a matching (its Schmidt
    decomposition), COH derives the layer from its edges, MIX puts the
    layers side by side, and LA identifies the two sides with [s] and
    [t]. *)

From QOT Require Import Prelude Tensor QuantumStates PSD SymAsym Cost.
From QOT Require Import QuantumOptimalTransport LayeredGraphs GraphOperations.
From QOT Require Import GraphCost GraphOptimality.
From mathcomp.algebra_tactics Require Import ring lra.
From Template Require Import DensityTerms DensityEquality DensityDeduction.
From Template Require Import DensitySoundness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section Completeness.

Variable d : nat.

Implicit Types (L : 'M[C]_d) (G : lgraph d) (s t : term d).

(** ** Step 1: the bases of a layer

    The Schmidt decomposition of the vector of a layer, as a singular
    value decomposition of its amplitude matrix:
    [Λ = Σ_k √σ_k |f_k> <g_k|^T] with [(f_k)] and [(g_k)] orthonormal and
    [σ_k > 0]. The [f_k] are the eigenvectors of [Λ Λ^t*] with a nonzero
    eigenvalue [σ_k], and [g_k] is the row of [Λ] along [f_k],
    normalised. *)
Lemma schmidt_decomp L :
  exists (n : nat) (F G : 'I_n -> 'cV[C]_d) (sv : 'I_n -> R),
    [/\ forall k l, cdot (F k) (F l) = (k == l)%:R,
        forall k l, cdot (G k) (G l) = (k == l)%:R,
        forall k, 0 < sv k
      & L = \sum_k (Num.sqrt (sv k))%:C *: edge (F k) (G k)].
Proof.
pose H := L *m L^t*.
have H_herm : H \is hermsymmx by rewrite herm_eq /H trmxC_mul trmxCK.
pose P := spectralmx H; pose sp := spectral_diag H.
have PPt : P *m P^t* = 1%:M by apply/unitarymxP; exact: spectral_unitarymx.
have PtP : P^t* *m P = 1%:M.
  by apply: unitary_trmxCV; exact: spectral_unitarymx.
have HH : H = P^t* *m diag_mx sp *m P by exact: spectral_decomp.
pose M := P *m L.
have MMt : M *m M^t* = diag_mx sp.
  rewrite /M trmxC_mul mulmxA -[P *m L *m _]mulmxA -/H HH !mulmxA PPt mul1mx.
  by rewrite -mulmxA PPt mulmx1.
have MME i i' : \sum_j M i j * conjC (M i' j) = sp ord0 i *+ (i == i').
  have /matrixP /(_ i i') := MMt; rewrite !mxE => <-.
  by apply: eq_bigr => j _; rewrite !mxE.
pose dR (i : 'I_d) : R := \sum_j nsq (M i j).
have spE i : sp ord0 i = (dR i)%:C.
  have := MME i i; rewrite eqxx mulr1n => <-.
  by rewrite /dR rmorph_sum /=; apply: eq_bigr => j _; rewrite nsqE.
have dR_ge0 i : 0 <= dR i by apply: sumr_ge0 => j _; exact: nsq_ge0.
have row0 i : dR i = 0 -> row i M = 0.
  move=> /eqP; rewrite psumr_eq0 => [/allP M0|j _]; last exact: nsq_ge0.
  apply/rowP => j; rewrite [LHS]mxE [RHS]mxE; apply/eqP; rewrite -nsq_eq0.
  by have := M0 j; rewrite mem_index_enum => /(_ isT).
pose J := [pred i | dR i != 0].
pose idx (k : 'I_#|J|) : 'I_d := enum_val k.
have idx_gt0 k : 0 < dR (idx k).
  by rewrite lt_neqAle eq_sym dR_ge0 andbT; exact: (enum_valP k).
pose F (k : 'I_#|J|) : 'cV[C]_d := (row (idx k) P)^t*.
pose G (k : 'I_#|J|) : 'cV[C]_d :=
  (Num.sqrt (dR (idx k)))^-1%:C *: (row (idx k) M)^T.
exists #|J|, F, G, (fun k => dR (idx k)); split=> //.
- move=> k l; rewrite /cdot /F trmxCK -(inj_eq enum_val_inj).
  have /matrixP /(_ (idx k) (idx l)) := PPt; rewrite !mxE => <-.
  by apply: eq_bigr => j _; rewrite !mxE.
- move=> k l.
  have -> : cdot (G k) (G l) =
      ((Num.sqrt (dR (idx k)))^-1 * (Num.sqrt (dR (idx l)))^-1)%:C *
      \sum_j M (idx l) j * conjC (M (idx k) j).
    rewrite /cdot mxE mulr_sumr; apply: eq_bigr => j _.
    rewrite !mxE rmorphM /= conjC_real rmorphM /=.
    by rewrite mulrACA [conjC _ * _]mulrC.
  rewrite MME (inj_eq enum_val_inj) eq_sym.
  have [->|_] := eqVneq k l; last by rewrite mulr0n mulr0.
  rewrite mulr1n spE -rmorphM /= -invfM -expr2 sqr_sqrtr //.
  by rewrite mulVf ?rmorph1 // gt_eqF.
- have LE : L = \sum_i (row i P)^t* *m row i M.
    rewrite -[LHS]mul1mx -PtP -mulmxA -/M; apply/matrixP => x y.
    rewrite mxE summxE; apply: eq_bigr => i _.
    by rewrite !mxE big_ord1 !mxE.
  rewrite {1}LE (bigID (mem J)) /= [X in _ + X]big1 ?addr0 => [|i].
    rewrite big_enum_val; apply: eq_bigr => k _.
    rewrite /edge /G /F linearZ /= trmxK -scalemxAr scalerA -rmorphM /=.
    by rewrite divff ?scale1r // gt_eqF // sqrtr_gt0.
  by rewrite inE negbK => /eqP /row0 ->; rewrite mulmx0.
Qed.

(** ** Step 3: one layer

    The two marginals of a layer, rescaled to mass one, are terms [s] and
    [t] in the bases of Step 1. DIRAC closes every edge and COH gives
    [s =_c t] with [c] the cost of the layer. The number [m] is the mass
    of the layer. *)
Lemma layer_derivable L :
  L != 0 ->
  exists (s t : term d) (e m : R),
    [/\ 0 < m, qeq e s t, L *m L^t* = m%:C *: tden s,
        (L^t* *m L)^T = m%:C *: tden t
      & complex.Re (\tr (linterp L *m Pasym d)) = m * e].
Proof.
move=> L_neq0.
have [n [F [G [sv [F_orth G_orth sv_gt0 LE]]]]] := schmidt_decomp L.
pose m := \sum_k sv k.
have m_gt0 : 0 < m.
  have [n0|n_gt0] := posnP n.
    move: L_neq0; rewrite LE big1 ?eqxx // => k _.
    by have := ltn_ord k; rewrite [X in (_ < X)%N]n0.
  rewrite lt_neqAle eq_sym sumr_ge0 ?andbT => [|k _]; last exact: ltW.
  rewrite psumr_neq0 => [|k _]; last exact: ltW.
  by apply/hasP; exists (Ordinal n_gt0); rewrite ?mem_index_enum ?sv_gt0.
pose w k := sv k / m.
have w_gt0 k : 0 < w k by rewrite divr_gt0.
have w_sum : \sum_k w k = 1 by rewrite -mulr_suml divff // gt_eqF.
pose f k := kvec (F k); pose g k := kvec (G k).
have f_orth : orthonormal f.
  by move=> k l; rewrite /kdot !kden_kvec; exact: F_orth.
have g_orth : orthonormal g.
  by move=> k l; rewrite /kdot !kden_kvec; exact: G_orth.
pose c : C := (Num.sqrt m)%:C.
have LE' : L = c *: coh_layer f g w.
  rewrite LE /coh_layer scaler_sumr; apply: eq_bigr => k _.
  rewrite scalerA /f /g !kden_kvec; congr (_ *: _).
  rewrite /c /amp -rmorphM /= -sqrtrM ?ltW // /w mulrCA divff ?mulr1 //.
  by rewrite gt_eqF.
have csq : c * conjC c = m%:C.
  by rewrite /c conjC_real -rmorphM /= -expr2 sqr_sqrtr // ltW.
have csq' : conjC c * c = m%:C by rewrite mulrC.
exists (tsum (fun k => KScale (amp (w k)) (f k))),
       (tsum (fun k => KScale (amp (w k)) (g k))),
       (coh_index w (fun k => dirac_index (f k) (g k)) f g), m; split=> //.
- apply: q_coh => // k.
  by apply: q_dirac; rewrite /kunit ?f_orth ?g_orth eqxx.
- rewrite LE' trmxC_scale -scalemxAl -scalemxAr scalerA csq.
  by rewrite coh_layer_margL.
- rewrite LE' trmxC_scale -scalemxAl -scalemxAr scalerA csq' linearZ /=.
  by rewrite coh_layer_margR.
- rewrite LE' linterpZ -scalemxAl mxtraceZ normCK csq Re_scale.
  by rewrite coh_layer_cost.
Qed.

(** ** Step 4: all layers

    MIX, once for each layer after the first. The mixture is nested to
    the right, with the masses renormalised at each step as in
    Proposition 1. *)
Lemma layers_derivable G :
  G != [::] -> all (fun L => L != 0) G ->
  exists (s t : term d) (e m : R),
    [/\ 0 < m, qeq e s t, \sum_(L <- G) L *m L^t* = m%:C *: tden s,
        (\sum_(L <- G) L^t* *m L)^T = m%:C *: tden t
      & gcost Pasym G = m * e].
Proof.
elim: G => // L G IH _ /= /andP[L_neq0 G_neq0].
have [s1 [t1 [e1 [m1 [m1_gt0 H1 HL1 HR1 Hc1]]]]] := layer_derivable L_neq0.
case: G IH G_neq0 => [_ _|L' G IH G_neq0].
  exists s1, t1, e1, m1; rewrite !big_seq1; split=> //.
  by rewrite /gcost /qcost (ginterp_atom L).
have [//|s2 [t2 [e2 [m2 [m2_gt0 H2 HL2 HR2 Hc2]]]]] := IH _ G_neq0.
pose m := m1 + m2; pose p := m1 / m.
have m_gt0 : 0 < m by rewrite addr_gt0.
have p01 : 0 <= p <= 1.
  by rewrite /p ler_pdivrMr // mul1r lerDl divr_ge0 ltW.
have mp : m * p = m1 by rewrite /p mulrCA divff ?mulr1 // gt_eqF.
have mq : m * (1 - p) = m2 by rewrite mulrBr mulr1 mp /m addrAC subrr add0r.
have mix_den (A1 A2 : 'M[C]_d) :
    m1%:C *: A1 + m2%:C *: A2 = m%:C *: (p%:C *: A1 + (1 - p%:C) *: A2).
  rewrite scalerDr !scalerA -(rmorph1 (real_complex R)) -rmorphB -!rmorphM /=.
  by rewrite mp mq.
exists (tmix p s1 s2), (tmix p t1 t2), (p * e1 + (1 - p) * e2), m; split=> //.
- exact: q_mix.
- by rewrite big_cons HL1 HL2 tden_mix // mix_den.
- by rewrite tden_mix // -mix_den big_cons linearD /= HR1 HR2.
- rewrite /gcost /qcost ginterp_cons mulmxDl linearD /= Re_D Hc1.
  rewrite -/(qcost _ _) -/(gcost _ _) Hc2.
  by rewrite -[in LHS]mp -[in LHS]mq -2!mulrA -mulrDr.
Qed.

(** ** Theorem 5 (Completeness)

    For state terms the distance itself is the index of a derivation. *)
Theorem qeq_attained s t :
  state_term s -> state_term t ->
  exists2 e : R, qeq e s t & T (tden s) (tden t) = e%:E.
Proof.
move=> s_state t_state.
have rho_dens := state_term_density s_state.
have sigma_dens := state_term_density t_state.
have [tau /set_mem Htau HT] :=
  Tc_attained Pasym (kron_mem_QCouplings rho_dens sigma_dens).
have [G [HG [G_lgraph HmL HmR] G_neq0 _]] := graph_completeness Htau.
have G_nonnil : G != [::].
  apply: contra_eq_neq G_lgraph => ->.
  by rewrite /gmass big_nil eq_sym oner_eq0.
have [s' [t' [e [m [m_gt0 Hq HL HR Hc]]]]] := layers_derivable G_nonnil G_neq0.
have [s'_state t'_state] := qeq_state Hq.
have m1 : m = 1.
  apply: complexI; rewrite rmorph1 -[LHS]mulr1 -[X in _ * X]s'_state tmass_tr.
  by rewrite -mxtraceZ -HL -margL_mx HmL -tmass_tr.
exists e; last first.
  by rewrite /T HT -HG -/(qcost _ _) -/(gcost _ _) Hc m1 mul1r.
apply: q_la Hq _; apply: laeq_complete.
  by rewrite -HmL margL_mx HL m1 rmorph1 scale1r.
by rewrite -HmR margR_mx HR m1 rmorph1 scale1r.
Qed.

Theorem qeq_complete e s t :
  state_term s -> state_term t ->
  (T (tden s) (tden t) <= e%:E)%E -> qeq e s t.
Proof.
move=> s_state t_state; have [e' He' ->] := qeq_attained s_state t_state.
by rewrite lee_fin; exact: q_max.
Qed.

(** Soundness and completeness together. *)
Corollary qeqP e s t :
  state_term s -> state_term t ->
  qeq e s t <-> (T (tden s) (tden t) <= e%:E)%E.
Proof.
by move=> s_state t_state; split; [exact: qeq_T | exact: qeq_complete].
Qed.

(** ** Corollary 4

    [T(⟦s⟧, ⟦t⟧) = min {ε : s =_ε t is derivable}]. *)
Corollary T_min s t :
  state_term s -> state_term t ->
  T (tden s) (tden t) = ereal_inf [set e%:E | e in [set e | qeq e s t]].
Proof.
move=> s_state t_state; apply/eqP; rewrite eq_le; apply/andP; split.
  by apply/ereal_infP => _ [e /= He <-]; exact: qeq_T.
have [e He ->] := qeq_attained s_state t_state.
by apply: ge_ereal_inf; exists e%:E => //; exists e.
Qed.

End Completeness.
