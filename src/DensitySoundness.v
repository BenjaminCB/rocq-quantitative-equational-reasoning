(** * Soundness of the quantitative rules

    Theorem 4 of the notes: a derivation of [s =_ε t] describes a layered
    graph that transports [⟦s⟧] to [⟦t⟧] at antisymmetric cost at most
    [ε], so [T(⟦s⟧, ⟦t⟧) <= ε]. DIRAC draws an edge, COH puts edges in one
    layer (Lemma 8), MIX puts layers side by side and LA renames the
    vertices. *)

From QOT Require Import Prelude Tensor QuantumStates PSD SymAsym Cost.
From QOT Require Import QuantumOptimalTransport LayeredGraphs GraphOperations.
From QOT Require Import GraphCost GraphOptimality.
From mathcomp.algebra_tactics Require Import ring lra.
From Template Require Import DensityTerms DensityEquality DensityDeduction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** ** Real and complex scalars *)

Lemma half_real : (2^-1 : C) = (2^-1 : R)%:C.
Proof. by rewrite fmorphV /= rmorph_nat. Qed.

Lemma Re_scale (x : R) (z : C) : complex.Re (x%:C * z) = x * complex.Re z.
Proof. by case: z => u v /=; rewrite mul0r subr0. Qed.

Lemma Re_B (x y : C) : complex.Re (x - y) = complex.Re x - complex.Re y.
Proof. by case: x => ? ?; case: y. Qed.

(** ** A coupling with a pure marginal

    A coupling of [|a><a|] and [σ] is supported on [|a> ⊗ H], and its
    cost is [1/2 (1 - <a|σ|a>)] ([4], Corollary 2.7). *)
Section PureCoupling.

Variable d : nat.

Lemma kronBl (A B D : 'M[C]_d) : (A - B) *t* D = A *t* D - B *t* D.
Proof.
apply/matrixP => p q.
case/mxvec_indexP: p => i1 i2; case/mxvec_indexP: q => j1 j2.
by rewrite !(kronmxE, mxE) mulrBl.
Qed.

Lemma coupling_pure_cost (a : 'cV[C]_d) (sigma : 'M[C]_d) tau :
  (a^t* *m a) ord0 ord0 = 1 -> QCouplings (a *m a^t*) sigma tau ->
  \tr (tau *m Pasym d) = 2^-1 * (1 - (a^t* *m sigma *m a) ord0 ord0).
Proof.
move=> a_unit [[tau_herm [tau_psd tau_tr]] [HR HL]].
pose Pi : 'M[C]_d := a *m a^t*.
have aa : a^t* *m a = 1%:M by rewrite [LHS]mx11_scalar a_unit.
have PiPi : Pi *m Pi = Pi.
  by rewrite /Pi mulmxA -[a *m _ *m a]mulmxA aa mulmx1.
have Pi_herm : Pi^t* = Pi by rewrite /Pi trmxC_mul trmxCK.
have Htau : tau^t* = tau by move: tau_herm; rewrite herm_eq => /eqP <-.
pose Pl := Pi *t* (1%:M : 'M[C]_d).
pose Pr := (1%:M : 'M[C]_d) *t* Pi.
have Pl_herm : Pl^t* = Pl by rewrite /Pl kron_trmxC Pi_herm trmxC1.
have Pl_tau : Pl *m tau = tau.
  have: ((1%:M - Pi) *t* 1%:M) *m tau = 0.
    apply: psd_quad_zero_mx => //.
    rewrite -ptraceR_trace ptraceR_kron1_conj HR -/Pi.
    by rewrite mulmxBl mul1mx PiPi subrr mul0mx mxtrace0.
  rewrite kronBl kron1mx mulmxBl mul1mx => /eqP.
  by rewrite subr_eq0 => /eqP <-.
have tau_Pl : tau *m Pl = tau.
  by have := congr1 (fun Z => Z^t*) Pl_tau; rewrite trmxC_mul Htau Pl_herm.
have PP_F : Pl *m (Pr *m flipmx d) = Pl *m Pr.
  rewrite mulmxA /Pl /Pr kron_mulmx mulmx1 mul1mx /Pi -kron_mulmx -mulmxA.
  by rewrite (diag_kron_flip_fix (a^t*)).
have trF : \tr (tau *m flipmx d) = (a^t* *m sigma *m a) ord0 ord0.
  rewrite -{1}Pl_tau -[Pl *m tau *m _]mulmxA mxtrace_mulC.
  rewrite -[tau *m _ *m Pl]mulmxA flip_kron_swap -/Pr.
  rewrite -{1}tau_Pl -[tau *m Pl *m _]mulmxA PP_F mulmxA tau_Pl.
  rewrite -ptraceL_trace ptraceL_kron1R_mulR HL /Pi mulmxA mxtrace_mulC.
  by rewrite mulmxA trace_mx11.
rewrite /Pasym -scalemxAr mxtraceZ mulmxBr mulmx1 linearB /= tau_tr trF.
by [].
Qed.

End PureCoupling.

Section Soundness.

Variable d : nat.

Implicit Types (a b : ket d) (s t : term d) (u v : 'cV[C]_d).

(** ** Edges

    The layer of a single edge from the vertex labelled [u] to the vertex
    labelled [v]: its vectorisation is [|u> ⊗ |v>]. *)
Definition edge u v : 'M[C]_d := u *m v^T.

Definition cdot u v : C := (u^t* *m v) ord0 ord0.

Lemma cdot_kden a b : cdot (kden a) (kden b) = kdot a b.
Proof. by []. Qed.

Lemma cdot_mx u v : u^t* *m v = (cdot u v)%:M.
Proof. by rewrite [LHS]mx11_scalar. Qed.

Lemma cdot_tr u v : v^T *m (u^T)^t* = (cdot u v)%:M.
Proof.
rewrite [LHS]mx11_scalar; congr (_%:M); rewrite /cdot !mxE.
by apply: eq_bigr => i _; rewrite !mxE mulrC.
Qed.

Lemma edge_mul_adj u v u' v' :
  edge u v *m (edge u' v')^t* = cdot v' v *: (u *m u'^t*).
Proof.
rewrite /edge trmxC_mul mulmxA -[u *m _ *m _]mulmxA cdot_tr.
by rewrite mul_mx_scalar -scalemxAl.
Qed.

Lemma edge_adj_mul u v u' v' :
  ((edge u v)^t* *m edge u' v')^T = cdot u u' *: (v' *m v^t*).
Proof.
rewrite /edge trmxC_mul mulmxA -[_ *m u^t* *m u']mulmxA cdot_mx.
rewrite mul_mx_scalar -scalemxAl linearZ /= trmx_mul trmxK.
by rewrite -map_trmx trmxK.
Qed.

Lemma tr_conj_edge u v u' v' :
  \tr (conjmx (edge u v) *m edge u' v') = cdot v u' * cdot u v'.
Proof.
have -> : conjmx (edge u v) = (u^t*)^T *m v^t*.
  by rewrite /conjmx /edge map_mxM map_trmx trmxK.
rewrite mulmxA -[_ *m v^t* *m u']mulmxA cdot_mx mul_mx_scalar -scalemxAl.
rewrite mxtraceZ mxtrace_mulC; congr (_ * _).
rewrite trace_mx11 /cdot !mxE.
by apply: eq_bigr => i _; rewrite !mxE mulrC.
Qed.

Lemma trmxC_sum (I : Type) (r : seq I) (m n : nat) (F : I -> 'M[C]_(m, n)) :
  (\sum_(i <- r) F i)^t* = \sum_(i <- r) (F i)^t*.
Proof.
by apply: (big_morph _ (@trmxC_add m n)); rewrite trmx0 map_mx0.
Qed.

Lemma conjmx_sum (I : Type) (r : seq I) (F : I -> 'M[C]_d) :
  conjmx (\sum_(i <- r) F i) = \sum_(i <- r) conjmx (F i).
Proof.
by apply: (big_morph _ _ (map_mx0 _ _ _)) => A B; exact: map_mxD.
Qed.

(** ** The layer of DIRAC *)

Lemma edge_transports a b :
  kunit a -> kunit b ->
  transports (atom (edge (kden a) (kden b))) (tden (TKet a)) (tden (TKet b)).
Proof.
rewrite /kunit /kdot -!/(cdot _ _) => a_unit b_unit; split.
- rewrite /is_lgraph gmass_atom lmass_trmx edge_mul_adj b_unit scale1r.
  by rewrite mxtrace_mulC trace_mx11.
- by rewrite margL_mx big_seq1 edge_mul_adj b_unit scale1r.
- by rewrite margR_mx big_seq1 edge_adj_mul a_unit scale1r.
Qed.

(** The cost of a coupling of two pure states. *)
Lemma tr_pure_coupling a b tau :
  kunit a -> QCouplings (tden (TKet a)) (tden (TKet b)) tau ->
  \tr (tau *m Pasym d) = (dirac_index a b)%:C.
Proof.
move=> a_unit /(coupling_pure_cost a_unit) ->.
rewrite /dirac_index /= /proj mulmxA -mulmxA !kdot_mx -scalar_mxM mxE eqxx.
rewrite mulr1n [kdot b a]kdot_conj -nsqE.
by rewrite rmorphM rmorphB rmorph1 /= -half_real.
Qed.

Lemma gcost_pure a b (G : lgraph d) :
  kunit a -> transports G (tden (TKet a)) (tden (TKet b)) ->
  gcost Pasym G = dirac_index a b.
Proof.
move=> a_unit /transports_coupling /(tr_pure_coupling a_unit).
by rewrite /gcost /qcost => ->.
Qed.

(** ** Lemma 8 (The layer of COH)

    The layer [|φ> = Σ_k √s_k |f_k> ⊗ |g_k>] of (48) has mass one, the
    mixtures [Σ_k s_k |f_k><f_k|] and [Σ_k s_k |g_k><g_k|] as marginals,
    and the cost that COH gives when every premise is closed by
    DIRAC. *)
Section CohLayer.

Variables (n : nat) (f g : 'I_n -> ket d) (w : 'I_n -> R).
Hypotheses (f_orth : orthonormal f) (g_orth : orthonormal g).
Hypotheses (w_gt0 : forall k, 0 < w k) (w_sum : \sum_k w k = 1).

Definition coh_layer : 'M[C]_d :=
  \sum_k amp (w k) *: edge (kden (f k)) (kden (g k)).

Let w_ge0 k : 0 <= w k. Proof. exact: ltW. Qed.

Lemma coh_layer_adj :
  coh_layer^t* = \sum_k amp (w k) *: (edge (kden (f k)) (kden (g k)))^t*.
Proof.
rewrite /coh_layer trmxC_sum; apply: eq_bigr => k _.
by rewrite trmxC_scale amp_conj.
Qed.

Lemma coh_layer_margL :
  coh_layer *m coh_layer^t* = tden (tsum (fun k => KScale (amp (w k)) (f k))).
Proof.
rewrite tden_tsum coh_layer_adj /coh_layer mulmx_suml.
apply: eq_bigr => k _; rewrite mulmx_sumr (bigD1 k) //= big1 => [|l l_ne].
  rewrite addr0 -scalemxAl -scalemxAr scalerA edge_mul_adj.
  rewrite cdot_kden g_orth eqxx scale1r projZ amp_conj.
  by [].
rewrite -scalemxAl -scalemxAr edge_mul_adj cdot_kden g_orth.
by rewrite (negbTE l_ne) scale0r !scaler0.
Qed.

Lemma coh_layer_margR :
  (coh_layer^t* *m coh_layer)^T =
  tden (tsum (fun k => KScale (amp (w k)) (g k))).
Proof.
rewrite tden_tsum coh_layer_adj /coh_layer mulmx_suml linear_sum /=.
apply: eq_bigr => k _; rewrite mulmx_sumr linear_sum /=.
rewrite (bigD1 k) //= big1 => [|l l_ne].
  rewrite addr0 -scalemxAl -scalemxAr scalerA linearZ /= edge_adj_mul.
  by rewrite cdot_kden f_orth eqxx scale1r projZ amp_conj.
rewrite -scalemxAl -scalemxAr !linearZ /= edge_adj_mul cdot_kden f_orth.
by rewrite eq_sym (negbTE l_ne) scale0r !scaler0.
Qed.

Lemma coh_layer_mass : lmass coh_layer = 1.
Proof.
rewrite lmass_trmx coh_layer_margL -tmass_tr tmass_tsum.
rewrite -[RHS](rmorph1 (real_complex R)) -w_sum rmorph_sum /=.
apply: eq_bigr => k _.
by rewrite kdotZl kdotZr f_orth eqxx mulr1 amp_conj amp_sq.
Qed.

Lemma coh_layer_overlap :
  \tr (conjmx coh_layer *m coh_layer) =
  \sum_k \sum_l (Num.sqrt (w k * w l))%:C * mirror f g k l.
Proof.
rewrite /coh_layer conjmx_sum mulmx_suml raddf_sum /=.
apply: eq_bigr => k _; rewrite mulmx_sumr raddf_sum /=.
apply: eq_bigr => l _.
have -> : conjmx (amp (w k) *: edge (kden (f k)) (kden (g k))) =
          amp (w k) *: conjmx (edge (kden (f k)) (kden (g k))).
  by rewrite /conjmx map_mxZ; congr (_ *: _); exact: amp_conj.
rewrite -scalemxAl -scalemxAr scalerA mxtraceZ tr_conj_edge.
rewrite sqrtrM // rmorphM /= !cdot_kden /mirror /amp.
by congr (_ * _); rewrite mulrC.
Qed.

(** The index COH assigns when its premises carry the indices [e]. *)
Lemma coh_layer_cost :
  complex.Re (\tr (linterp coh_layer *m Pasym d)) =
  coh_index w (fun k => dirac_index (f k) (g k)) f g.
Proof.
rewrite cost_layer_overlap coh_layer_mass coh_layer_overlap half_real.
rewrite Re_scale Re_B Re_sum /coh_index /=.
have -> : \sum_k complex.Re (\sum_l (Num.sqrt (w k * w l))%:C * mirror f g k l)
        = \sum_k (w k * nsq (kdot (f k) (g k)) +
                  \sum_(l | l != k)
                     Num.sqrt (w k * w l) * complex.Re (mirror f g k l)).
  apply: eq_bigr => k _; rewrite Re_sum (bigD1 k) //=; congr (_ + _).
    by rewrite Re_scale mirror_diag /= -expr2 sqrtr_sqr ger0_norm.
  by apply: eq_bigr => l _; rewrite Re_scale.
rewrite big_split /= opprD addrA mulrBr; congr (_ - _).
have half (x y : R) : 2^-1 * (y - y * x) = y * (2^-1 * (1 - x)) by ring.
rewrite -[X in X - _]w_sum -sumrB mulr_sumr; apply: eq_bigr => k _.
exact: half.
Qed.

End CohLayer.

Lemma coh_index_le n (w e e' : 'I_n -> R) (f g : 'I_n -> ket d) :
  (forall k, 0 <= w k) -> (forall k, e k <= e' k) ->
  coh_index w e f g <= coh_index w e' f g.
Proof.
move=> w_ge0 le_e; rewrite /coh_index lerD2r; apply: ler_sum => k _.
exact: ler_wpM2l.
Qed.

(** ** Theorem 4 (Soundness) *)
Theorem qeq_sound e s t :
  qeq e s t ->
  exists2 G : lgraph d, transports G (tden s) (tden t) & gcost Pasym G <= e.
Proof.
elim=> {e s t}.
- move=> a b a_unit b_unit.
  have HG := edge_transports a_unit b_unit.
  by exists (atom (edge (kden a) (kden b))); rewrite ?(gcost_pure a_unit HG).
- move=> p e e' s t s' t' p01 _ [G HG leG] _ [G' HG' leG'].
  have /andP[p_ge0 p_le1] := p01.
  have pC_ge0 : 0 <= p%:C :> C by rewrite ler0c.
  have pC_le1 : p%:C <= 1 :> C by rewrite -(rmorph1 (real_complex R)) lecR.
  exists (csum p%:C G G').
    by rewrite !tden_mix //; exact: transports_csum.
  rewrite /gcost ginterp_csum // qcost_convex ?subr_ge0 //.
  rewrite -(rmorph1 (real_complex R)) -rmorphB /=.
  by rewrite lerD // ler_wpM2l // subr_ge0.
- move=> n f g w e _ IH f_orth g_orth w_gt0 w_sum.
  have f_unit k : kunit (f k) by rewrite /kunit f_orth eqxx.
  exists (atom (coh_layer f g w)).
    split.
    + by rewrite /is_lgraph gmass_atom coh_layer_mass.
    + by rewrite margL_mx big_seq1 coh_layer_margL.
    + by rewrite margR_mx big_seq1 coh_layer_margR.
  rewrite /gcost /qcost ginterp_atom coh_layer_cost //.
  apply: coh_index_le => k; first exact: ltW.
  by have [G HG] := IH k; rewrite (gcost_pure (f_unit k) HG).
- move=> e s s' t t' /laeq_sound -> _ [G HG leG] /laeq_sound <-.
  by exists G.
- move=> e e' s t _ [G HG leG] le_e.
  by exists G => //; exact: le_trans leG le_e.
Qed.

(** In particular [T(⟦s⟧, ⟦t⟧) <= ε]. *)
Corollary qeq_T e s t : qeq e s t -> (T (tden s) (tden t) <= e%:E)%E.
Proof.
move=> /qeq_sound [G /transports_coupling HG leG].
apply: le_trans (Tc_le_qcost Pasym HG) _.
by rewrite lee_fin.
Qed.

(** Both sides of a derivable equation are state terms, and its index is
    nonnegative. *)
Corollary qeq_state e s t : qeq e s t -> state_term s /\ state_term t.
Proof.
move=> /qeq_sound [G [HG HL HR] _].
rewrite /state_term !tmass_tr -HL -HR /margL /margR.
by rewrite ptraceR_trace ptraceL_trace -gmass_tr.
Qed.

Corollary qeq_ge0 e s t : qeq e s t -> 0 <= e.
Proof.
move=> /qeq_T; rewrite -lee_fin; apply: le_trans.
exact: T_ge0.
Qed.

End Soundness.
