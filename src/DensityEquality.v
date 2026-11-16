(** * The rules of linear algebra

    The judgment [s = t] between terms (Section 9.3 of the notes): the
    least congruence for [+], with [+] associative, that contains the
    rules KET, ZERO and ENS. Lemma 7 says that it is sound and complete
    for equality of the matrices the terms denote. *)

From QOT Require Import Prelude Tensor QuantumStates PSD Cost LayeredGraphs.
From Template Require Import DensityTerms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** ** Two ensembles with the same Gram matrix

    The linear algebra behind ENS. An ensemble of [N] vectors of [ℂ^d] is
    a matrix [X] with [N] rows, and the matrix it mixes to is the
    transpose of [X^t* *m X]. If two ensembles mix to the same matrix
    then, after padding both with [N] zero vectors, one is a unitary
    combination of the other [9].

    The padding makes room for the unitary: the map [K] sending the
    vectors of [X] to those of [Y] is only a partial isometry, and
    [[K, 1 - K K^t*], [1 - K^t* K, K^t*]] is a unitary that extends it. *)
Section GramDilation.

Variables N d : nat.

(** The case of a diagonal Gram matrix. The inverse of [0] is [0], so
    [sp^-1] is the pseudoinverse of the diagonal. *)
Lemma partial_isometry_diag (X Y : 'M[C]_(N, d)) (sp : 'rV[C]_d) :
  X^t* *m X = diag_mx sp -> Y^t* *m Y = diag_mx sp ->
  exists K : 'M[C]_N,
    [/\ K *m X = Y, K^t* *m Y = X & K *m K^t* *m K = K].
Proof.
move=> HX HY.
pose spV : 'rV[C]_d := \row_i (sp ord0 i)^-1.
have sp_sum (Z : 'M[C]_(N, d)) i :
    Z^t* *m Z = diag_mx sp -> sp ord0 i = \sum_k conjC (Z k i) * Z k i.
  move=> /matrixP /(_ i i); rewrite !mxE eqxx mulr1n => <-.
  by apply: eq_bigr => k _; rewrite !mxE.
have sp_real i : conjC (sp ord0 i) = sp ord0 i.
  rewrite (sp_sum X) // rmorph_sum /=; apply: eq_bigr => k _.
  by rewrite rmorphM /= conjCK mulrC.
have spV_herm : (diag_mx spV)^t* = diag_mx spV.
  rewrite tr_diag_mx map_diag_mx; congr diag_mx; apply/rowP => i.
  by rewrite !mxE fmorphV; congr (_^-1); exact: sp_real.
have col0 (Z : 'M[C]_(N, d)) k i :
    Z^t* *m Z = diag_mx sp -> sp ord0 i = 0 -> Z k i = 0.
  move=> HZ /eqP; rewrite (sp_sum Z) // psumr_eq0 => [/allP /(_ k)|j _].
    rewrite mem_index_enum => /(_ isT); rewrite mulf_eq0 conjC_eq0 orbb.
    by move/eqP.
  by rewrite mulrC -normCK exprn_ge0.
have absorb (Z : 'M[C]_(N, d)) :
    Z^t* *m Z = diag_mx sp -> Z *m diag_mx spV *m diag_mx sp = Z.
  move=> HZ; rewrite -mulmxA mulmx_diag mul_mx_diag; apply/matrixP => k i.
  rewrite !mxE; have [sp0|sp_neq0] := eqVneq (sp ord0 i) 0.
    by rewrite (col0 Z) // mul0r.
  by rewrite mulVf // mulr1.
have spVK p (Z : 'M[C]_(p, d)) :
    Z *m diag_mx spV *m diag_mx sp *m diag_mx spV = Z *m diag_mx spV.
  rewrite -!mulmxA !mulmx_diag; congr (_ *m diag_mx _); apply/rowP => i.
  rewrite !mxE; have [->|sp_neq0] := eqVneq (sp ord0 i) 0.
    by rewrite invr0 !mul0r.
  by rewrite mulrA mulVf // mul1r.
have HXl p (Z : 'M[C]_(p, d)) : Z *m X^t* *m X = Z *m diag_mx sp.
  by rewrite -mulmxA HX.
have HYl p (Z : 'M[C]_(p, d)) : Z *m Y^t* *m Y = Z *m diag_mx sp.
  by rewrite -mulmxA HY.
exists (Y *m diag_mx spV *m X^t*); split.
- by rewrite HXl absorb.
- by rewrite !trmxC_mul trmxCK spV_herm !mulmxA HYl absorb.
- by rewrite !trmxC_mul trmxCK spV_herm !mulmxA HXl HYl !spVK.
Qed.

(** The general case, by diagonalising the Gram matrix. *)
Lemma partial_isometry (X Y : 'M[C]_(N, d)) :
  X^t* *m X = Y^t* *m Y ->
  exists K : 'M[C]_N,
    [/\ K *m X = Y, K^t* *m Y = X & K *m K^t* *m K = K].
Proof.
move=> HXY; pose G := X^t* *m X.
have G_herm : G \is hermsymmx by rewrite herm_eq /G trmxC_mul trmxCK.
pose P := spectralmx G; pose sp := spectral_diag G.
have PPt : P *m P^t* = 1%:M by apply/unitarymxP; exact: spectral_unitarymx.
have PtP : P^t* *m P = 1%:M.
  by apply: unitary_trmxCV; exact: spectral_unitarymx.
have HG : G = P^t* *m diag_mx sp *m P by exact: spectral_decomp.
have diagE (Z : 'M[C]_(N, d)) :
    Z^t* *m Z = G -> (Z *m P^t*)^t* *m (Z *m P^t*) = diag_mx sp.
  move=> HZ; rewrite trmxC_mul trmxCK mulmxA -[P *m _ *m Z]mulmxA HZ HG.
  by rewrite !mulmxA PPt mul1mx -mulmxA PPt mulmx1.
have [K [HK HKt HKK]] :=
  partial_isometry_diag (diagE X (erefl _)) (diagE Y (esym HXY)).
exists K; split=> //.
- by rewrite -[X]mulmx1 -PtP [X *m _]mulmxA mulmxA HK -mulmxA PtP mulmx1.
- by rewrite -[Y]mulmx1 -PtP [Y *m _]mulmxA mulmxA HKt -mulmxA PtP mulmx1.
Qed.

(** The unitary that extends a partial isometry. *)
Lemma partial_isometry_unitary (K : 'M[C]_N) :
  K *m K^t* *m K = K ->
  block_mx K (1%:M - K *m K^t*) (1%:M - K^t* *m K) (K^t*) \is unitarymx.
Proof.
move=> HK.
have HKt : K^t* *m K *m K^t* = K^t*.
  by have := congr1 (fun Z => Z^t*) HK; rewrite !trmxC_mul trmxCK mulmxA.
have herm1 : (1%:M - K *m K^t*)^t* = 1%:M - K *m K^t*.
  by rewrite trmxC_sub trmxC1 trmxC_mul trmxCK.
have herm2 : (1%:M - K^t* *m K)^t* = 1%:M - K^t* *m K.
  by rewrite trmxC_sub trmxC1 trmxC_mul trmxCK.
apply/unitarymxP.
rewrite tr_block_mx map_block_mx herm1 herm2 trmxCK mulmx_block.
rewrite [in RHS](@scalar_mx_block _ N N); congr block_mx.
- rewrite mulmxBl mul1mx mulmxBr mulmx1 mulmxA HK.
  by rewrite subrr subr0 addrC subrK.
- by rewrite mulmxBr mulmx1 mulmxBl mul1mx mulmxA HK !subrr addr0.
- by rewrite mulmxBl mul1mx mulmxBr mulmx1 mulmxA HKt !subrr addr0.
- rewrite mulmxBl mul1mx mulmxBr mulmx1 mulmxA HKt.
  by rewrite subrr subr0 subrK.
Qed.

Theorem gram_dilation (X Y : 'M[C]_(N, d)) :
  X^t* *m X = Y^t* *m Y ->
  exists2 U : 'M[C]_(N + N),
    U \is unitarymx & U *m col_mx X 0 = col_mx Y 0.
Proof.
move=> /partial_isometry [K [HK HKt HKK]].
exists (block_mx K (1%:M - K *m K^t*) (1%:M - K^t* *m K) (K^t*)).
  exact: partial_isometry_unitary.
rewrite mul_block_col !mulmx0 !addr0 HK; congr col_mx.
by rewrite mulmxBl mul1mx -mulmxA HK HKt subrr.
Qed.

End GramDilation.

Section Equality.

Variable d : nat.

Implicit Types (a b : ket d) (s t u : term d).

(** ** The judgment *)

(** The linear combination [Σ_k c_k a_k] of a family of ket terms. *)
Definition klin (n : nat) (c : 'I_n -> C) (a : 'I_n -> ket d) : ket d :=
  ksum [seq KScale (c k) (a k) | k <- enum 'I_n].

Lemma kden_klin n (c : 'I_n -> C) (a : 'I_n -> ket d) :
  kden (klin c a) = \sum_k c k *: kden (a k).
Proof. by rewrite /klin kden_ksum big_map big_enum. Qed.

(** KET, ZERO and ENS, and the closure conditions. In ENS the unitary
    acts on the list of brackets: the family [a] of [n] ket terms is
    replaced by the [n] combinations [Σ_k U_lk a_k]. For [n = 0] both
    sides are [[0]]. *)
Inductive laeq : term d -> term d -> Prop :=
| la_ket a b : keq a b -> laeq (TKet a) (TKet b)
| la_zero s : laeq (TAdd s (TKet KZero)) s
| la_ens n (U : 'M[C]_n) (a : 'I_n -> ket d) :
    U \is unitarymx ->
    laeq (tsum a) (tsum (fun l => klin (U l) a))
| la_assoc s t u : laeq (TAdd (TAdd s t) u) (TAdd s (TAdd t u))
| la_cong s s' t t' : laeq s s' -> laeq t t' -> laeq (TAdd s t) (TAdd s' t')
| la_refl s : laeq s s
| la_sym s t : laeq s t -> laeq t s
| la_trans s t u : laeq s t -> laeq t u -> laeq s u.

(** ** Soundness *)

(** The ensemble of a family of ket terms: one row for each ket. *)
Definition ensmx (n : nat) (a : 'I_n -> ket d) : 'M[C]_(n, d) :=
  \matrix_(k, j) kden (a k) j ord0.

Lemma tden_tsum_mx n (a : 'I_n -> ket d) :
  tden (tsum a) = ((ensmx a)^t* *m ensmx a)^T.
Proof.
rewrite tden_tsum; apply/matrixP => i j; rewrite summxE !mxE.
by apply: eq_bigr => k _; rewrite !mxE big_ord1 !mxE mulrC.
Qed.

Lemma ensmx_klin n (U : 'M[C]_n) (a : 'I_n -> ket d) :
  ensmx (fun l => klin (U l) a) = U *m ensmx a.
Proof.
apply/matrixP => l j; rewrite !mxE kden_klin summxE.
by apply: eq_bigr => k _; rewrite !mxE.
Qed.

Theorem laeq_sound s t : laeq s t -> tden s = tden t.
Proof.
elim=> //= {s t}.
- by move=> a b /keq_sound ->.
- by move=> s; rewrite proj0 addr0.
- move=> n U a U_unitary; rewrite !tden_tsum_mx ensmx_klin.
  by rewrite trmxC_mul mulmxA -[_ *m U^t* *m U]mulmxA unitary_trmxCV ?mulmx1.
- by move=> s t u; rewrite addrA.
- by move=> s s' t t' _ -> _ ->.
- by move=> s t u _ -> _ ->.
Qed.

Lemma laeq_mass s t : laeq s t -> tmass s = tmass t.
Proof. by move=> /laeq_sound eq_st; rewrite !tmass_tr eq_st. Qed.

Lemma laeq_state s t : laeq s t -> state_term s -> state_term t.
Proof. by rewrite /state_term => /laeq_mass ->. Qed.

(** ** Completeness *)

(** Inside a bracket one computes with vectors. *)
Lemma la_ket_den a b : kden a = kden b -> laeq (TKet a) (TKet b).
Proof. by move=> /keq_complete; exact: la_ket. Qed.

(** *** Step 1: flatten and pad *)

(** The brackets of a term, from left to right: the first one and the
    list of the others. *)
Fixpoint tflat s : ket d * seq (ket d) :=
  match s with
  | TKet a => (a, [::])
  | TAdd s t => ((tflat s).1, (tflat s).2 ++ (tflat t).1 :: (tflat t).2)
  end.

Lemma laeq_tbig_cat a l b l' :
  laeq (TAdd (tbig a l) (tbig b l')) (tbig a (l ++ b :: l')).
Proof.
elim: l a => [|c l IHl] a /=; first exact: la_refl.
by apply: la_trans (la_assoc _ _ _) _; apply: la_cong (la_refl _) (IHl c).
Qed.

Lemma laeq_tflat s : laeq s (tbig (tflat s).1 (tflat s).2).
Proof.
elim: s => [a|s IHs t IHt] /=; first exact: la_refl.
exact: la_trans (la_cong IHs IHt) (laeq_tbig_cat _ _ _ _).
Qed.

Lemma laeq_tbig_rcons0 a l : laeq (tbig a (rcons l KZero)) (tbig a l).
Proof.
elim: l a => [|b l IHl] a /=; first exact: la_zero.
exact: la_cong (la_refl _) (IHl b).
Qed.

Lemma laeq_tbig_pad a l m : laeq (tbig a (l ++ nseq m KZero)) (tbig a l).
Proof.
elim: m => [|m IHm]; first by rewrite cats0; exact: la_refl.
rewrite -addn1 nseqD catA cats1.
exact: la_trans (laeq_tbig_rcons0 _ _) IHm.
Qed.

(** The family of the first [n] brackets of a list, padded with [[0]]. *)
Definition kfam (l : seq (ket d)) (n : nat) (k : 'I_n) : ket d :=
  nth KZero l k.

Lemma map_kfam l n :
  (size l <= n)%N ->
  [seq kfam l k | k <- enum 'I_n] = l ++ nseq (n - size l) KZero.
Proof.
move=> le_ln; apply: (@eq_from_nth _ KZero).
  by rewrite size_map size_enum_ord size_cat size_nseq subnKC.
move=> i; rewrite size_map size_enum_ord => lt_in.
rewrite (nth_map (Ordinal lt_in)) ?size_enum_ord // /kfam nth_enum_ord //.
rewrite nth_cat nth_nseq; case: ltnP => // le_li.
by rewrite nth_default //; case: ifP.
Qed.

Lemma laeq_tsum_kfam s n :
  let l := (tflat s).1 :: (tflat s).2 in
  (size l <= n)%N -> laeq s (tsum (@kfam l n)).
Proof.
move=> l le_ln; rewrite /tsum map_kfam //=.
exact: la_trans (laeq_tflat s) (la_sym (laeq_tbig_pad _ _ _)).
Qed.

Lemma ensmx_kfam_pad l n m :
  (size l <= n)%N ->
  ensmx (@kfam l (n + m)) = col_mx (ensmx (@kfam l n)) 0.
Proof.
move=> le_ln; apply/matrixP => k j; rewrite !mxE.
case: (split_ordP k) => k' ->; rewrite ?col_mxEu ?col_mxEd !mxE //.
by rewrite /kfam /= nth_default ?mxE // (leq_trans le_ln) // leq_addr.
Qed.

(** *** Steps 2 to 6: one ensemble is a unitary combination of the other *)

(** A sum of brackets may be rewritten bracket by bracket. *)
Lemma laeq_tsum_seq (I : Type) (r : seq I) (f g : I -> ket d) :
  (forall k, kden (f k) = kden (g k)) ->
  laeq (tsum_seq [seq f k | k <- r]) (tsum_seq [seq g k | k <- r]).
Proof.
move=> eq_fg; case: r => [|i r] /=; first exact: la_refl.
elim: r i => [|j r IHr] i /=; first exact: la_ket_den.
exact: la_cong (la_ket_den (eq_fg i)) (IHr j).
Qed.

Lemma laeq_tsum n (f g : 'I_n -> ket d) :
  (forall k, kden (f k) = kden (g k)) -> laeq (tsum f) (tsum g).
Proof. exact: laeq_tsum_seq. Qed.

(** ENS in matrix form: two families of the same size whose ensembles
    are related by a unitary are equal. *)
Lemma la_ens_mx n (U : 'M[C]_n) (a b : 'I_n -> ket d) :
  U \is unitarymx -> ensmx b = U *m ensmx a -> laeq (tsum a) (tsum b).
Proof.
move=> U_unitary Hb; apply: la_trans (la_ens a U_unitary) _.
apply: laeq_tsum => l; apply/colP => j.
by have /matrixP /(_ l j) := Hb; rewrite -ensmx_klin !mxE.
Qed.

(** *** Lemma 7 (Linear algebra is sound and complete for equality) *)
Theorem laeq_complete s t : tden s = tden t -> laeq s t.
Proof.
move=> eq_st.
pose ls := (tflat s).1 :: (tflat s).2; pose lt := (tflat t).1 :: (tflat t).2.
pose n := (size ls + size lt)%N.
have le_s : (size ls <= n)%N by exact: leq_addr.
have le_t : (size lt <= n)%N by exact: leq_addl.
have Hs : laeq s (tsum (@kfam ls (n + n))).
  by apply: laeq_tsum_kfam; exact: leq_trans le_s (leq_addr _ _).
have Ht : laeq t (tsum (@kfam lt (n + n))).
  by apply: laeq_tsum_kfam; exact: leq_trans le_t (leq_addr _ _).
have H : tden (tsum (@kfam ls (n + n))) = tden (tsum (@kfam lt (n + n))).
  by rewrite -(laeq_sound Hs) -(laeq_sound Ht).
apply: la_trans Hs (la_trans _ (la_sym Ht)).
have pad_s := @ensmx_kfam_pad ls n n le_s.
have pad_t := @ensmx_kfam_pad lt n n le_t.
move: H; rewrite !tden_tsum_mx pad_s pad_t => /trmx_inj.
rewrite !tr_col_mx !map_row_mx !mul_row_col !trmx0 !map_mx0 !mul0mx !addr0.
case/gram_dilation=> U U_unitary HU.
by apply: (la_ens_mx U_unitary); rewrite pad_s pad_t.
Qed.

Corollary laeqP s t : laeq s t <-> tden s = tden t.
Proof. by split; [exact: laeq_sound | exact: laeq_complete]. Qed.

End Equality.
