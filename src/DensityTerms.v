(** * Terms for density matrices

    The syntax of the quantitative equational theory of density matrices:
    ket terms, which denote vectors of [ℂ^d], and terms, which denote
    positive semidefinite matrices. A sum inside a bracket is a
    superposition and a sum outside is a mixture.

    The scalars [C], the predicates [psdmx] and [is_density] and the cost
    [T] come from the library [QOT]. *)

From QOT Require Import Prelude QuantumStates PSD LayeredGraphs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(** ** Real numbers inside the complex numbers

    Weights and indices are real numbers, and amplitudes are complex. *)

(** The squared modulus of a complex number, as a real number. *)
Definition nsq (z : C) : R := complex.Re z ^+ 2 + complex.Im z ^+ 2.

Lemma nsqE (z : C) : (nsq z)%:C = z * conjC z.
Proof. by rewrite /nsq add_Re2_Im2 sqr_normc. Qed.

Lemma nsqE' (z : C) : (nsq z)%:C = conjC z * z.
Proof. by rewrite nsqE mulrC. Qed.

Lemma nsq_ge0 (z : C) : 0 <= nsq z.
Proof. by rewrite /nsq addr_ge0 // sqr_ge0. Qed.

Lemma nsq_eq0 (z : C) : (nsq z == 0) = (z == 0).
Proof.
by rewrite -(inj_eq (@complexI _)) nsqE mulf_eq0 conjC_eq0 orbb.
Qed.

Lemma nsq_conj (z : C) : nsq (conjC z) = nsq z.
Proof. by apply: complexI; rewrite !nsqE conjCK mulrC. Qed.

Lemma nsq0 : nsq 0 = 0.
Proof. by apply: complexI; rewrite nsqE mul0r. Qed.

Lemma nsq1 : nsq 1 = 1.
Proof. by apply: complexI; rewrite nsqE mul1r conjC1. Qed.

Lemma conjC_real (x : R) : conjC (x%:C) = x%:C.
Proof. exact: conjc_real. Qed.

Lemma Re_real (x : R) : complex.Re (x%:C) = x.
Proof. by []. Qed.

(** The amplitude of a weight. *)
Definition amp (p : R) : C := (Num.sqrt p)%:C.

Lemma amp_sq (p : R) : 0 <= p -> amp p * amp p = p%:C.
Proof. by move=> p_ge0; rewrite /amp -rmorphM /= -expr2 sqr_sqrtr. Qed.

Lemma amp_conj (p : R) : conjC (amp p) = amp p.
Proof. exact: conjC_real. Qed.

Lemma amp0 : amp 0 = 0.
Proof. by rewrite /amp sqrtr0. Qed.

Lemma amp1 : amp 1 = 1.
Proof. by rewrite /amp sqrtr1. Qed.

Lemma ampM (p q : R) : 0 <= p -> amp (p * q) = amp p * amp q.
Proof. by move=> p_ge0; rewrite /amp sqrtrM // rmorphM. Qed.

Section Terms.

Variable d : nat.

(** ** Ket terms (Definition 10)

    [e_i | 0 | αa | a + a], over the fixed orthonormal basis [e_1, ..., e_d]
    of [ℂ^d]. *)
Inductive ket : Type :=
| KBase of 'I_d
| KZero
| KScale of C & ket
| KAdd of ket & ket.

(** The vector a ket term denotes. *)
Fixpoint kden (a : ket) : 'cV[C]_d :=
  match a with
  | KBase i => delta_mx i ord0
  | KZero => 0
  | KScale c a => c *: kden a
  | KAdd a b => kden a + kden b
  end.

(** The axioms of a vector space, equation (43), closed under the rules of
    equational logic. *)
Inductive keq : ket -> ket -> Prop :=
| keq_addC a b : keq (KAdd a b) (KAdd b a)
| keq_addA a b c : keq (KAdd (KAdd a b) c) (KAdd a (KAdd b c))
| keq_add0 a : keq (KAdd a KZero) a
| keq_scale0 a : keq (KScale 0 a) KZero
| keq_scaleDr c a b : keq (KScale c (KAdd a b)) (KAdd (KScale c a) (KScale c b))
| keq_scaleDl c e a : keq (KScale (c + e) a) (KAdd (KScale c a) (KScale e a))
| keq_scaleA c e a : keq (KScale c (KScale e a)) (KScale (c * e) a)
| keq_scale1 a : keq (KScale 1 a) a
| keq_refl a : keq a a
| keq_sym a b : keq a b -> keq b a
| keq_trans a b c : keq a b -> keq b c -> keq a c
| keq_congD a a' b b' : keq a a' -> keq b b' -> keq (KAdd a b) (KAdd a' b')
| keq_congZ c a a' : keq a a' -> keq (KScale c a) (KScale c a').

(** Two ket terms equal by (43) denote the same vector. *)
Lemma keq_sound a b : keq a b -> kden a = kden b.
Proof.
elim=> //= {a b}.
- by move=> a b; rewrite addrC.
- by move=> a b c; rewrite addrA.
- by move=> a; rewrite addr0.
- by move=> a; rewrite scale0r.
- by move=> c a b; rewrite scalerDr.
- by move=> c e a; rewrite scalerDl.
- by move=> c e a; rewrite scalerA.
- by move=> a; rewrite scale1r.
- by move=> a b c _ -> _ ->.
- by move=> a a' b b' _ -> _ ->.
- by move=> c a a' _ ->.
Qed.

(** *** Completeness of (43)

    Every ket term is equal by (43) to the expansion of its vector in the
    basis, so two ket terms that denote the same vector are equal by
    (43). *)

Lemma keq_0add a : keq (KAdd KZero a) a.
Proof. exact: keq_trans (keq_addC _ _) (keq_add0 a). Qed.

(** [α0 = α(0a) = (α0)a = 0a = 0]. *)
Lemma keq_scaler0 c : keq (KScale c KZero) KZero.
Proof.
apply: keq_trans (keq_scale0 KZero).
apply: keq_trans (keq_congZ c (keq_sym (keq_scale0 KZero))) _.
by apply: keq_trans (keq_scaleA _ _ _) _; rewrite mulr0; exact: keq_refl.
Qed.

Lemma keq_addACA a b c e :
  keq (KAdd (KAdd a b) (KAdd c e)) (KAdd (KAdd a c) (KAdd b e)).
Proof.
apply: keq_trans (keq_addA _ _ _) _.
apply: keq_trans (keq_sym (keq_addA _ _ _)); apply: keq_congD (keq_refl a) _.
apply: keq_trans (keq_sym (keq_addA _ _ _)) _.
apply: keq_trans (keq_addA _ _ _); apply: keq_congD (keq_refl e).
exact: keq_addC.
Qed.

(** The sum of a list of ket terms. *)
Definition ksum (l : seq ket) : ket := foldr KAdd KZero l.

Lemma kden_ksum l : kden (ksum l) = \sum_(a <- l) kden a.
Proof. by elim: l => [|a l IHl] /=; rewrite ?big_nil // big_cons IHl. Qed.

(** The expansion of a vector over a list of basis vectors. *)
Definition kexp (r : seq 'I_d) (v : 'cV[C]_d) : ket :=
  ksum [seq KScale (v i ord0) (KBase i) | i <- r].

(** The ket term of a vector: its expansion in the basis. *)
Definition kvec (v : 'cV[C]_d) : ket := kexp (enum 'I_d) v.

Lemma kexpD r u v : keq (kexp r (u + v)) (KAdd (kexp r u) (kexp r v)).
Proof.
elim: r => [|i r IHr] /=; first exact: keq_sym (keq_add0 _).
apply: keq_trans (keq_addACA _ _ _ _).
by apply: keq_congD IHr; rewrite mxE; exact: keq_scaleDl.
Qed.

Lemma kexpZ r c v : keq (kexp r (c *: v)) (KScale c (kexp r v)).
Proof.
elim: r => [|i r IHr] /=; first exact: keq_sym (keq_scaler0 c).
apply: keq_trans (keq_sym (keq_scaleDr _ _ _)).
by apply: keq_congD IHr; rewrite mxE; exact: keq_sym (keq_scaleA _ _ _).
Qed.

Lemma kexp0 r : keq (kexp r 0) KZero.
Proof.
elim: r => [|i r IHr] /=; first exact: keq_refl.
apply: keq_trans (keq_add0 KZero).
by apply: keq_congD IHr; rewrite mxE; exact: keq_scale0.
Qed.

Lemma kexp_delta r i :
  uniq r -> keq (kexp r (delta_mx i ord0)) (if i \in r then KBase i else KZero).
Proof.
elim: r => [|j r IHr]; first by move=> _; exact: keq_refl.
rewrite /kexp /= inE mxE eqxx andbT [i == j]eq_sym => /andP[j_notin r_uniq].
have [j_eq|j_ne] /= := eqVneq j i.
  move: (IHr r_uniq); rewrite -j_eq (negbTE j_notin) => IH.
  apply: keq_trans (keq_add0 _).
  by apply: keq_congD IH; exact: keq_scale1.
apply: keq_trans (keq_0add _).
by apply: keq_congD (IHr r_uniq); exact: keq_scale0.
Qed.

Lemma keq_kvec a : keq a (kvec (kden a)).
Proof.
elim: a => [i||c a IHa|a IHa b IHb] /=.
- apply: keq_sym; have := kexp_delta i (enum_uniq 'I_d).
  by rewrite mem_enum.
- exact: keq_sym (kexp0 _).
- exact: keq_trans (keq_congZ c IHa) (keq_sym (kexpZ _ _ _)).
- exact: keq_trans (keq_congD IHa IHb) (keq_sym (kexpD _ _ _)).
Qed.

Theorem keq_complete a b : kden a = kden b -> keq a b.
Proof.
move=> eq_ab; apply: keq_trans (keq_kvec a) _.
by rewrite eq_ab; exact: keq_sym (keq_kvec b).
Qed.

Corollary keqP a b : keq a b <-> kden a = kden b.
Proof. by split; [exact: keq_sound | exact: keq_complete]. Qed.

Lemma kden_kvec v : kden (kvec v) = v.
Proof.
rewrite /kvec /kexp kden_ksum big_map big_enum /=.
apply/colP => i; rewrite summxE (bigD1 i) //= big1 ?addr0 => [|j j_ne].
  by rewrite !mxE !eqxx mulr1.
by rewrite !mxE (negbTE (_ : i != j)) ?mulr0 // eq_sym.
Qed.

(** ** The inner product, equation (44) *)

(** [<a|b>], conjugate linear in [a] and linear in [b]. *)
Definition kdot (a b : ket) : C := ((kden a)^t* *m kden b) ord0 ord0.

Lemma kdotE a b : kdot a b = \sum_i conjC (kden a i ord0) * kden b i ord0.
Proof. by rewrite /kdot mxE; apply: eq_bigr => i _; rewrite !mxE. Qed.

Lemma kdot_mx a b : (kden a)^t* *m kden b = (kdot a b)%:M.
Proof. by rewrite [LHS]mx11_scalar. Qed.

(** The three equations of (44). *)
Lemma kdot_base i j : kdot (KBase i) (KBase j) = (i == j)%:R.
Proof.
rewrite kdotE (bigD1 i) //= big1 ?addr0 => [|k k_ne].
  by rewrite !mxE !eqxx conjC1 mul1r andbT eq_sym.
by rewrite !mxE (negbTE k_ne) conjC0 mul0r.
Qed.

Lemma kdot_linear a b c beta gamma :
  kdot a (KAdd (KScale beta b) (KScale gamma c)) =
  beta * kdot a b + gamma * kdot a c.
Proof.
rewrite !kdotE !mulr_sumr -big_split /=; apply: eq_bigr => i _.
by rewrite !mxE mulrDr !mulrA ![conjC _ * _]mulrC.
Qed.

Lemma kdot_conj a b : kdot b a = conjC (kdot a b).
Proof.
rewrite !kdotE rmorph_sum /=; apply: eq_bigr => i _.
by rewrite rmorphM /= conjCK mulrC.
Qed.

Lemma kdotZr a c b : kdot a (KScale c b) = c * kdot a b.
Proof.
rewrite !kdotE mulr_sumr; apply: eq_bigr => i _.
by rewrite !mxE mulrCA.
Qed.

Lemma kdotZl c a b : kdot (KScale c a) b = conjC c * kdot a b.
Proof. by rewrite kdot_conj kdotZr rmorphM /= -kdot_conj. Qed.

Lemma kdot0r a : kdot a KZero = 0.
Proof. by rewrite /kdot /= mulmx0 mxE. Qed.

Lemma kdot0l a : kdot KZero a = 0.
Proof. by rewrite kdot_conj kdot0r conjC0. Qed.

Lemma kdot_ge0 a : 0 <= kdot a a.
Proof.
rewrite kdotE sumr_ge0 // => i _.
by rewrite mulrC -normCK exprn_ge0.
Qed.

(** A ket term is a unit if [<a|a> = 1]. *)
Definition kunit (a : ket) : Prop := kdot a a = 1.

(** ** Terms (Definition 11)

    [s ::= [a] | s + s]. *)
Inductive term : Type :=
| TKet of ket
| TAdd of term & term.

(** The projector [|v><v|] onto a vector, of trace [<v|v>]. *)
Definition proj (v : 'cV[C]_d) : 'M[C]_d := v *m v^t*.

Lemma proj_herm v : proj v \is hermsymmx.
Proof. by rewrite herm_eq /proj trmxC_mul trmxCK. Qed.

Lemma proj_psd v : psdmx (proj v).
Proof. by rewrite /proj -{1}[v]trmxCK; exact: rv_outer_psd. Qed.

Lemma tr_proj v : \tr (proj v) = (v^t* *m v) ord0 ord0.
Proof. by rewrite /proj mxtrace_mulC trace_mx11. Qed.

Lemma projZ c v : proj (c *: v) = (c * conjC c) *: proj v.
Proof. by rewrite /proj trmxC_scale -scalemxAl -scalemxAr scalerA. Qed.

Lemma proj0 : proj 0 = 0.
Proof. by rewrite /proj mul0mx. Qed.

(** The interpretation and the mass of a term. *)
Fixpoint tden (s : term) : 'M[C]_d :=
  match s with
  | TKet a => proj (kden a)
  | TAdd s t => tden s + tden t
  end.

Fixpoint tmass (s : term) : C :=
  match s with
  | TKet a => kdot a a
  | TAdd s t => tmass s + tmass t
  end.

Lemma tmass_tr s : tmass s = \tr (tden s).
Proof.
elim: s => [a|s IHs t IHt] /=; first by rewrite tr_proj.
by rewrite mxtraceD IHs IHt.
Qed.

Lemma tmass_ge0 s : 0 <= tmass s.
Proof.
by elim: s => [a|s IHs t IHt] /=; [exact: kdot_ge0 | exact: addr_ge0].
Qed.

(** Every term denotes a positive semidefinite matrix. *)
Lemma tden_herm s : tden s \is hermsymmx.
Proof.
by elim: s => [a|s IHs t IHt] /=; [exact: proj_herm | exact: hermD].
Qed.

Lemma tden_psd s : psdmx (tden s).
Proof.
by elim: s => [a|s IHs t IHt] /=; [exact: proj_psd | exact: psdD].
Qed.

(** A state term is a term of mass one, and it denotes a density
    matrix. *)
Definition state_term (s : term) : Prop := tmass s = 1.

Lemma state_term_density s : state_term s -> is_density (tden s).
Proof.
move=> s_state; split; first exact: tden_herm.
by split; [exact: tden_psd | rewrite -tmass_tr].
Qed.

Lemma kunit_state a : kunit a -> state_term (TKet a).
Proof. by []. Qed.

(** ** Scalings, equation (45)

    [p [a] = [√p a]], [p (s + t) = p s + p t] and
    [s +_p t = p s + (1 - p) t]. *)
Fixpoint tscale (p : R) (s : term) : term :=
  match s with
  | TKet a => TKet (KScale (amp p) a)
  | TAdd s t => TAdd (tscale p s) (tscale p t)
  end.

Definition tmix (p : R) (s t : term) : term :=
  TAdd (tscale p s) (tscale (1 - p) t).

Lemma tden_scale p s : 0 <= p -> tden (tscale p s) = p%:C *: tden s.
Proof.
move=> p_ge0; elim: s => [a|s IHs t IHt] /=.
  by rewrite projZ amp_conj amp_sq.
by rewrite IHs IHt scalerDr.
Qed.

Lemma tmass_scale p s : 0 <= p -> tmass (tscale p s) = p%:C * tmass s.
Proof. by move=> p_ge0; rewrite !tmass_tr tden_scale // mxtraceZ. Qed.

Lemma tden_mix p s t :
  0 <= p <= 1 ->
  tden (tmix p s t) = p%:C *: tden s + (1 - p%:C) *: tden t.
Proof.
case/andP=> p_ge0 p_le1; rewrite /= !tden_scale ?subr_ge0 //.
by rewrite rmorphB rmorph1.
Qed.

Lemma state_term_mix p s t :
  0 <= p <= 1 -> state_term s -> state_term t -> state_term (tmix p s t).
Proof.
move=> p01 s_state t_state; rewrite /state_term tmass_tr tden_mix //.
rewrite mxtraceD !mxtraceZ -!tmass_tr s_state t_state !mulr1.
by rewrite addrC subrK.
Qed.

(** ** Sums of brackets

    [tsum a] is the term [[a_1] + ... + [a_n]] of a family of [n] ket
    terms, associated to the right. The sum of no brackets is [[0]]. *)
Fixpoint tbig (a : ket) (l : seq ket) : term :=
  if l is b :: l' then TAdd (TKet a) (tbig b l') else TKet a.

Definition tsum_seq (l : seq ket) : term :=
  if l is a :: l' then tbig a l' else TKet KZero.

Definition tsum (n : nat) (a : 'I_n -> ket) : term :=
  tsum_seq [seq a k | k <- enum 'I_n].

Lemma tden_tbig a l : tden (tbig a l) = \sum_(b <- a :: l) proj (kden b).
Proof.
elim: l a => [|b l IHl] a /=; first by rewrite big_seq1.
by rewrite IHl [RHS]big_cons.
Qed.

Lemma tden_tsum_seq l : tden (tsum_seq l) = \sum_(a <- l) proj (kden a).
Proof.
case: l => [|a l]; first by rewrite big_nil /= proj0.
exact: tden_tbig.
Qed.

Lemma tden_tsum n (a : 'I_n -> ket) :
  tden (tsum a) = \sum_k proj (kden (a k)).
Proof. by rewrite /tsum tden_tsum_seq big_map big_enum. Qed.

Lemma tmass_tsum n (a : 'I_n -> ket) : tmass (tsum a) = \sum_k kdot (a k) (a k).
Proof.
rewrite tmass_tr tden_tsum raddf_sum /=.
by apply: eq_bigr => k _; rewrite tr_proj.
Qed.

End Terms.

Arguments KZero {d}.
