(** * The quantitative rules

    The judgment [s =_ε t] between terms (Section 9.4 of the notes, Figure
    4), read as "[s] can be transported to [t] at antisymmetric cost at
    most [ε]". It is the least relation closed under DIRAC, MIX, COH, LA
    and MAX. *)

From QOT Require Import Prelude.
From Template Require Import DensityTerms DensityEquality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section Deduction.

Variable d : nat.

Implicit Types (a b : ket d) (s t : term d) (e p : R).

(** The index of DIRAC: the probability [1/2 (1 - |<a|b>|^2)] that the
    SWAP test reports "different" on [|a> ⊗ |b>]. *)
Definition dirac_index a b : R := 2^-1 * (1 - nsq (kdot a b)).

(** The mirror overlap (47) of the pairs [k] and [l] of two families:
    [ω_kl = <f_k|g_l> <g_k|f_l>]. *)
Definition mirror (n : nat) (f g : 'I_n -> ket d) (k l : 'I_n) : C :=
  kdot (f k) (g l) * kdot (g k) (f l).

Lemma mirror_conj n (f g : 'I_n -> ket d) k l :
  mirror f g l k = conjC (mirror f g k l).
Proof. by rewrite /mirror rmorphM /= -!kdot_conj mulrC. Qed.

Lemma mirror_diag n (f g : 'I_n -> ket d) k :
  mirror f g k k = (nsq (kdot (f k) (g k)))%:C.
Proof. by rewrite /mirror nsqE [kdot (g k) _]kdot_conj. Qed.

(** The index of COH. The sum over [k != l] runs over ordered pairs, so
    it contains [ω_kl] together with its conjugate [ω_lk] and only the
    real parts contribute. *)
Definition coh_index (n : nat) (w e : 'I_n -> R) (f g : 'I_n -> ket d) : R :=
  \sum_k w k * e k -
  2^-1 * \sum_k \sum_(l | l != k)
           Num.sqrt (w k * w l) * complex.Re (mirror f g k l).

(** A family of ket terms is orthonormal. *)
Definition orthonormal (n : nat) (f : 'I_n -> ket d) : Prop :=
  forall k l, kdot (f k) (f l) = (k == l)%:R.

(** The five rules of Figure 4. *)
Inductive qeq : R -> term d -> term d -> Prop :=
| q_dirac a b :
    kunit a -> kunit b ->
    qeq (dirac_index a b) (TKet a) (TKet b)
| q_mix p e e' s t s' t' :
    0 <= p <= 1 -> qeq e s t -> qeq e' s' t' ->
    qeq (p * e + (1 - p) * e') (tmix p s s') (tmix p t t')
| q_coh n (f g : 'I_n -> ket d) (w e : 'I_n -> R) :
    (forall k, qeq (e k) (TKet (f k)) (TKet (g k))) ->
    orthonormal f -> orthonormal g ->
    (forall k, 0 < w k) -> \sum_k w k = 1 ->
    qeq (coh_index w e f g)
      (tsum (fun k => KScale (amp (w k)) (f k)))
      (tsum (fun k => KScale (amp (w k)) (g k)))
| q_la e s s' t t' : laeq s s' -> qeq e s' t' -> laeq t' t -> qeq e s t
| q_max e e' s t : qeq e s t -> e <= e' -> qeq e' s t.

(** LA on one side only. *)
Lemma q_la_l e s s' t : laeq s s' -> qeq e s' t -> qeq e s t.
Proof. by move=> Hs Hq; exact: q_la Hs Hq (la_refl _). Qed.

Lemma q_la_r e s t t' : qeq e s t' -> laeq t' t -> qeq e s t.
Proof. by move=> Hq Ht; exact: q_la (la_refl _) Hq Ht. Qed.

(** A rule applies when its index is only equal to the one asked for. *)
Lemma q_eq e e' s t : qeq e s t -> e = e' -> qeq e' s t.
Proof. by move=> Hq <-. Qed.

End Deduction.
