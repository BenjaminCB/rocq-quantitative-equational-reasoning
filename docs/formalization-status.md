# Formalization status: *Compact Quantitative Theories of Convex Algebras*

Paper: `docs/paper/compact-quantitative-theories-of-convex-algebras.pdf`
(Matteo Mio, ENTICS Vol. 5, MFPS 2025). Builds on:
`docs/paper/universal-quantitative-algebra-for-fuzzy-relations-and-generalised-metric-spaces.pdf`
([27], Mio–Sarkis–Vignudelli) and
`docs/paper/quantitative-algebraic-reasoning-extended.pdf` ([22], Mardare–Panangaden–Plotkin).

This document records what the `src/` development currently proves against
the paper's numbered results, what's missing, and a proposed order of attack.
All claims below were checked by reading the source; the tree currently
contains zero `Admitted`/`Axiom`/`Parameter`/`Conjecture` (verified by
`grep`), so everything reported "done" is a real proof, not a stub.

## 1. What's already formalized

The proof system itself (`FRelDeduction.v`, `FuzzyRelation.v`, `Signature.v`)
is generic in the signature `sig` and theory `E`, so it corresponds to [27]'s
Definition 4.1 apparatus (Def 2.6–2.18 of the paper under review), not just to
the ICA example: `judgement` = the paper's quantitative equation forms,
`satisfies`/`fuzzy_models` = Def 2.10, `frel_derives` = the proof system
(Init, eq-refl/sym/trans/cong, the `d_B(b,b')` axiom, substitution with
side-conditions, weakening, the `1`-axiom, and — in `FRelFull` mode only —
the infinitary order-completeness rule). `derives_fin`/`derives_full`
correspond to "finite proof" vs. "proof, possibly using the infinitary rule."

On top of that generic core, `ICA.v` instantiates the theory `𝕀ℂ𝔸`
(**§4, Def 4.1**) via `ica_theory` (binary presentation, weights in the open
unit interval), and the remaining files carry out the paper's central
argument for the special case where the carrier of variables is a `finType`:

| Paper result | Repo artifact | File |
|---|---|---|
| Def 4.1 (theory `𝕀ℂ𝔸`) | `ica_theory`, `ica_op`, `ica_weight_*` | `ICA.v` |
| Def 4.2 (Kantorovich lifting `K(d)`) | `kantorovich_lifting` (upstream, re-exported) | `ProbabilityDistribution.v` |
| Prop 4.5 (η is 1-Lipschitz) | `kantorovich_dirac_le` (upstream) | used in `ICAKantorovichSoundness.v` |
| Prop 4.6 (soundness: `(D(A),K(d))` models `𝕀ℂ𝔸`) | `kantorovich_models_ica` | `ICAKantorovichSoundness.v` |
| Cor 4.7 (soundness wrt provability) | `finite_kantorovich_soundness{,_fin}`, `finite_kantorovich_eq_soundness` | `ICAKantorovichSoundness.v` |
| Cor 4.8 (`=` provability ⟺ Birkhoff ⟺ finite quantitative proof), `EqJ` case | `term_distribution_correctness`, `term_distribution_complete` | `BarycentricNormalization.v` |
| Lemma 4.9 (barycentric peeling / interpolation induction) | `extract_exists` and the `term_of_fdist*` family | `BarycentricNormalization.v` |
| Prop 4.10 (completeness, `QEqJ` case, infinitary) | `ica_completeness` | `BarycentricNormalization.v` |
| Prop 4.12 (existence of an *optimal*, not just almost-optimal, coupling) | `kantorovich_optimal_coupling` | `KantorovichCompactness.v` |
| Cor 4.13 (completeness wrt *finite* proofs) | `ica_finite_completeness` | `BarycentricNormalization.v` |

So: soundness and completeness (both the equational and the quantitative
directions, both possibly-infinitary and finitary) are done, and the one
genuinely analytic fact the paper needs and upstream `mathcomp-analysis`
doesn't provide — an exact optimal coupling, not merely an `η`-almost-optimal
one — is proved from scratch via a compactness argument on the encoding of
couplings as row vectors (`KantorovichCompactness.v`). That file's own
header correctly identifies itself as filling exactly this one upstream gap.

Everything above is restricted to `finType` carriers `X` (see §2.1) but is
otherwise a faithful, complete formalization of the paper's core argument
(§4 in its entirety, modulo the finiteness restriction and modulo Theorem
4.14 and Corollary 4.11 not being assembled as standalone statements — see
§2.4).

**M1 update:** Prop 4.10 and Cor 4.13's *completeness* directions are now
additionally available for an arbitrary `choiceType` carrier `A`, not just
`finType`: `ica_completeness_gen` and `ica_finite_completeness_gen`
(`BarycentricNormalization.v`) take `d : A -> A -> R` and `s t : term
ica_signature A` directly, with the Kantorovich hypothesis stated over the
terms' own combined variable set. Cor 4.7's *soundness* direction needed a
different, genuinely new construction (`D(A)`, see §2.1's correction note
under M1) rather than the same transport — that construction is now done
too, see the M1b update below.

**M1b update:** Prop 4.5, Prop 4.6, and Cor 4.7 are now *also* available for
an arbitrary `choiceType` carrier `A`, via `D(A) := gdist R A`
(`GeneralDistribution.v`, finitely-supported distributions over a bare
`choiceType`) and the model built on it in `ICAGeneralSoundness.v`:
`gdirac_interpretation` (Prop 4.5), `gkantorovich_models_ica` (Prop 4.6),
and `g_kantorovich_soundness`/`g_kantorovich_eq_soundness`/
`g_kantorovich_soundness_fin` (Cor 4.7, in its `QEqJ`/`EqJ`/finitary-`QEqJ`
forms respectively). See §3's M1b for the construction.

## 2. What's missing

### 2.1 Generality: carrier restricted to `finType`

The paper's results are stated for an **arbitrary, possibly infinite** fuzzy
relation `(A, d_A)` (Prop 4.6, Cor 4.7, Prop 4.10, Cor 4.13, Thm 4.14 all
open with "Let `(A,d)` be a (possibly infinite) fuzzy relation..."). The
repo's `ProbabilityDistribution.v` builds everything on mathcomp-analysis's
`fdist R X`, which requires `X : finType`. Every downstream theorem
(`ica_completeness`, `ica_finite_completeness`, `term_distribution_*`,
`kantorovich_optimal_coupling`, ...) inherits that restriction.

**This gap is real but shallower than it first looks.** `D(A)` only ever
contains *finitely-supported* distributions, and terms are finite objects,
so nothing here actually needs `fdist`/`kantorovich_lifting` to exist over
an infinite type. The reduction is:

- Every term `s : term ica_signature A` only mentions finitely many
  elements of `A`: `term_vars s` (already present, `BarycentricNormalization.v:152`)
  computes exactly that set by structural recursion — its current type
  (`{set X}` for `X : finType`) is an artifact of where it's used, not of
  its definition; retyped at `{fset X}` for `X : choiceType` it's the same
  function.
- `KantorovichProperties.v`'s `fsum` already uses the relevant idiom: a
  `A : {fset X}` coerces to its own `finType` (`\sum_(x : A) f (fsval x)`),
  so `B := term_vars s ∪ term_vars t` is *already* a `finType` for free via
  that coercion — no bijection needs to be constructed by hand.
- `fuzzy_space`/`judgement`/`frel_derives` (`FuzzyRelation.v`,
  `FRelDeduction.v`) were never restricted to `finType` in the first place —
  only the *Kantorovich model* was. So the proof system itself already
  supports the ambient infinite `A`; only the model construction needs the
  finite subtype.
- One genuine semantic fact is needed to connect the two:
  `K(d_A)(μ,ν) = K(d_A|_B)(μ,ν)` whenever `supp(μ) ∪ supp(ν) ⊆ B`, because
  any coupling of `μ,ν` has support inside `supp(μ)×supp(ν) ⊆ B×B`, so the
  defining infimum never sees anything outside `B`. Standard, not deep.
- And one generic proof-theoretic fact: derivability of
  `⊢ ∀(B,d_A|B).s=_ε t` (finite context `B ⊆ A`) lifts to
  `⊢ ∀(A,d_A).s=_ε t` via `FD_Subst` along the inclusion `B ↪ A`, whose
  side-conditions discharge by `FD_UseVariables` since `d_A|B` is literally
  the restriction of `d_A`. This is fully generic in the signature/theory,
  so it belongs in `FRelDeduction.v`, not `ICA.v`.

So the plan is *not* "rebuild `ProbabilityDistribution.v`/
`KantorovichCompactness.v` over a new carrier type" — it's "transport `s,t`
into the existing finType machinery via the `{fset}`-coercion, run the
already-proved theorems there unchanged, and transport the conclusion back
up." The compactness argument in `KantorovichCompactness.v` in particular
does not need to be touched at all.

#### Worked walkthrough

The four bullets above compress a fair amount; spelled out end to end,
against a concrete instance, the argument runs as follows.

**Setup.** Take `A := nat` (an infinite carrier), some `d_A : A -> A -> R`,
and two fixed terms

```
s = Var 3 <+p+> Var 5
t = Var 3 <+q+> Var 7
```

The target theorem (say Cor 4.13) claims: if `K(d_A)([s],[t]) <= eps` then
`⊢ ∀(A,d_A). s =_eps t` has a finite proof. The context in that judgment is
*all* of `A` — even though `s,t` only mention `{3,5,7}`, `∀(A,d_A).s=_eps t`
is, by Def 2.10, a statement quantified over 1-Lipschitz maps out of the
*whole* of `A` (this is exactly the point of Remark 2.13 in the paper: the
1-Lipschitz side-condition binds the ambient context, not just the
variables a term happens to mention). So it is not obviously true that a
fact provable about the three variables `{3,5,7}` in isolation says anything
about the judgment quantified over all of `A`; the four steps below are
exactly what closes that gap.

**Step 2 (carve out `B`).** `B := term_vars s :|: term_vars t = {3,5,7}`.
`term_vars` is plain structural recursion on the term (`Var x ↦ {x}`,
`App f args ↦` union of the recursive calls over `args`) — nothing about
its definition inspects `A`, so it is exactly as well-defined when `A` is
infinite as when it's a `finType`; the only reason it is currently typed at
`{set X}` (mathcomp's finite-set type, which requires `X` finite) rather
than `{fset X}` (`finmap`'s version, which works for any `X : choiceType`)
is where it happens to be used today. Once retyped, `B : {fset A}` is both
"the finite subset of `A` that `s,t` actually touch" *and*, via `finmap`'s
own coercion, a `finType` in its own right (an element of `B` is an element
of `A` bundled with a proof of membership) — exactly the idiom
`KantorovichProperties.v`'s `fsum` already exploits
(`\sum_(x : A) f (fsval x)` for `A : {fset X}`). So `B` needs no bijection
built by hand; it is simultaneously a subset of the infinite `A` and a ready
made argument to `kantorovich_algebra`, `term_distribution`, and everything
else that currently demands a `finType`.

**Step 3 (the semantic hypothesis transfers to `B`).** `K(d_A)([s],[t])` is
defined as `inf` over `Γ([s],[t])`, the couplings of `[s]` and `[t]`
(Def 2.3/4.2). The fact that makes restricting to `B` lossless is:

> Any coupling `γ` of `μ,ν` satisfies `supp(γ) ⊆ supp(μ) × supp(ν)`.

(If `γ(a,b) > 0` then `μ(a) = Σ_b γ(a,b) > 0`, since one positive summand
forces a nonnegative sum positive, so `a ∈ supp(μ)`; symmetrically for `b`.)
Since `supp([s]) ∪ supp([t]) ⊆ B` by construction — this is precisely
`term_distribution_support`, already proved — *every* coupling that could
possibly appear in `Γ([s],[t])` already has all its mass inside `B × B`,
regardless of whether it is regarded as living in `A × A` or `B × B`. So the
infimum defining `K(d_A)([s],[t])` and the infimum defining
`K(d_A|_B)([s],[t])` (computed with `B` as the ambient finType) range over
literally the same set of couplings, weighted by the same cost function
(`d_A` and `d_A|_B` agree on `B × B` by definition of restriction). The two
numbers coincide: `K(d_A)([s],[t]) ≤ eps ⟺ K(d_A|_B)([s],[t]) ≤ eps`. This
is the one place actual mathematical content, beyond bookkeeping, enters —
everything else in this argument is transport.

**Step 1 (lift the resulting proof back to `A`).** Applying the *existing*
finType theorem to `B` (now legitimately a finType, holding the semantic
hypothesis via step 3) produces a finite proof `⊢ ∀(B,d_A|_B). s =_eps t`.
To turn this into the desired `⊢ ∀(A,d_A). s =_eps t`, use `FD_Subst`: given
a derivation of `phi` in a small context `X`, plus, for every `x,y ∈ X`, a
derivation *in the target context `Y`* that the images of `x,y` under some
substitution `σ` are at distance `≤ d_X(x,y)`, `FD_Subst` produces a
derivation of `phi` with `σ` applied, in context `Y`. Take `X = B`, `Y = A`,
`σ = Var ∘ incl` where `incl : B -> A` just forgets the membership witness
(so `σ` sends each `Var x` to itself, reinterpreted in the bigger type). The
side condition needed, for `x,y ∈ B`, is

```
⊢ ∀(A,d_A). Var (incl x) =_{d_A|_B(x,y)} Var (incl y)
```

`FD_UseVariables` is exactly the axiom that reads distances straight off a
context's own relation: instantiated at `incl x, incl y` it gives, for
free, a bound of exactly `d_A(incl x, incl y)`. And `d_A|_B(x,y)` is *by
construction* `d_A(incl x, incl y)` — not a fact to separately verify, but
how the restricted relation is built in the first place. So the side
condition is discharged with no extra proof obligation, and `FD_Subst`
(noting `σ` applied to `s,t` — terms already entirely over `B` — is just
`s,t` again, reinterpreted) yields exactly `⊢ ∀(A,d_A). s =_eps t`.

**The whole chain:**

```
  Hypothesis:  K(d_A)([s],[t]) ≤ eps            (about the full, infinite A)
                        │  step 3 (coupling support ⊆ B×B)
                        ▼
               K(d_A|_B)([s],[t]) ≤ eps          (same number, computed on finType B)
                        │  already-proved finType theorem, e.g. ica_finite_completeness
                        ▼
        ⊢_fin ∀(B, d_A|_B). s =_eps t             (finite proof, small context)
                        │  step 1: FD_Subst + FD_UseVariables (side condition free)
                        ▼
        ⊢_fin ∀(A, d_A).   s =_eps t              (finite proof, full context — the goal)
```

**Why this is the same theorem, not a weaker one.** The one place this
might look like a shortcut: `∀(A,d_A).s=_eps t` is, semantically, a
statement about 1-Lipschitz maps out of the *whole*, possibly infinite `A`
(Def 2.10) — so how can a derivation built from the three-element `B`
possibly account for all of those interpretations? It doesn't need to,
directly, because that direction is already handled once and for all by
`derives_full_sound`/`derives_fin_sound` in `FRelDeduction.v`: those
theorems say *any* derivation — any term of the `frel_derives` inductive
type, however it was built — is sound at every model, for whatever the
context's carrier type happens to be. They were never restricted to
`finType` in the first place (`fuzzy_space`'s carrier is an arbitrary
`Type`), so nothing about them needs revisiting. The only place `finType`
ever mattered was in *constructing* the proof term — and that is exactly
what steps 2–4 route around, by constructing it over `B` (where the
existing Kantorovich machinery applies) and transporting the syntactic
proof object upward, rather than re-verifying semantics over `A` by hand.

### 2.2 §3: the general theory of compact quantitative theories

Not formalized at all:
- **Def 3.1** — the generic predicate "`E` is compact" (`E ⊨ φ ⟹ E ⊢_fin φ`
  for *all* quantitative equations `φ`, not just the ones about `𝕀ℂ𝔸`).
  Nothing in the repo defines this as a reusable `Prop` parametrized over an
  arbitrary theory `E`; compactness of `𝕀ℂ𝔸` is only visible as the
  conjunction of `term_distribution_correctness` + `ica_finite_completeness`,
  not as an instance of a named general definition.
- **Prop 3.3** (empty signature ⟹ trivially compact) and **Prop 3.4**
  (a theory built entirely from discrete-context equations `∀(B,d_1^B)` is
  compact, because it's really just Birkhoff's theory in disguise) — small,
  self-contained, good warm-up lemmas once Def 3.1 exists.
- **Prop 3.5** (the theory axiomatizing pseudometrics is *not* compact) —
  a genuine negative result, needs a witness relational structure
  `(C, {R_ε})` refuting every finite proof. Independent of everything else;
  good for exercising the infinitary rule from the "this really is needed"
  side.

None of these gate the main line (§4/§5) but a "fully formalized paper"
claim should include them, since Def 3.1 is the paper's own organizing
concept and Prop 3.5 is the result motivating the whole paper.

### 2.3 §5: the generalized theory `𝕀ℂ𝔸^⊕p` and its instances

Entirely unformalized. The paper generalizes §4's argument along the convex
operation `⊕_p : [0,1]² → [0,1]` used inside the interpolation axiom:
- **Def 5.1** (`K^⊕p(d)`, the `⊕_p`-lifting) and **Def 5.2** (theory
  `𝕀ℂ𝔸^⊕p`) — direct generalizations of `K(d)`/`𝕀ℂ𝔸`, parametrizing the
  interpolation axiom's right-hand bound by `⊕_p` instead of the fixed
  `p·ε + (1-p)·δ`.
- **Thm 5.3** — soundness+completeness+compactness of `𝕀ℂ𝔸^⊕p` under three
  abstract conditions on `⊕_p` (monotonicity, a limit inequality, and
  existence of optimal couplings for the `⊕_p`-lifting). This is where the
  work in §2.1 and the specific ICA proofs pay off a second time: the proof
  is described in the paper as "the same proof as Thm 4.14, abstracted over
  `⊕_p`" — so once §4 is generalized past `finType`, Thm 5.3 is mostly a
  re-parametrization exercise, *not* a from-scratch proof.
- **Prop 5.4** — four concrete instances: the standard mean (already done,
  this *is* §4), `max` (giving the Hausdorff-flavored lifting), the
  `k`-Wasserstein family `(p·xᵏ+(1-p)·yᵏ)^{1/k}`, and the log-probability
  operation `x^p·y^{1-p}`. Each instance needs its own proof of the three
  Thm 5.3 hypotheses; `max` and `k`-Wasserstein additionally need an
  existence-of-optimal-coupling argument analogous to
  `kantorovich_optimal_coupling` but for the `⊕_p`-lifted cost (the
  `∞`-Wasserstein case is explicitly flagged in the paper as using only
  *lower semicontinuity*, not continuity, of the evaluation map — a strictly
  harder compactness argument than Prop 4.12's).

This section is optional relative to "formalize the paper's main theorem"
but is presented in the paper as the payoff of the whole construction, so a
complete formalization should include at least the standard + `max` +
`k`-Wasserstein cases.

### 2.4 Loose ends inside §4 itself

- **Cor 4.11** (the free `𝕀ℂ𝔸`-algebra generated by `(A,d_A)` is isomorphic
  to `(D(A), {+_p}, K(d_A))`) is not stated as such. Its ingredients
  (soundness + completeness in both directions) are all present, but no
  lemma packages them into an isomorphism of quantitative algebras (which
  first requires the generic notion of "free algebra," itself only
  described informally in the repo, not defined as a Coq structure).
- **Thm 4.14** (compactness of `𝕀ℂ𝔸` itself) is not stated as one theorem.
  The two cases (`EqJ` via `term_distribution_correctness`, `QEqJ` via
  `ica_finite_completeness` composed with `derives_full`/`derives_fin`) are
  both proved but never assembled into the single "for every quantitative
  equation `φ`, `𝕀ℂ𝔸 ⊨ φ ⟹ 𝕀ℂ𝔸 ⊢_fin φ`" statement, and can't be phrased
  as an instance of a general `IsCompact` predicate until §2.2's Def 3.1
  exists.
- The paper works with quantitative algebras over a **fuzzy relation**
  `d : A×A → [0,1]`, not assumed a metric; nothing in the current gap list
  is metric-specific, so this is already handled correctly (`FuzzyRelation.v`
  never assumes symmetry/triangle inequality) — noted here only to confirm
  it is *not* an additional gap.

## 3. Milestone plan

Ordered so each milestone is buildable and checkable on its own, and so that
later milestones reuse earlier ones rather than duplicating proof effort.
"Optional" milestones can be skipped without blocking a "faithfully
formalizes the paper's main line of results" claim.

### M1 — Lift the `finType` results to arbitrary carriers *(§2.1)*

**Status: done for the completeness direction (Prop 4.10, Cor 4.13); the
soundness direction (Cor 4.7) turned out not to be a thin corollary of the
same transport and is re-scoped below, with the reason.**

No new distribution type and no changes to `KantorovichCompactness.v`'s
compactness argument — the existing `finType` theorems are reused as a
black box, via a thin transport layer:

1. **Done.** `frel_derives_embed` in `FRelDeduction.v`: given `X, Y :
   fuzzy_space R` and an *isometric* embedding `incl : fcarrier X ->
   fcarrier Y` (i.e. `frel Y (incl x) (incl x') = frel X x x'`), derivability
   of `subst_judgement (Var \o incl) phi` in context `Y` follows from
   derivability of `phi` in context `X`, for both `FRelFinite` and
   `FRelFull` modes. Proof: `FD_Subst` with `sigma := Var \o incl`, whose
   side conditions discharge by `FD_UseVariables` + the isometry hypothesis.
   In the actual use (below) the isometry is not an extra proof obligation
   at the call site: it holds definitionally (`erefl`), because `X`'s
   relation is literally *defined* as the pullback of `Y`'s along `incl`.
   (`ica_finite_eqj_reambient` in `BarycentricNormalization.v` is the same
   idea specialized to `incl = id` between two metrics on the same carrier;
   `frel_derives_embed` generalizes it to a genuine sub-carrier embedding.)
2. **Done.** `term_vars` (`BarycentricNormalization.v`) retyped from `{set
   X}` for `X : finType` to `{fset X}` for `X : choiceType` — the
   definition itself didn't change, only the ambient finiteness assumption.
   `B := term_vars s `|` term_vars t` (now named `gen_vars s t`) is a `{fset
   A}` for an *arbitrary* `A : choiceType`, and `{fset A}` values coerce to
   their own `finType` directly (the same idiom `fsum` in
   `ProbabilityDistribution.v` already exploits — not `KantorovichProperties.v`
   as originally guessed above), so `gen_vars s t` is immediately usable as
   the `finType` the existing Kantorovich machinery expects. Two downstream
   lemmas (`term_distribution_support`, `term_distribution_support_neq0`)
   were restated pointwise (`x \in ... = x \in ...`) rather than as literal
   `{set}`/`{fset}` equalities, since the two set types no longer coincide.
3. **Superseded — see the correction below.** The originally-planned
   `K(d_A)(μ,ν) = K(d_A|_B)(μ,ν)` restriction lemma is not what the
   completeness direction actually needed; what it needed instead is
   `subst_term_eq_on` (a `subst_term` congruence: substitutions agreeing on
   every variable a term mentions produce the same result) plus
   `gen_transport`/`s_B_transport`/`t_B_transport` (reindexing into
   `gen_vars s t` and back via `fsval` is the identity on `s`/`t`). Both are
   proved in `BarycentricNormalization.v`. The support-restriction fact
   *is* still exactly what Cor 4.7 needs — see below.
4. **Done**, for Prop 4.10 and Cor 4.13. `ica_completeness_gen` and
   `ica_finite_completeness_gen` (`BarycentricNormalization.v`) take `A :
   choiceType`, `d : A -> A -> R`, terms `s t : term ica_signature A`, and
   a Kantorovich hypothesis stated over `gen_vars s t` (the canonical finite
   witness set, coerced to a `finType`); they conclude `derives_full`/
   `derives_fin` for the judgement `QEqJ eps s t` at the *full* context `A`.
   Proof: solve the existing finType theorem
   (`ica_completeness`/`ica_finite_completeness`) at `gen_vars s t`, then
   `frel_derives_embed` lifts the resulting derivation to `A`, and
   `s_B_transport`/`t_B_transport` confirm the lifted judgement is literally
   `QEqJ eps s t`, not merely something equivalent to it.

**Correction to the plan above — Cor 4.7 does not generalize this way.**
The completeness direction only needs to *produce* a derivation over `A`
from a fact about `gen_vars s t`, which `frel_derives_embed` does with no
semantic content beyond isometry-by-construction. Cor 4.7 runs the other
way: from `derives_full`/`derives_fin` over the *full* context `A`, conclude
a Kantorovich bound. That requires invoking `derives_full_sound`/
`derives_fin_sound` at an actual **model with carrier `A`**, which
(`kantorovich_algebra` being built on `fdist R X` for `X : finType`) does
not exist for infinite `A` without first building `D(A)`, the type of
finitely-supported distributions over an arbitrary `choiceType`, with
`K(d_A) : D(A) -> D(A) -> R` a genuine binary operation on it. There is no
way around this via a fixed reindexing of `A` into a finite witness set `B`:
`derives_full_sound` needs an `interpretation` (`A -> fdist R B`) that is
nonexpansive at *every* pair of `A`, and collapsing two points of `A \ B` to
a shared image forces the model to assign them Kantorovich-distance `0`
regardless of their actual `d`-distance — unsound as soon as `d` is positive
on some pair outside `B`. So the originally-planned step 3 (`K(d_A)(μ,ν) =
K(d_A|_B)(μ,ν)` whenever `supp(μ) ∪ supp(ν) ⊆ B`) was real and necessary,
just for the *other* direction than this milestone's step 4 turned out to
need: it is exactly the well-definedness fact that would make `K(d_A)`,
once `D(A)` exists, independent of which finite witness set computes it.
Building `D(A)` generically is a genuine new piece of mathematics (a
finitely-supported-distribution type over a bare `choiceType`, its own
convex-mixture/support/coupling infrastructure, and this well-definedness
lemma) rather than a thin corollary of what's already proved, so Cor 4.7's
arbitrary-carrier version is left open as its own milestone rather than
folded into M1.

### M1b — `D(A)` and Cor 4.7 for arbitrary carriers *(§2.1, done)*

**Status: done.** `D(A)` is `gdist R A` (`GeneralDistribution.v`): a
mass function `A -> R`, packaged as a `{fsfun A -> R with 0}` (`finmap`'s
finitely-supported functions) together with proofs that it is nonnegative
and sums to `1` over its own (necessarily finite) support. Built on top of
it:

- `gdirac`/`gdist_restrict`: the point mass at `x : A`, and the restriction
  of a `gdist` to any finite `B : {fset A}` containing its support, as a
  genuine `fdist R B` (`B`'s own `finType` coercion) — so every already-proved
  `fdist`/`kantorovich_lifting` fact becomes available the moment a
  sufficient finite witness set is fixed.
- `push_fdist`/`coupling_push`/`coupling_pullback` and the transport theorem
  `kantorovich_lifting_push`: for an *injective* `f : Y -> X` between
  finTypes with `d (f y1) (f y2) = d0 y1 y2`, the Kantorovich lifting of `d`
  on the pushed-forward distributions equals the lifting of `d0` on the
  originals. Proved via the "coupling support ⊆ product of marginal
  supports" fact flagged in the M1 correction note above (`coupling_support`,
  `coupling_support2`), used to push a `Y`-coupling forward (zero off the
  image, no content needed) and pull an `X`-coupling of the pushed
  distributions back (needs the support fact, since such a coupling's mass
  is automatically confined to the image).
- `gdist_kantorovich_widen`/`gkantorovich_restrict`: specializing the
  transport theorem to `fincl : B -> B'` (`finmap`'s inclusion of nested
  `{fset A}`s) gives exactly the well-definedness fact the M1 correction
  note identified as missing: the Kantorovich lifting computed by
  restricting to *any* finite `B ⊇ supp(μ) ∪ supp(ν)` is independent of the
  choice of `B`. `gkantorovich : (A -> A -> R) -> gdist R A -> gdist R A ->
  R` is then defined via the canonical witness `B := supp(μ) ∪ supp(ν)`, and
  `gkantorovich_restrict` re-expresses it at any larger `B` on demand.

`ICAGeneralSoundness.v` builds the arbitrary-carrier Kantorovich model on
top of this: `gconv` (convex combination of `gdist`s, pointwise via
`weighted_sum`, algebraic laws — idempotence/skew-commutativity/
skew-associativity — transported from the finType case via `gdist_ext` +
`gconvE`, no coupling machinery needed for these); `gkantorovich_ops`/
`g_kantorovich_algebra` (the `FuzzyAlgebra` with carrier `gdist R A`);
`gkantorovich_convex_mixture` (the interpolation-axiom bound, obtained by
restricting all four distributions and both mixtures to their common
four-way witness set via `gkantorovich_restrict` and then invoking the
already-proved finType `kantorovich_convex_mixture`); `gkantorovich_models_ica`
(Prop 4.6 for `D(A)`); and `gdirac_interpretation` (Prop 4.5 for `D(A)`,
via `gkantorovich_restrict` at `B := {x,y}` and the upstream
`kantorovich_dirac_le`). Composing with `derives_full_sound`/
`derives_fin_sound` (exactly as `ICAKantorovichSoundness.v` does for the
finType case) gives Cor 4.7 itself, now for an arbitrary `choiceType`
carrier: `g_kantorovich_soundness`, `g_kantorovich_eq_soundness`,
`g_kantorovich_soundness_fin`.

Combined with M1's completeness direction, this closes the
arbitrary-carrier version of Thm 4.14 (mod M2's bookkeeping — see below) and
Cor 4.11: soundness and completeness, in both the equational and
quantitative directions, both possibly-infinitary and finitary, are now
available for `𝕀ℂ𝔸` over any `choiceType` carrier, not just `finType`.
Machine-checked against the same axiom baseline the rest of the repo
already depends on (`propositional_extensionality`,
`functional_extensionality_dep`, `constructive_indefinite_description`,
all from `mathcomp-analysis`'s `boolp.v` via `all_classical`) — no new
axioms.

### M2 — Assemble Theorem 4.14 and Corollary 4.11 *(§2.4, low effort)*

1. State and prove `ica_compactness` (Thm 4.14): a single theorem taking a
   quantitative equation `φ` and `𝕀ℂ𝔸 ⊨ φ` (or `derives_full`), concluding
   `derives_fin`, by case-splitting into the existing `EqJ`/`QEqJ` proofs.
2. Define a `free_algebra`/`is_free` notion (or reuse `FuzzyAlgebra` plus a
   universal-property statement) and state Corollary 4.11 as the resulting
   isomorphism, reusing `term_distribution_correctness` (both directions)
   and `ica_completeness`/`ica_finite_completeness`.

Independent of M1/M1b for the finite-carrier version. The *arbitrary-carrier*
version of Thm 4.14's `QEqJ` case needs both directions over `A`: soundness
(`g_kantorovich_soundness`, from M1b) and completeness
(`ica_completeness_gen`, from M1) — both now done, so this milestone's
remaining work is purely the bookkeeping of assembling them (and the `EqJ`
case, similarly using `g_kantorovich_eq_soundness` + the completeness-side
`EqJ` facts) into the single `is_compact_theory`-shaped statement, which
also needs M3's `is_compact_theory` definition to state in that form.

### M3 — §3's general framework *(§2.2, independent, good warm-up)*

1. Define `is_compact_theory` (Def 3.1) generically over `sig`/`E`, as a
   `Prop` about `frel_derives`/semantic consequence.
2. Prove Prop 3.3 and Prop 3.4 as direct consequences of the definition
   (Prop 3.4 essentially restates Birkhoff completeness, likely provable by
   reusing/adapting `derives_fin_to_full`-style reasoning already present).
3. Prove Prop 3.5 (pseudometric theory is not compact) by constructing the
   witness relational structure from the paper's proof directly.
4. Retrofit M2's `ica_compactness` to be stated as `is_compact_theory
   ica_theory` once this milestone lands, tying §3's abstraction to §4's
   instance the way the paper does.

Can run in parallel with M1 — touches none of the same files.

### M4 — §5 general theory + standard-mean sanity check *(§2.3, depends on M1)*

1. Define `K_lift` parametrized by an abstract `⊕_p` (Def 5.1) and the
   theory `ica_theory_gen` parametrized the same way (Def 5.2), generalizing
   `ICA.v`'s hard-coded `weighted_sum` interpolation bound.
2. State Thm 5.3's three hypotheses on `⊕_p` as a record/typeclass, and
   redo the §4 proof chain (Prop 4.6 → Cor 4.13) abstracted over it —
   ideally as a functor-style refactor of `ICAKantorovichSoundness.v` +
   `BarycentricNormalization.v` so §4's existing proofs become the `⊕_p =
   weighted_sum` instance of the generalized statement, rather than
   duplicated code.
3. Sanity-check by re-deriving §4's own results as the first instance
   (`⊕_p x y = weighted_sum p x y`), confirming the abstraction is not
   over- or under-specified before spending effort on the harder instances
   below.

This milestone's proof *content* is mostly "re-run M1+§4 one level more
abstractly," so its cost is dominated by how cleanly M1 generalizes rather
than by new mathematics.

### M5 — §5 instances *(§2.3, depends on M4; can be split/parallelized per instance)*

1. `⊕_p x y = max{x,y}` (Hausdorff-flavored lifting): prove the three Thm
   5.3 hypotheses; optimal-coupling existence should follow the same
   compactness-of-a-continuous-function-on-a-compact-set pattern as Prop
   4.12.
2. `⊕_p x y = (p·xᵏ + (1-p)·yᵏ)^{1/k}` for fixed `k ≥ 1` (`k`-Wasserstein):
   same shape as (1), with more numeric side-conditions.
3. *(optional, harder)* `⊕_p x y = xᵖ·y^{1-p}` (log-probabilities): same
   shape, arithmetic-heavier due to the `log`/`exp` convention at `0`.
4. *(optional, hardest, paper explicitly flags this as needing more than
   Prop 4.12's argument)* the `∞`-Wasserstein case, where the evaluation map
   is only lower semicontinuous, not continuous — needs a genuinely
   different existence-of-minimizer argument (lower-semicontinuous function
   on a compact set attains its infimum) rather than reusing
   `compact_EVT_min`.

Each instance is independent once M4's abstraction exists, so these can be
tackled in any order or split across sessions.

## 4. Suggested order

`M1 → M1b → M2`, with `M3` run any time (no dependencies), then `M4 → M5`
once `M1`/`M1b` are in. If the goal is "cover the paper's headline theorem
faithfully" rather than "cover every numbered result," `M1 + M1b + M2`
alone already closes the main gap; `M3`–`M5` are what separates that from a
complete formalization of the paper as published.

**Update:** M1 (Prop 4.10, Cor 4.13 — completeness) and M1b (`D(A)`, Cor
4.7 — soundness) are both done. Together they give the arbitrary-carrier
soundness+completeness pair the paper's Thm 4.14/Cor 4.11 rest on; what
remains of M2 is purely assembling those two already-proved halves (plus
M3's `is_compact_theory` definition) into the single stated theorems, not
further mathematical content.
