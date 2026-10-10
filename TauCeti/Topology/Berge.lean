/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import TauCeti.Topology.ApproxMinimizer
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-! # Upper hemicontinuity of the argmin correspondence over a fixed compact set

This is the *fixed-constraint case* of Berge's maximum theorem: the feasible set
`K` does not vary with the parameter `p`.  (The classical Berge theorem allows a
parameter-varying constraint correspondence; that more general case is not
formalized here.)

Let `g : P → X → ℝ` be jointly continuous and let `K ⊆ X` be a fixed nonempty
compact set.  Consider the parametric minimization of `g p` over `K`, with
argmin correspondence
`M p = {x ∈ K | IsMinOn (g p) K x}`.
In this fixed-constraint setting, the value function `p ↦ ⨅ x ∈ K, g p x` is
continuous and the correspondence `M` is upper hemicontinuous (and compact-valued
and nonempty).

Mathlib has the hemicontinuity *definitions* (`Mathlib/Topology/Semicontinuity/
Hemicontinuity.lean`) and the extreme-value theorem (`IsCompact.exists_isMinOn`),
but no Berge theorem.  This file supplies the upper-hemicontinuity half in two
usable forms, building on the approximate-minimizer stability engine
`TauCeti.exists_subseq_tendsto_isMinOn_of_approxMinOn`:

* `tendsto_eval_sub_of_isCompact` — along a convergent parameter sequence
  `p k → p₀`, the evaluation difference `g (p k) (x k) − g p₀ (x k)` vanishes
  uniformly over points `x k` staying in the compact `K` (a uniform-convergence-
  on-compacts fact, here in the sequential form actually needed).
* `tendsto_subseq_isMinOn_of_isMinOn` — **sequential upper hemicontinuity**: any
  sequence of constrained minimizers `x k ∈ argmin (g (p k))` for `p k → p₀` has
  a subsequence converging to a constrained minimizer of `g p₀`.  This is the
  closed-graph form of Berge's theorem.
* `upperHemicontinuousAt_isMinOn` — the same conclusion phrased through Mathlib's
  own `UpperHemicontinuousAt` predicate for the argmin correspondence
  `p ↦ {x ∈ K | IsMinOn (g p) K x}` (requires `X` Hausdorff so the compact `K` is
  closed and limits of feasible points stay feasible).
* `exists_modulus_isMinOn_family` / `exists_modulus_isMinOn` — the **uniform
  `ε`–`δ` modulus** form (metric `P`): for every `ε > 0` there is a `δ > 0` such
  that whenever `dist p p₀ ≤ δ`, *every* minimizer of `g p` over `K` is `ε`-close
  (in the ambient metric, or in any finite family of continuous invariants) to
  *some* minimizer of `g p₀` over `K`.  The family form lets closeness be measured
  by a finite family of continuous invariants rather than the ambient metric,
  which is useful when minimizers are only determined up to a symmetry group.

## Main results

* `TauCeti.tendsto_subseq_isMinOn_of_isMinOn`
* `TauCeti.upperHemicontinuousAt_isMinOn`
* `TauCeti.continuous_iInf_of_isCompact` — value-function continuity.
* `TauCeti.exists_modulus_isMinOn_family` / `TauCeti.exists_modulus_isMinOn`

## Staging note

Staged for Tau Ceti, roadmap topic T22.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
the Berge maximum theorem (upper hemicontinuity of the
parametric argmin correspondence over a fixed compact feasible set).
Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]); golfed a terminal
`simp only [Function.comp_apply]; exact …` to `simpa using …` (rule 1.15).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `1ca2679`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Intended Mathlib home: the Berge maximum theorem (upper hemicontinuity of the.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (rule 2 of
  `scripts/check_dependency_layers.py`); this module imports Mathlib only.
-/

public section

/-!
### Provenance

Moved from the retired `ForMathlib` staging tree into `ForTauCeti/Topology/`.
`ForMathlib` to `TauCeti` to match the destination package; declaration names,
statements and proofs are unchanged.

**FM-RETIRE was worked twice, and the two versions disagreed on the namespace.**
The `main` version (`c85510d6`) kept `namespace ForMathlib` here, reasoning that
`Challenge/**/Conformance.lean` is immutable so its `ForMathlib.*` pins could not
be re-issued.  Reconciled on merge in favour of `TauCeti`, because the pins are
not what immutability protects: `AGENTS.md`'s comparator rule forbids *filling the
proof placeholders*, and its rename protocol explicitly requires a dedicated rename pass to
update `Challenge/` and `comparator/*.json`, which is what was done — the three
Berge names in `comparator/challenge-berge.json`, the `#print axioms` lines in
`Challenge/Berge/Leaderboard.lean`, and the restated statements in
the paired `Conformance.lean` all read `TauCeti.*`.  Leaving `ForMathlib.*`
declarations inside `ForTauCeti` would also contradict the package rule that its
declarations live in their final `TauCeti.*` namespaces (`lakefile.toml`).
-/

namespace TauCeti

open Filter Topology Set

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
  [FirstCountableTopology X]

/-- **Sequential uniform convergence on a compact set from joint continuity.**
If `g : P → X → ℝ` is jointly continuous, `p k → p₀`, and the points `x k` stay in
a compact set `K`, then the evaluation difference `g (p k) (x k) − g p₀ (x k)`
tends to `0`.  (This is the only consequence of "`g (p k) → g p₀` uniformly on
`K`" needed for Berge; it is proved directly via the subsequence criterion and
sequential compactness, avoiding the compact-open topology.) -/
theorem tendsto_eval_sub_of_isCompact
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {p : ℕ → P} {p₀ : P} (hp : Tendsto p atTop (𝓝 p₀))
    {x : ℕ → X} (hx : ∀ k, x k ∈ K) :
    Tendsto (fun k => g (p k) (x k) - g p₀ (x k)) atTop (𝓝 0) := by
  -- Continuity of `g p₀ = (uncurry g) ∘ (p₀, ·)`.
  have hgp0 : Continuous (g p₀) := hg.comp (continuous_const.prodMk continuous_id)
  -- It suffices to find, in every subsequence, a convergent sub-subsequence.
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  -- `x ∘ ns` lives in `K`; extract a convergent sub-subsequence `x (ns (φ ·)) → a`.
  obtain ⟨a, _ha, φ, hφ_mono, hφ_tendsto⟩ := hK.tendsto_subseq (fun n => hx (ns n))
  refine ⟨φ, ?_⟩
  have hns' : Tendsto (fun n => ns (φ n)) atTop atTop := hns.comp hφ_mono.tendsto_atTop
  have hpns : Tendsto (fun n => p (ns (φ n))) atTop (𝓝 p₀) := hp.comp hns'
  -- Joint continuity along `(p (ns φ n), x (ns φ n)) → (p₀, a)`.
  have h1 : Tendsto (fun n => g (p (ns (φ n))) (x (ns (φ n)))) atTop (𝓝 (g p₀ a)) :=
    (hg.tendsto (p₀, a)).comp (hpns.prodMk_nhds hφ_tendsto)
  -- Continuity in the second argument at the fixed parameter `p₀`.
  have h2 : Tendsto (fun n => g p₀ (x (ns (φ n)))) atTop (𝓝 (g p₀ a)) :=
    (hgp0.tendsto a).comp hφ_tendsto
  simpa using h1.sub h2

/-- **Sequential upper hemicontinuity of the argmin correspondence over a fixed
compact set (the fixed-constraint case of Berge's maximum theorem).**
Let `g : P → X → ℝ` be jointly continuous and `K` a fixed compact set.  If
`p k → p₀` and each `x k` minimizes `g (p k)` over `K`, then a subsequence of
`x k` converges to a point `x₀ ∈ K` that minimizes `g p₀` over `K`.

This is the closed-graph form: the argmin correspondence
`p ↦ {x ∈ K | IsMinOn (g p) K x}` has closed graph (equivalently, is upper
hemicontinuous, since `K` is compact). -/
theorem tendsto_subseq_isMinOn_of_isMinOn
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {p : ℕ → P} {p₀ : P} (hp : Tendsto p atTop (𝓝 p₀))
    {x : ℕ → X} (hxK : ∀ k, x k ∈ K)
    (hxmin : ∀ k, IsMinOn (g (p k)) K (x k)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧
      Tendsto (fun t => x (φ t)) atTop (𝓝 x₀) := by
  have hgp0 : Continuous (g p₀) := hg.comp (continuous_const.prodMk continuous_id)
  -- The evaluation difference vanishes (uniform convergence on `K`).
  have hsub : Tendsto (fun k => g (p k) (x k) - g p₀ (x k)) atTop (𝓝 0) :=
    tendsto_eval_sub_of_isCompact hK hg hp hxK
  -- `x k` approximately minimizes `g p₀` on `K`, with error
  -- `ε y k = (g (p k) y − g p₀ y) + (g p₀ (x k) − g (p k) (x k))`.
  refine exists_subseq_tendsto_isMinOn_of_approxMinOn hK hgp0 hxK
    (ε := fun y k => (g (p k) y - g p₀ y) + (g p₀ (x k) - g (p k) (x k))) ?_ ?_
  · -- the error tends to `0` for each fixed comparison point `y ∈ K`
    intro y _hy
    have ha : Tendsto (fun k => g (p k) y - g p₀ y) atTop (𝓝 0) := by
      have hy' : Tendsto (fun k => g (p k) y) atTop (𝓝 (g p₀ y)) :=
        (hg.tendsto (p₀, y)).comp (hp.prodMk_nhds tendsto_const_nhds)
      have hc : Tendsto (fun _ : ℕ => g p₀ y) atTop (𝓝 (g p₀ y)) := tendsto_const_nhds
      simpa using hy'.sub hc
    have hb : Tendsto (fun k => g p₀ (x k) - g (p k) (x k)) atTop (𝓝 0) := by
      simpa [neg_sub] using hsub.neg
    simpa using ha.add hb
  · -- the approximate-minimization inequality, from `IsMinOn (g (p k)) K`
    intro y hy k
    have hmin : g (p k) (x k) ≤ g (p k) y := (isMinOn_iff.mp (hxmin k)) y hy
    linarith

/-- **Uniform closeness on a compact set, without first countability.**

For every `ε > 0`, `g p` is uniformly within `ε` of `g p₀` on `K` once `p` is close enough to
`p₀`.  Proved from the tube lemma `IsCompact.eventually_forall_of_forall_eventually` rather
than from sequential compactness, which is what keeps `X` free of
`[FirstCountableTopology]`. -/
theorem eventually_forall_abs_sub_lt_of_isCompact {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g)) (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in 𝓝 p₀, ∀ x ∈ K, |g p x - g p₀ x| < ε := by
  refine hK.eventually_forall_of_forall_eventually fun x₀ _ => ?_
  have hcont : ContinuousAt (fun z : P × X => |g z.1 z.2 - g p₀ z.2|) (p₀, x₀) :=
    ((hg.continuousAt).sub
      ((hg.comp (continuous_const.prodMk continuous_snd)).continuousAt)).abs
  have hzero : |g p₀ x₀ - g p₀ x₀| = 0 := by simp
  exact hcont (by simpa [hzero] using Iio_mem_nhds hε)

/-- **Upper hemicontinuity of the argmin correspondence, with no countability hypothesis.**

The same conclusion as `upperHemicontinuousAt_isMinOn` below, but free of
`[FirstCountableTopology X]` and `[(𝓝 p₀).IsCountablyGenerated]`: those are artifacts of
routing the proof through `UpperHemicontinuousAt.of_sequences`, not features of the
mathematics.

The argument is the classical one.  Let `V` be open around the `p₀`-argmin set.  If `K ⊆ V`
there is nothing to do; otherwise `K \ V` is compact and nonempty, and no point of it
minimises `g p₀`, so the minimum of `g p₀` over `K \ V` strictly exceeds its minimum over
`K`.  Take `ε` a third of that gap and move `p` close enough that `g p` is uniformly within
`ε` of `g p₀` on `K`: a minimiser of `g p` outside `V` would then be within `2ε` of the
smaller value, contradicting the `3ε` gap. -/
theorem upperHemicontinuousAt_isMinOn_of_isCompact {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g)) (p₀ : P) :
    UpperHemicontinuousAt (fun p => {x ∈ K | IsMinOn (g p) K x}) p₀ := by
  refine UpperHemicontinuousAt.of_forall_isOpen fun V hV hsub => ?_
  have hcont : ∀ q : P, ContinuousOn (g q) K := fun q =>
    (hg.comp (continuous_const.prodMk continuous_id)).continuousOn
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · filter_upwards with p using fun x hx => absurd hx.1 (Set.notMem_empty x)
  by_cases hKV : K ⊆ V
  · filter_upwards with p using fun x hx => hKV hx.1
  -- the part of `K` outside `V` is compact, nonempty, and misses every `p₀`-minimiser
  have hKVc : IsCompact (K \ V) := hK.diff hV
  have hKVne : (K \ V).Nonempty := by
    obtain ⟨x, hxK, hxV⟩ := Set.not_subset.mp hKV
    exact ⟨x, hxK, hxV⟩
  obtain ⟨x₀, hx₀K, hx₀min⟩ := hK.exists_isMinOn hKne (hcont p₀)
  obtain ⟨y₀, hy₀mem, hy₀min⟩ := hKVc.exists_isMinOn hKVne ((hcont p₀).mono Set.sdiff_subset)
  have hgap : g p₀ x₀ < g p₀ y₀ := by
    rcases lt_or_ge (g p₀ x₀) (g p₀ y₀) with h | h
    · exact h
    · exact absurd (hsub ⟨hy₀mem.1, fun z hz => le_trans h (hx₀min hz)⟩) hy₀mem.2
  set ε := (g p₀ y₀ - g p₀ x₀) / 3 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  filter_upwards [eventually_forall_abs_sub_lt_of_isCompact hK hg p₀ hε] with p hp x hx
  by_contra hxV
  have hxKV : x ∈ K \ V := ⟨hx.1, hxV⟩
  have h1 : g p₀ y₀ ≤ g p₀ x := hy₀min hxKV
  have h2 : |g p x - g p₀ x| < ε := hp x hx.1
  have h3 : |g p x₀ - g p₀ x₀| < ε := hp x₀ hx₀K
  have h4 : g p x ≤ g p x₀ := hx.2 hx₀K
  have e2 := abs_lt.mp h2
  have e3 := abs_lt.mp h3
  have : g p₀ y₀ - g p₀ x₀ < 2 * ε := by linarith
  rw [hεdef] at this
  linarith

/-- **Upper hemicontinuity of the argmin correspondence over a fixed compact set
(the fixed-constraint case of Berge's maximum theorem), via Mathlib's
`UpperHemicontinuousAt`.**
For jointly continuous `g` and compact `K`, the argmin correspondence
`p ↦ {x ∈ K | IsMinOn (g p) K x}` is upper hemicontinuous at `p₀` in the sense of
`Mathlib.Topology.Semicontinuity.Hemicontinuity`.

This lands the closed-graph statement on Mathlib's own predicate.  It carries no
countability or separation hypothesis: the earlier route through
`UpperHemicontinuousAt.of_sequences` needed `[FirstCountableTopology X]`,
`[T2Space X]` and `[(𝓝 p₀).IsCountablyGenerated]`, and
`upperHemicontinuousAt_isMinOn_of_isCompact` does without them. -/
theorem upperHemicontinuousAt_isMinOn {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g)) (p₀ : P) :
    UpperHemicontinuousAt (fun p => {x ∈ K | IsMinOn (g p) K x}) p₀ :=
  upperHemicontinuousAt_isMinOn_of_isCompact hK hg p₀
/-- **Value-function continuity over a fixed compact set (the value-function half
of the fixed-constraint case of Berge's maximum theorem).**
For jointly continuous `g`, a fixed nonempty compact `K`, and `P` first-countable,
the value function `p ↦ ⨅ x ∈ K, g p x` is continuous.

This is the second half of the fixed-constraint statement (alongside the upper
hemicontinuity of the argmin correspondence above).  The proof is the standard
squeeze: with `xₖ` a
minimizer of `g (p k)` and `x₀` a minimizer of `g p₀`,
`V p₀ + (g (p k) xₖ − g p₀ xₖ) ≤ V (p k) ≤ g (p k) x₀`,
where the lower bound tends to `V p₀` via `tendsto_eval_sub_of_isCompact` and the
upper bound via joint continuity at the fixed `x₀`. -/
theorem continuous_iInf_of_isCompact [FirstCountableTopology P]
    {K : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g)) :
    Continuous (fun p => ⨅ x : ↥K, g p ↑x) := by
  have : Nonempty ↥K := hKne.to_subtype
  -- `g q` is continuous for each parameter, and bounded below on the compact `K`.
  have hgcont : ∀ q : P, Continuous (g q) :=
    fun q => hg.comp (continuous_const.prodMk continuous_id)
  have hbdd : ∀ q : P, BddBelow (Set.range fun x : ↥K => g q ↑x) := by
    intro q
    refine (hK.bddBelow_image (hgcont q).continuousOn).mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨↑x, x.2, rfl⟩
  -- The value `⨅ x ∈ K, g q x` is a lower bound, attained at any minimizer.
  have hVle : ∀ (q : P) (y : X), y ∈ K → (⨅ x : ↥K, g q ↑x) ≤ g q y :=
    fun q y hy => ciInf_le (hbdd q) ⟨y, hy⟩
  have hval : ∀ (q : P) (xq : X), xq ∈ K → IsMinOn (g q) K xq →
      (⨅ x : ↥K, g q ↑x) = g q xq := by
    intro q xq hxqK hmin
    exact le_antisymm (hVle q xq hxqK) (le_ciInf fun x => (isMinOn_iff.mp hmin) ↑x x.2)
  -- Sequential continuity (`P` is a sequential space).
  rw [continuous_iff_seqContinuous]
  intro p p₀ hp
  obtain ⟨x₀, hx₀K, hx₀min⟩ := hK.exists_isMinOn hKne (hgcont p₀).continuousOn
  choose xseq hxseqK hxseqmin using fun k => hK.exists_isMinOn hKne (hgcont (p k)).continuousOn
  have hVp0 : (⨅ x : ↥K, g p₀ ↑x) = g p₀ x₀ := hval p₀ x₀ hx₀K hx₀min
  -- Upper bound: `V (p k) ≤ g (p k) x₀ → g p₀ x₀ = V p₀`.
  have hi : Tendsto (fun k => g (p k) x₀) atTop (𝓝 (⨅ x : ↥K, g p₀ ↑x)) := by
    rw [hVp0]
    exact (hg.tendsto (p₀, x₀)).comp (hp.prodMk_nhds tendsto_const_nhds)
  -- Lower bound: `V p₀ + (g (p k) xₖ − g p₀ xₖ) ≤ V (p k)`, with the increment → 0.
  have hlo : Tendsto (fun k => (⨅ x : ↥K, g p₀ ↑x) +
      (g (p k) (xseq k) - g p₀ (xseq k))) atTop (𝓝 (⨅ x : ↥K, g p₀ ↑x)) := by
    have := tendsto_eval_sub_of_isCompact hK hg hp hxseqK
    simpa using tendsto_const_nhds.add this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hi (fun k => ?_) (fun k => ?_)
  · -- `V p₀ + (g (p k) xₖ − g p₀ xₖ) ≤ V (p k) = g (p k) xₖ`
    simp only [Function.comp_apply]
    have hV : (⨅ x : ↥K, g (p k) ↑x) = g (p k) (xseq k) :=
      hval (p k) (xseq k) (hxseqK k) (hxseqmin k)
    have := hVle p₀ (xseq k) (hxseqK k)
    rw [hV]; linarith
  · -- `V (p k) ≤ g (p k) x₀`
    simpa using hVle (p k) x₀ hx₀K

/-- **Uniform `ε`–`δ` modulus form over a fixed compact set (the fixed-constraint
case of Berge's maximum theorem).**
With `P` a (pseudo)metric space, `g` jointly continuous, `K` a fixed compact set,
and closeness measured by a *finite family* of jointly-continuous functionals
`ρ i : X → X → ℝ` with `ρ i x x = 0` (a family of continuous invariants, not
necessarily a metric): for every `ε > 0` there is `δ > 0` such that whenever
`dist p p₀ ≤ δ`, *every* feasible minimizer `x` of `g p` over `K` (i.e. `x ∈ K`
with `IsMinOn (g p) K x`) is `ρ`-within `ε` of *some* feasible minimizer `x₀` of
`g p₀` over `K` (`∀ i, ρ i x x₀ < ε`).

The `δ` depends only on `p₀` and `ε` (a genuine modulus of upper hemicontinuity),
which lets one avoid measurable selection of minimizers.  The closeness family
captures *invariant* closeness measures for which the ambient metric is not the
right notion — for instance when minimizers are only determined up to a symmetry
group, so that closeness should be measured by group-invariant functionals. -/
theorem exists_modulus_isMinOn_family {P X : Type*} [PseudoMetricSpace P]
    [TopologicalSpace X] [FirstCountableTopology X]
    {ι : Type*} [Finite ι]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {ρ : ι → X → X → ℝ} (hρ : ∀ i, Continuous (Function.uncurry (ρ i)))
    (hρ0 : ∀ i x, ρ i x x = 0)
    (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : P) (x : X), x ∈ K → IsMinOn (g p) K x → dist p p₀ ≤ δ →
      ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧ ∀ i, ρ i x x₀ < ε := by
  by_contra hcon
  push Not at hcon
  -- Counterexamples at `δ = 1/(k+1)`: feasible minimizers `x k` for parameters
  -- `p k → p₀`, none `ρ`-`ε`-close (in some coordinate) to any minimizer of `g p₀`.
  have hex := fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  choose p x hxK hxmin hpδ hbad using hex
  -- The parameters converge to `p₀` (squeeze `0 ≤ dist (p k) p₀ ≤ 1/(k+1)`).
  have hp : Tendsto p atTop (𝓝 p₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun k => dist_nonneg) hpδ tendsto_one_div_add_atTop_nhds_zero_nat
  -- Berge: a subsequence of the minimizers converges to a minimizer of `g p₀`.
  obtain ⟨φ, _hφ, x₀, hx₀K, hx₀min, htend⟩ :=
    tendsto_subseq_isMinOn_of_isMinOn hK hg hp hxK hxmin
  -- Each closeness coordinate is eventually `< ε` along the subsequence (`ρ i · x₀`
  -- is continuous and vanishes at `x₀`); over the finite family, simultaneously so.
  have hev : ∀ i, ∀ᶠ t in atTop, ρ i (x (φ t)) x₀ < ε := by
    intro i
    have hcont : Tendsto (fun t => ρ i (x (φ t)) x₀) atTop (𝓝 0) := by
      have := (hρ i).tendsto (x₀, x₀) |>.comp (htend.prodMk_nhds tendsto_const_nhds)
      rwa [show Function.uncurry (ρ i) (x₀, x₀) = 0 from hρ0 i x₀] at this
    exact hcont.eventually (eventually_lt_nhds hε)
  obtain ⟨t, ht⟩ := (eventually_all.mpr hev).exists
  -- ... contradicting that some coordinate of `x (φ t)` stays `≥ ε`-far.
  obtain ⟨i, hi⟩ := hbad (φ t) x₀ hx₀K hx₀min
  exact absurd (ht i) (not_lt.mpr hi)

/-- **Uniform `ε`–`δ` modulus form over a fixed compact set, metric closeness
(the fixed-constraint case of Berge's maximum theorem).**
The single-functional special case of `exists_modulus_isMinOn_family` where
closeness is the ambient metric `dist`: for every `ε > 0` there is `δ > 0` with,
for every feasible minimizer `x` of `g p` over `K` with `dist p p₀ ≤ δ`, some
feasible minimizer `x₀` of `g p₀` over `K` with `dist x x₀ < ε`. -/
theorem exists_modulus_isMinOn {P X : Type*} [PseudoMetricSpace P] [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (p₀ : P) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : P) (x : X), x ∈ K → IsMinOn (g p) K x → dist p p₀ ≤ δ →
      ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧ dist x x₀ < ε := by
  obtain ⟨δ, hδ, h⟩ := exists_modulus_isMinOn_family hK hg
    (ρ := fun _ : Unit => dist) (fun _ => continuous_dist) (fun _ => dist_self) p₀ hε
  refine ⟨δ, hδ, fun p x hxK hxmin hpd => ?_⟩
  obtain ⟨x₀, hx₀K, hx₀min, hclose⟩ := h p x hxK hxmin hpd
  exact ⟨x₀, hx₀K, hx₀min, hclose ()⟩

/-! ### Varying constraints: the lower-hemicontinuous half

The theorems above fix the feasible set `K`.  Berge's theorem allows `K` to vary
with the parameter, and the two bounds on the value function then come from
*different* hypotheses: lower hemicontinuity of `K` gives the upper bound, upper
hemicontinuity together with compactness gives the lower one.

This section supplies the first.  The content is that a feasible point at `p₀`
can be approximately tracked at nearby parameters -- which is exactly what lower
hemicontinuity says -- and joint continuity then transfers the value.
-/

/-- **Feasible points can be tracked, with their values.**

If `K` is lower hemicontinuous at `p₀`, `g` is jointly continuous, and `y` is
feasible at `p₀`, then for every `ε > 0` all nearby parameters admit a feasible
point whose value beats `g p₀ y + ε`.

Lower hemicontinuity alone gives a nearby *feasible* point; joint continuity is
what makes its *value* close.  Neither hypothesis can be dropped: without the
first the nearby constraint sets could avoid a neighbourhood of `y` entirely,
and without the second a feasible point close to `y` need not have a close
value. -/
theorem eventually_exists_mem_lt_of_lowerHemicontinuousAt
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {K : P → Set X} {p₀ : P} (hKl : LowerHemicontinuousAt K p₀)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    {y : X} (hy : y ∈ K p₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in nhds p₀, ∃ x ∈ K p, g p x < g p₀ y + ε := by
  -- The sublevel set of the jointly continuous `g` is open and contains `(p₀, y)`.
  set W : Set (P × X) := {qx | g qx.1 qx.2 < g p₀ y + ε} with hW
  have hWopen : IsOpen W := isOpen_lt hg continuous_const
  have hmemW : (p₀, y) ∈ W := by simp [hW, hε]
  -- Split it into a parameter neighbourhood and a state neighbourhood.
  obtain ⟨N, u, hNopen, huopen, hpN, hyu, hsub⟩ :=
    isOpen_prod_iff.mp hWopen p₀ y hmemW
  -- Lower hemicontinuity tracks `y` into `u` at nearby parameters.
  have htrack : ∀ᶠ p in nhds p₀, (K p ∩ u).Nonempty :=
    (lowerHemicontinuousAt_iff.mp hKl) u huopen ⟨y, hy, hyu⟩
  filter_upwards [htrack, hNopen.mem_nhds hpN] with p hp hpmem
  obtain ⟨x, hxK, hxu⟩ := hp
  exact ⟨x, hxK, hsub (Set.mk_mem_prod hpmem hxu)⟩

/-- **The upper bound on the value function**, from lower hemicontinuity.

`V p = ⨅ x ∈ K p, g p x` eventually beats `V p₀ + ε`.  This is the half of
Berge's value theorem that lower hemicontinuity buys; the matching lower bound
`V p₀ ≤ liminf V p` is where upper hemicontinuity and compactness of the
constraint sets do their work, and is not proved here.

The infimum is taken over the subtype `↥(K p)`, so a nonemptiness hypothesis is
needed for it to be meaningful, and boundedness below for `ciInf_le` to apply. -/
theorem eventually_iInf_lt_of_lowerHemicontinuousAt
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {K : P → Set X} {p₀ : P} (hKl : LowerHemicontinuousAt K p₀)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (hbdd : ∀ p, BddBelow (Set.range fun x : ↥(K p) => g p ↑x))
    {y : X} (hy : y ∈ K p₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in nhds p₀, (⨅ x : ↥(K p), g p ↑x) < g p₀ y + ε := by
  filter_upwards [eventually_exists_mem_lt_of_lowerHemicontinuousAt hKl hg hy hε]
    with p hp
  obtain ⟨x, hxK, hxlt⟩ := hp
  exact lt_of_le_of_lt (ciInf_le (hbdd p) ⟨x, hxK⟩) hxlt

/-! ### Varying constraints: the upper-hemicontinuous half

Where lower hemicontinuity above gave the *upper* bound on the value function,
upper hemicontinuity gives the reverse one, and it does so through a single
fact: a limit of feasible points stays feasible.
-/

/-- **Feasibility passes to limits under upper hemicontinuity.**

If `pₖ → p₀`, each `xₖ` is feasible at `pₖ`, and `xₖ → x₀`, then `x₀` is
feasible at `p₀`.

**This is the step that fails without upper hemicontinuity**: nothing otherwise
stops the constraint sets from collapsing away from `x₀` in the limit, and a
minimizer extracted from the `xₖ` would not be a competitor at `p₀`.

The separation hypotheses are genuine rather than artifacts.  `x₀ ∉ K p₀` with
`K p₀` closed gives disjoint opens `U ∋ x₀` and `V ⊇ K p₀`; upper
hemicontinuity puts `K p` inside `V` eventually, while convergence puts `xₖ`
inside `U` eventually, and `xₖ ∈ K pₖ` then contradicts disjointness. -/
theorem mem_of_tendsto_of_upperHemicontinuousAt
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] [RegularSpace X]
    {K : P → Set X} {p₀ : P} (hKu : UpperHemicontinuousAt K p₀)
    (hKclosed : IsClosed (K p₀))
    {p : ℕ → P} (hp : Tendsto p atTop (𝓝 p₀))
    {x : ℕ → X} (hxK : ∀ k, x k ∈ K (p k))
    {x₀ : X} (hx : Tendsto x atTop (𝓝 x₀)) :
    x₀ ∈ K p₀ := by
  by_contra hx₀
  -- Separate the point from the closed constraint set.
  obtain ⟨U, V, hUopen, hVopen, hx₀U, hKV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isClosed (isCompact_singleton (x := x₀)) hKclosed
      (Set.disjoint_singleton_left.mpr hx₀)
  -- Upper hemicontinuity pushes the nearby constraint sets into `V`.
  have hVnhds : V ∈ 𝓝ˢ (K p₀) := hVopen.mem_nhdsSet.mpr hKV
  have hev : ∀ᶠ q in 𝓝 p₀, V ∈ 𝓝ˢ (K q) := (upperHemicontinuousAt_iff.mp hKu) V hVnhds
  have hevk : ∀ᶠ k in atTop, V ∈ 𝓝ˢ (K (p k)) := hp.eventually hev
  -- Convergence puts the points into `U`.
  have hUk : ∀ᶠ k in atTop, x k ∈ U := hx (hUopen.mem_nhds (hx₀U rfl))
  obtain ⟨k, hkV, hkU⟩ := (hevk.and hUk).exists
  exact Set.disjoint_left.mp hUV hkU (subset_of_mem_nhdsSet hkV (hxK k))

/-- **Subsequence extraction for a varying constraint family.**

From feasible points `xₖ ∈ K pₖ` with `pₖ → p₀`, extract a convergent
subsequence whose limit is feasible at `p₀`.

**The local-boundedness hypothesis is what makes this possible and cannot be
weakened to "each `K p` is compact":** a family of individually compact sets can
march off to infinity as `p → p₀`, leaving no compact set to extract from.  A
single compact `C` containing `K p` for all `p` near `p₀` is the standard Berge
assumption and rules exactly that out.

Given it, the two hemicontinuity lanes supply the rest: compactness of `C`
produces the convergent subsequence, and
`mem_of_tendsto_of_upperHemicontinuousAt` returns its limit to `K p₀`. -/
theorem exists_subseq_tendsto_mem_of_upperHemicontinuousAt
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] [RegularSpace X]
    [FirstCountableTopology X]
    {K : P → Set X} {p₀ : P} (hKu : UpperHemicontinuousAt K p₀)
    (hKclosed : IsClosed (K p₀))
    {C : Set X} (hC : IsCompact C) (hKC : ∀ᶠ q in 𝓝 p₀, K q ⊆ C)
    {p : ℕ → P} (hp : Tendsto p atTop (𝓝 p₀))
    {x : ℕ → X} (hxK : ∀ k, x k ∈ K (p k)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x₀ ∈ K p₀,
      Tendsto (fun t => x (φ t)) atTop (𝓝 x₀) := by
  -- Past some index every point lies in the common compact set.
  obtain ⟨N, hN⟩ := (hp.eventually hKC).exists_forall_of_atTop
  -- Shift so that the whole tail is inside `C`, extract there.
  have hmem : ∀ k, x (N + k) ∈ C := fun k => hN (N + k) (Nat.le_add_right N k) (hxK (N + k))
  obtain ⟨x₀, _hx₀C, ψ, hψmono, hψtend⟩ := hC.tendsto_subseq hmem
  refine ⟨fun t => N + ψ t, ?_, x₀, ?_, ?_⟩
  · exact fun a b hab => Nat.add_lt_add_left (hψmono hab) N
  · -- The limit is feasible, by upper hemicontinuity.
    refine mem_of_tendsto_of_upperHemicontinuousAt hKu hKclosed
      (p := fun t => p (N + ψ t)) ?_ (fun t => hxK (N + ψ t)) hψtend
    exact hp.comp (tendsto_atTop_mono (fun t => Nat.le_add_left (ψ t) N)
      hψmono.tendsto_atTop)
  · exact hψtend

/-- **Local boundedness comes free in a locally compact ambient space.**

If `K p₀` is compact and `K` is upper hemicontinuous at `p₀`, then some compact
`C` contains `K p` for every `p` near `p₀`.

This reconciles `exists_subseq_tendsto_mem_of_upperHemicontinuousAt`, which
assumes such a `C`, with the usual statement of Berge's theorem, which assumes
only that each `K p` is compact.  Those are genuinely different hypotheses --
individually compact sets can escape to infinity as `p → p₀` — but the escape
needs a non-locally-compact ambient space, so it cannot happen here.

The proof is the reason upper hemicontinuity is stated with neighbourhoods
rather than with sets: `exists_compact_superset` puts `K p₀` inside the
*interior* of a compact `C`, and that interior is an open set to which upper
hemicontinuity directly applies. -/
theorem exists_isCompact_eventually_subset_of_upperHemicontinuousAt
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X]
    {K : P → Set X} {p₀ : P} (hKu : UpperHemicontinuousAt K p₀)
    (hK₀ : IsCompact (K p₀)) :
    ∃ C : Set X, IsCompact C ∧ ∀ᶠ p in 𝓝 p₀, K p ⊆ C := by
  obtain ⟨C, hCcompact, hsub⟩ := exists_compact_superset hK₀
  refine ⟨C, hCcompact, ?_⟩
  -- `interior C` is open and contains `K p₀`, so it is a neighbourhood of it.
  have hnhds : interior C ∈ 𝓝ˢ (K p₀) := isOpen_interior.mem_nhdsSet.mpr hsub
  filter_upwards [(upperHemicontinuousAt_iff.mp hKu) (interior C) hnhds] with p hp
  exact (subset_of_mem_nhdsSet hp).trans interior_subset

/-- **The extraction, from Berge's own hypotheses.**

`exists_subseq_tendsto_mem_of_upperHemicontinuousAt` with its local-boundedness
assumption discharged by
`exists_isCompact_eventually_subset_of_upperHemicontinuousAt`.  This is the form
the value theorem consumes: compactness of the single set `K p₀`, upper
hemicontinuity, and a locally compact ambient space. -/
theorem exists_subseq_tendsto_mem_of_isCompact
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] [RegularSpace X]
    [T2Space X] [FirstCountableTopology X] [WeaklyLocallyCompactSpace X]
    {K : P → Set X} {p₀ : P} (hKu : UpperHemicontinuousAt K p₀)
    (hK₀ : IsCompact (K p₀))
    {p : ℕ → P} (hp : Tendsto p atTop (𝓝 p₀))
    {x : ℕ → X} (hxK : ∀ k, x k ∈ K (p k)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x₀ ∈ K p₀,
      Tendsto (fun t => x (φ t)) atTop (𝓝 x₀) := by
  obtain ⟨C, hCcompact, hKC⟩ :=
    exists_isCompact_eventually_subset_of_upperHemicontinuousAt hKu hK₀
  exact exists_subseq_tendsto_mem_of_upperHemicontinuousAt hKu hK₀.isClosed
    hCcompact hKC hp hxK

/-- **Upper semicontinuity of the value function under lower hemicontinuity.**

`V p = ⨅ x ∈ K p, g p x` eventually falls below any bound strictly above
`V p₀`.  With the matching lower statement this gives continuity of `V`; the two
halves are *not* symmetric — this one is what lower hemicontinuity buys, and the
other needs upper hemicontinuity and the compactness extraction.

The compactness of `K p₀` is used only to produce a genuine minimizer there, so
that the bound from `eventually_iInf_lt_of_lowerHemicontinuousAt` can be stated
against `V p₀` itself rather than against an approximate value. -/
theorem eventually_iInf_lt_of_lt_iInf
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {K : P → Set X} {p₀ : P} (hKl : LowerHemicontinuousAt K p₀)
    (hK₀ : IsCompact (K p₀)) (hK₀ne : (K p₀).Nonempty)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (hbdd : ∀ p, BddBelow (Set.range fun x : ↥(K p) => g p ↑x))
    {b : ℝ} (hb : (⨅ x : ↥(K p₀), g p₀ ↑x) < b) :
    ∀ᶠ p in 𝓝 p₀, (⨅ x : ↥(K p), g p ↑x) < b := by
  have : Nonempty ↥(K p₀) := hK₀ne.to_subtype
  have hgcont : Continuous (g p₀) := hg.comp (continuous_const.prodMk continuous_id)
  -- A genuine minimizer at `p₀`, so the bound can be stated against `V p₀`.
  obtain ⟨y, hyK, hymin⟩ := hK₀.exists_isMinOn hK₀ne hgcont.continuousOn
  have hyval : (⨅ x : ↥(K p₀), g p₀ ↑x) = g p₀ y :=
    le_antisymm (ciInf_le (hbdd p₀) ⟨y, hyK⟩)
      (le_ciInf fun x => (isMinOn_iff.mp hymin) ↑x x.2)
  -- Feed the gap `b - V p₀` to the lower-hemicontinuity bound.
  have hε : 0 < b - g p₀ y := by rw [hyval] at hb; linarith
  filter_upwards [eventually_iInf_lt_of_lowerHemicontinuousAt hKl hg hbdd hyK hε]
    with p hp
  linarith [hp]

/-- **Lower semicontinuity of the value function under upper hemicontinuity.**

`V p` eventually exceeds any bound strictly below `V p₀`.  This is the half that
consumes the whole upper-hemicontinuity chain: the contradiction produces a
*frequently* statement, first countability of the parameter space turns it into
a sequence, and `exists_subseq_tendsto_mem_of_isCompact` extracts a limit
feasible at `p₀` whose value would undercut `V p₀`. -/
theorem eventually_lt_iInf_of_iInf_lt
    {P X : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [TopologicalSpace X] [RegularSpace X] [T2Space X] [FirstCountableTopology X]
    [WeaklyLocallyCompactSpace X]
    {K : P → Set X} {p₀ : P} (hKu : UpperHemicontinuousAt K p₀)
    (hK₀ : IsCompact (K p₀))
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (hKne : ∀ p, (K p).Nonempty) (hKcompact : ∀ p, IsCompact (K p))
    (hbdd : ∀ p, BddBelow (Set.range fun x : ↥(K p) => g p ↑x))
    {b : ℝ} (hb : b < ⨅ x : ↥(K p₀), g p₀ ↑x) :
    ∀ᶠ p in 𝓝 p₀, b < ⨅ x : ↥(K p), g p ↑x := by
  by_contra hcon
  -- Failure gives a sequence of parameters along which the value stays low.
  rw [not_eventually] at hcon
  obtain ⟨q, hqtend, hqle⟩ := exists_seq_forall_of_frequently hcon
  -- At each, pick a minimizer; its value is the (low) infimum.
  have hgcont : ∀ r : P, Continuous (g r) :=
    fun r => hg.comp (continuous_const.prodMk continuous_id)
  choose x hxK hxmin using fun k =>
    (hKcompact (q k)).exists_isMinOn (hKne (q k)) (hgcont (q k)).continuousOn
  have hxval : ∀ k, g (q k) (x k) = ⨅ y : ↥(K (q k)), g (q k) ↑y := by
    intro k
    have : Nonempty ↥(K (q k)) := (hKne (q k)).to_subtype
    exact le_antisymm (le_ciInf fun y => (isMinOn_iff.mp (hxmin k)) ↑y y.2)
      (ciInf_le (hbdd (q k)) ⟨x k, hxK k⟩)
  -- Extract a convergent subsequence with feasible limit.
  obtain ⟨φ, hφmono, x₀, hx₀K, hx₀tend⟩ :=
    exists_subseq_tendsto_mem_of_isCompact hKu hK₀ hqtend hxK
  -- Its value is a limit of values below `b`, hence at most `b`.
  have hjoint : Tendsto (fun t => g (q (φ t)) (x (φ t))) atTop (𝓝 (g p₀ x₀)) :=
    (hg.tendsto (p₀, x₀)).comp
      ((hqtend.comp hφmono.tendsto_atTop).prodMk_nhds hx₀tend)
  have hle : g p₀ x₀ ≤ b := by
    refine le_of_tendsto hjoint ?_
    filter_upwards with t
    rw [hxval (φ t)]
    exact not_lt.mp (hqle (φ t))
  -- But `x₀` is feasible at `p₀`, so its value is at least `V p₀ > b`.
  exact absurd (lt_of_lt_of_le hb (ciInf_le (hbdd p₀) ⟨x₀, hx₀K⟩)) (not_lt.mpr hle)

/-- **Berge's value theorem, varying constraints.**

The value function `V p = ⨅ x ∈ K p, g p x` is continuous when the constraint
correspondence is compact-valued, nonempty-valued, and hemicontinuous in both
senses, and the objective is jointly continuous.

Each hypothesis is consumed exactly once and by a different half of the proof:
**lower** hemicontinuity gives `V p < b` above `V p₀`
(`eventually_iInf_lt_of_lt_iInf`), **upper** hemicontinuity gives `b < V p`
below it (`eventually_lt_iInf_of_iInf_lt`), and the order characterisation of
convergence in `ℝ` joins them. -/
theorem continuous_iInf_of_hemicontinuousAt
    {P X : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [TopologicalSpace X] [RegularSpace X] [T2Space X] [FirstCountableTopology X]
    [WeaklyLocallyCompactSpace X]
    {K : P → Set X} (hKcompact : ∀ p, IsCompact (K p)) (hKne : ∀ p, (K p).Nonempty)
    (hKu : ∀ p, UpperHemicontinuousAt K p) (hKl : ∀ p, LowerHemicontinuousAt K p)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (hbdd : ∀ p, BddBelow (Set.range fun x : ↥(K p) => g p ↑x)) :
    Continuous (fun p => ⨅ x : ↥(K p), g p ↑x) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  rw [ContinuousAt, tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · exact eventually_lt_iInf_of_iInf_lt (hKu p₀) (hKcompact p₀) hg hKne hKcompact hbdd hb
  · exact eventually_iInf_lt_of_lt_iInf (hKl p₀) (hKcompact p₀) (hKne p₀) hg hbdd hb

/-- **Berge's argmin theorem, varying constraints.**

The argmin correspondence `p ↦ {x ∈ K p | IsMinOn (g p) (K p) x}` is upper
hemicontinuous.

Minimality of a limit point is *not* proved by tracking comparison points into
the nearby constraint sets — the value theorem subsumes that.  Along a sequence
of minimizers, `g pₙ cₙ` **is** the value `V pₙ`, so joint continuity and
`continuous_iInf_of_hemicontinuousAt` together force `g p₀ c₀ = V p₀`, and
`V p₀ ≤ g p₀ y` for feasible `y` is then just `ciInf_le`. -/
theorem upperHemicontinuousAt_isMinOn_of_hemicontinuousAt
    {P X : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [TopologicalSpace X] [RegularSpace X] [T2Space X] [FirstCountableTopology X]
    [WeaklyLocallyCompactSpace X]
    {K : P → Set X} (hKcompact : ∀ p, IsCompact (K p)) (hKne : ∀ p, (K p).Nonempty)
    (hKu : ∀ p, UpperHemicontinuousAt K p) (hKl : ∀ p, LowerHemicontinuousAt K p)
    {g : P → X → ℝ} (hg : Continuous (Function.uncurry g))
    (hbdd : ∀ p, BddBelow (Set.range fun x : ↥(K p) => g p ↑x))
    (p₀ : P) [(𝓝 p₀).IsCountablyGenerated] :
    UpperHemicontinuousAt (fun p => {x ∈ K p | IsMinOn (g p) (K p) x}) p₀ := by
  obtain ⟨C, hCcompact, hKC⟩ :=
    exists_isCompact_eventually_subset_of_upperHemicontinuousAt (hKu p₀) (hKcompact p₀)
  refine UpperHemicontinuousAt.of_sequences hCcompact.isSeqCompact
    (hKC.mono fun p hp => (Set.sep_subset _ _).trans hp) ?_
  intro p hp c hc c₀ hc₀
  have hcK : ∀ n, c n ∈ K (p n) := fun n => (hc n).1
  -- Feasibility of the limit, from upper hemicontinuity.
  have hc₀K : c₀ ∈ K p₀ :=
    mem_of_tendsto_of_upperHemicontinuousAt (hKu p₀) (hKcompact p₀).isClosed hp hcK hc₀
  refine ⟨hc₀K, ?_⟩
  -- Along minimizers the objective value *is* the value function.
  have hval : ∀ n, g (p n) (c n) = ⨅ y : ↥(K (p n)), g (p n) ↑y := by
    intro n
    have : Nonempty ↥(K (p n)) := (hKne (p n)).to_subtype
    exact le_antisymm (le_ciInf fun y => (isMinOn_iff.mp (hc n).2) ↑y y.2)
      (ciInf_le (hbdd (p n)) ⟨c n, hcK n⟩)
  -- Two limits of the same sequence: joint continuity, and the value theorem.
  have hL : Tendsto (fun n => g (p n) (c n)) atTop (𝓝 (g p₀ c₀)) :=
    (hg.tendsto (p₀, c₀)).comp (hp.prodMk_nhds hc₀)
  have hV : Tendsto (fun n => g (p n) (c n)) atTop (𝓝 (⨅ y : ↥(K p₀), g p₀ ↑y)) := by
    simp only [hval]
    exact ((continuous_iInf_of_hemicontinuousAt hKcompact hKne hKu hKl hg hbdd).tendsto
      p₀).comp hp
  have heq : g p₀ c₀ = ⨅ y : ↥(K p₀), g p₀ ↑y := tendsto_nhds_unique hL hV
  -- Minimality is then `ciInf_le`.
  rw [isMinOn_iff]
  intro y hy
  rw [heq]
  exact ciInf_le (hbdd p₀) ⟨y, hy⟩

end TauCeti
