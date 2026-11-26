/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.Portmanteau

/-!
# Filter operations, law congruence, and Slutsky without separability

Mathlib defines `MeasureTheory.TendstoInDistribution X l Z μ μ'` along an arbitrary filter `l`,
packaging pointwise almost-everywhere measurability together with weak convergence of the laws in
`MeasureTheory.ProbabilityMeasure`. This file supplies basic filter operations for
`TendstoInDistribution` (precomposition along a `Filter.Tendsto` map of indices, monotonicity in
the index filter, congruence under eventual equality of pushforward laws allowing different sample
spaces, eventual almost-everywhere congruence along the filter, and sequential characterization for
countably generated index filters), law-invariance and identity-limit adapters, and Slutsky's
convergence-in-distribution replacement lemma without second countability or Borel-space
assumptions.

## Main statements

* `MeasureTheory.TendstoInDistribution.comp_tendsto` — precompose the index along a filter limit.
* `MeasureTheory.TendstoInDistribution.mono_left` — weaken the index filter.
* `MeasureTheory.TendstoInDistribution.congr_map` — transfer convergence in distribution between
  random variables with eventually equal pushforward laws (possibly on different probability
  spaces).
* `MeasureTheory.TendstoInDistribution.congr'` — replace random variables eventually almost
  everywhere along the index filter.
* `MeasureTheory.tendstoInDistribution_iff_forall_seq_tendsto` — along a countably generated filter,
  convergence in distribution is equivalent to convergence in distribution along every sequence
  tending to the filter.
* `MeasureTheory.TendstoInDistribution.of_map_eq` and
  `MeasureTheory.tendstoInDistribution_congr_map` — convergence in distribution depends on the limit
  random variable only through its law.
* `MeasureTheory.tendstoInDistribution_id_iff` — convergence in distribution to the identity on
  `(E, ν)` is pointwise almost-everywhere measurability plus weak convergence of the pushforward
  laws to `ν`.
* `MeasureTheory.TendstoInDistribution.congr_of_tendstoInMeasure_dist` and
  `MeasureTheory.TendstoInDistribution.congr_of_tendstoInMeasure_sub` — Slutsky's replacement lemma
  along an arbitrary filter for any pseudometric space or seminormed group with opens-measurable
  structure, without second countability or Borel-space assumptions.

## Source

* `MeasureTheory.TendstoInDistribution.congr_of_tendstoInMeasure_dist` (with
  `MeasureTheory.abs_integral_map_sub_le_of_lipschitz` in
  `TauCeti.MeasureTheory.Integral.Bochner.Basic`) is adapted from Mathlib's proof of
  `MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`
  (`Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`), splitting the integral on a
  null-measurable Lipschitz deviation event instead of `{δ ≤ ‖Y - X‖}` and replacing Mathlib's
  countably generated Lipschitz portmanteau theorem with
  `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lipschitz_integral_tendsto_of_filter`.

## References

* P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Theorem 2.1 and
  Theorem 3.1.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §2, Lemma 2.8.
-/

public section

open Filter
open scoped Topology

namespace MeasureTheory

variable {ι κ E Ω' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mE : MeasurableSpace E} [TopologicalSpace E] [OpensMeasurableSpace E]

/-- Precomposing the index of a family of random variables with a function tending to `l` preserves
convergence in distribution. -/
protected theorem TendstoInDistribution.comp_tendsto {l : Filter ι} {l' : Filter κ}
    {X : (i : ι) → Ω i → E} {Z : Ω' → E} {f : κ → ι}
    (h : TendstoInDistribution X l Z μ μ') (hf : Tendsto f l' l) :
    TendstoInDistribution (fun k ↦ X (f k)) l' Z (fun k ↦ μ (f k)) μ' where
  forall_aemeasurable k := h.forall_aemeasurable (f k)
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.comp hf

/-- Convergence in distribution is monotone in the index filter. -/
protected theorem TendstoInDistribution.mono_left {l₁ l₂ : Filter ι}
    {X : (i : ι) → Ω i → E} {Z : Ω' → E}
    (h : TendstoInDistribution X l₂ Z μ μ') (hl : l₁ ≤ l₂) :
    TendstoInDistribution X l₁ Z μ μ' :=
  h.comp_tendsto (tendsto_id'.2 hl)

/-- Convergence in distribution depends only on the eventual pushforward laws of the random
variables and the law of the limit, allowing both the index sample spaces and the limit space to
change. Pointwise almost-everywhere measurability of the replacement family and limit is required
because `TendstoInDistribution` records them globally and `Measure.map` is totalized to a Dirac
measure on non-almost-everywhere-measurable functions. -/
protected theorem TendstoInDistribution.congr_map {l : Filter ι}
    {Ω₂ : ι → Type*} {m₂ : ∀ i, MeasurableSpace (Ω₂ i)}
    {μ₂ : (i : ι) → Measure (Ω₂ i)} [∀ i, IsProbabilityMeasure (μ₂ i)]
    {Ω'' : Type*} {m'' : MeasurableSpace Ω''} {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {X : (i : ι) → Ω i → E} {Y : (i : ι) → Ω₂ i → E} {Z : Ω' → E} {W : Ω'' → E}
    (h : TendstoInDistribution X l Z μ μ')
    (hY : ∀ i, AEMeasurable (Y i) (μ₂ i)) (hW : AEMeasurable W μ'')
    (hXY : ∀ᶠ i in l, (μ i).map (X i) = (μ₂ i).map (Y i))
    (hZW : μ'.map Z = μ''.map W) :
    TendstoInDistribution Y l W μ₂ μ'' where
  forall_aemeasurable := hY
  aemeasurable_limit := hW
  tendsto := by
    have hlim : (⟨μ'.map Z, inferInstance⟩ : ProbabilityMeasure E) =
        ⟨μ''.map W, inferInstance⟩ :=
      Subtype.ext hZW
    rw [← hlim]
    refine h.tendsto.congr' ?_
    filter_upwards [hXY] with i hi
    exact Subtype.ext hi

/-- Convergence in distribution is preserved when the random variables are modified on null sets
eventually along the index filter and at the limit. Pointwise almost-everywhere measurability of
the replacement family is required at all indices because `TendstoInDistribution` records it
globally. -/
protected theorem TendstoInDistribution.congr' {l : Filter ι}
    {X Y : (i : ι) → Ω i → E} {Z T : Ω' → E}
    (h : TendstoInDistribution X l Z μ μ') (hY : ∀ i, AEMeasurable (Y i) (μ i))
    (hXY : ∀ᶠ i in l, X i =ᵐ[μ i] Y i) (hZT : Z =ᵐ[μ'] T) :
    TendstoInDistribution Y l T μ μ' :=
  h.congr_map hY (h.aemeasurable_limit.congr hZT)
    (hXY.mono fun _ hi ↦ Measure.map_congr hi) (Measure.map_congr hZT)

/-- Along a countably generated filter, convergence in distribution is equivalent to convergence in
distribution along every sequence tending to that filter. -/
theorem tendstoInDistribution_iff_forall_seq_tendsto {l : Filter ι} [l.IsCountablyGenerated]
    {X : (i : ι) → Ω i → E} {Z : Ω' → E}
    (hX : ∀ i, AEMeasurable (X i) (μ i)) (hZ : AEMeasurable Z μ') :
    TendstoInDistribution X l Z μ μ' ↔
      ∀ u : ℕ → ι, Tendsto u atTop l →
        TendstoInDistribution (fun n ↦ X (u n)) atTop Z (fun n ↦ μ (u n)) μ' where
  mp h _ hu := h.comp_tendsto hu
  mpr h :=
    { forall_aemeasurable := hX
      aemeasurable_limit := hZ
      tendsto := tendsto_iff_seq_tendsto.2 fun u hu ↦ (h u hu).tendsto }

/-- Convergence in distribution depends on the limit random variable only through its law. -/
protected theorem TendstoInDistribution.of_map_eq {Ω'' : Type*} [MeasurableSpace Ω'']
    {μ'' : Measure Ω''} [IsProbabilityMeasure μ''] {l : Filter ι}
    {X : (i : ι) → Ω i → E} {Z : Ω' → E} {W : Ω'' → E}
    (h : TendstoInDistribution X l Z μ μ') (hW : AEMeasurable W μ'')
    (heq : μ'.map Z = μ''.map W) :
    TendstoInDistribution X l W μ μ'' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hW
  tendsto := by
    have hlim : (⟨μ'.map Z, inferInstance⟩ : ProbabilityMeasure E) =
        ⟨μ''.map W, inferInstance⟩ := Subtype.ext heq
    rw [← hlim]
    exact h.tendsto

/-- Two almost-everywhere measurable limit random variables with the same law determine the same
convergence-in-distribution predicate. -/
theorem tendstoInDistribution_congr_map {Ω'' : Type*} [MeasurableSpace Ω'']
    {μ'' : Measure Ω''} [IsProbabilityMeasure μ''] {l : Filter ι}
    {X : (i : ι) → Ω i → E} {Z : Ω' → E} {W : Ω'' → E}
    (hZ : AEMeasurable Z μ') (hW : AEMeasurable W μ'') (heq : μ'.map Z = μ''.map W) :
    TendstoInDistribution X l Z μ μ' ↔ TendstoInDistribution X l W μ μ'' :=
  ⟨fun h ↦ h.of_map_eq hW heq, fun h ↦ h.of_map_eq hZ heq.symm⟩

/-- Convergence in distribution to the identity on `(E, ν)` is equivalent to pointwise
almost-everywhere measurability together with weak convergence of the pushforward laws to `ν` in
`ProbabilityMeasure E`. -/
theorem tendstoInDistribution_id_iff {l : Filter ι} {X : (i : ι) → Ω i → E}
    {ν : Measure E} [IsProbabilityMeasure ν] :
    TendstoInDistribution X l id μ ν ↔
      (∀ i, AEMeasurable (X i) (μ i)) ∧
        Tendsto (β := ProbabilityMeasure E) (fun i ↦ ⟨(μ i).map (X i), inferInstance⟩) l
          (𝓝 ⟨ν, inferInstance⟩) := by
  have hlim : (⟨ν.map id, inferInstance⟩ : ProbabilityMeasure E) = ⟨ν, inferInstance⟩ :=
    Subtype.ext Measure.map_id
  constructor
  · intro h
    exact ⟨h.forall_aemeasurable, hlim ▸ h.tendsto⟩
  · rintro ⟨hX, ht⟩
    exact
      { forall_aemeasurable := hX
        aemeasurable_limit := measurable_id.aemeasurable
        tendsto := hlim.symm ▸ ht }

/-- **Slutsky's convergence-in-distribution replacement lemma without separability**, for a general
pseudometric space and arbitrary filter `l`. If `X i → Z` in distribution and
`dist (Y i) (X i) → 0` in probability, with `Y i` almost-everywhere measurable, then `Y i → Z` in
distribution. Unlike Mathlib's `tendstoInDistribution_of_tendstoInMeasure_sub`, this drops
`SecondCountableTopology`, `BorelSpace`, and countable generation of `l`. -/
protected theorem TendstoInDistribution.congr_of_tendstoInMeasure_dist
    {E Ω'' : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace Ω''] {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {l : Filter ι} {X Y : ι → Ω'' → E} {Z : Ω' → E}
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY : ∀ i, AEMeasurable (Y i) μ'')
    (hXY : TendstoInMeasure μ'' (fun i ω ↦ dist (Y i ω) (X i ω)) l (fun _ ↦ 0)) :
    TendstoInDistribution Y l Z (fun _ ↦ μ'') μ' where
  forall_aemeasurable := hY
  aemeasurable_limit := hXZ.aemeasurable_limit
  tendsto := by
    apply ProbabilityMeasure.tendsto_iff_forall_lipschitz_integral_tendsto_of_filter.2
    rintro F ⟨M, hF_bd⟩ ⟨L, hF_lip⟩
    let L' : NNReal := max L 1
    have hL' : 0 < L' := lt_of_lt_of_le zero_lt_one (le_max_right L 1)
    have hF_lip' : LipschitzWith L' F := hF_lip.weaken (le_max_left L 1)
    have hX_lim : Tendsto (fun i ↦ ∫ x, F x ∂(μ''.map (X i))) l (𝓝 (∫ x, F x ∂(μ'.map Z))) := by
      simpa using ProbabilityMeasure.tendsto_iff_forall_lipschitz_integral_tendsto_of_filter.1
        hXZ.tendsto F ⟨M, hF_bd⟩ ⟨L', hF_lip'⟩
    refine hX_lim.congr_dist ?_
    rw [Metric.tendsto_nhds]
    intro ε hε
    set δ : ℝ := ε / (2 * (L' : ℝ)) with hδ_def
    have hδ : 0 < δ := by rw [hδ_def]; positivity
    have hLδ : (L' : ℝ) * δ = ε / 2 := by
      rw [hδ_def]
      field_simp
    have hdist : Tendsto (fun i ↦ μ''.real {ω | δ ≤ dist (Y i ω) (X i ω)}) l (𝓝 0) := by
      rw [tendstoInMeasure_iff_measureReal_norm] at hXY
      simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hXY δ hδ
    have h_bd : Tendsto (fun i ↦ ε / 2 + M * μ''.real {ω | δ ≤ dist (Y i ω) (X i ω)}) l
        (𝓝 (ε / 2)) := by
      simpa only [mul_zero, add_zero] using
        (tendsto_const_nhds (x := ε / 2)).add (hdist.const_mul M)
    filter_upwards [h_bd.eventually_lt_const (half_lt_self hε)] with i hi
    simp only [Real.dist_eq, sub_zero, abs_abs, ProbabilityMeasure.coe_mk]
    rw [abs_sub_comm]
    calc |∫ x, F x ∂(μ''.map (Y i)) - ∫ x, F x ∂(μ''.map (X i))|
        ≤ (L' : ℝ) * δ * μ''.real Set.univ + M * μ''.real {ω | δ ≤ dist (Y i ω) (X i ω)} :=
          abs_integral_map_sub_le_of_lipschitz (hXZ.forall_aemeasurable i) (hY i)
            hF_bd hF_lip' hδ
      _ = (L' : ℝ) * δ + M * μ''.real {ω | δ ≤ dist (Y i ω) (X i ω)} := by
          rw [probReal_univ, mul_one]
      _ < ε := by linarith

/-- **Slutsky's convergence-in-distribution replacement lemma without separability.** If `X i → Z`
in distribution and `Y i - X i → 0` in probability along an arbitrary filter `l` in a seminormed
group with opens-measurable structure, with `Y i` almost-everywhere measurable, then `Y i → Z` in
distribution. -/
protected theorem TendstoInDistribution.congr_of_tendstoInMeasure_sub
    {E Ω'' : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace Ω''] {μ'' : Measure Ω''} [IsProbabilityMeasure μ'']
    {l : Filter ι} {X Y : ι → Ω'' → E} {Z : Ω' → E}
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hY : ∀ i, AEMeasurable (Y i) μ'')
    (hXY : TendstoInMeasure μ'' (fun i ω ↦ Y i ω - X i ω) l (fun _ ↦ 0)) :
    TendstoInDistribution Y l Z (fun _ ↦ μ'') μ' := by
  refine hXZ.congr_of_tendstoInMeasure_dist hY ?_
  rw [tendstoInMeasure_iff_norm] at hXY ⊢
  simpa only [sub_zero, dist_eq_norm_sub, Real.norm_eq_abs, abs_norm] using hXY

end MeasureTheory
