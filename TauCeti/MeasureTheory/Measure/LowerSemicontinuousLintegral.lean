/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import TauCeti.Topology.Semicontinuity.Approximation

/-!
# Lower semicontinuity of a lower semicontinuous integrand in the measure

Fix a lower semicontinuous `f : Ω → ℝ≥0∞` on a pseudometric space. This file proves that the
pairing `μ ↦ ∫⁻ x, f x ∂μ` is lower semicontinuous for the weak topology on `FiniteMeasure Ω` and
on `ProbabilityMeasure Ω`, together with the two consequences the direct method of the calculus of
variations runs on: the `liminf` inequality along a weakly convergent family, and attainment of the
infimum on a nonempty compact set of measures.

For a bounded continuous integrand the pairing is *continuous* — that is what the weak topology is
defined by. The content here is that dropping boundedness and continuity down to lower
semicontinuity costs exactly one half of that continuity, and no integrability hypothesis at all:
the value `∞` is allowed on both sides.

## Main results

* `TauCeti.lowerSemicontinuous_lintegral_finiteMeasure` and
  `TauCeti.lowerSemicontinuous_lintegral_probabilityMeasure`: the pairing is lower semicontinuous.
* `TauCeti.le_liminf_lintegral_of_tendsto_probabilityMeasure` and
  `TauCeti.le_liminf_lintegral_of_tendsto_finiteMeasure`: the `liminf` form along a weakly
  convergent family.
* `TauCeti.exists_isMinOn_lintegral`: a nonempty compact set of probability measures contains one
  minimising the integral, with no finiteness assumption on the minimum value.
* `TauCeti.isClosed_setOfPred_lintegral_le_finiteMeasure` and
  `TauCeti.isClosed_setOfPred_lintegral_le_probabilityMeasure`: the sublevel sets of the pairing
  are closed.
* `TauCeti.lowerSemicontinuousOn_lintegral_comp`: for `h` lower semicontinuous and `Φ` arbitrary,
  `μ ↦ ∫⁻ x, h (Φ x) ∂μ` is still lower semicontinuous on a set of probability measures for which
  `Φ` is continuous on closed sets of uniformly almost full mass.

## Implementation notes

The proof is the standard monotone-approximation argument: `TauCeti.lscApprox` writes `f` as the
pointwise supremum of an increasing sequence of bounded continuous `ℝ≥0`-valued functions, the
monotone convergence theorem turns that into a supremum of integrals, each summand is continuous in
the measure because it is a weak-topology test function, and a supremum of continuous functions is
lower semicontinuous.

Only `OpensMeasurableSpace Ω` is used on the measurable side: it is what makes a lower
semicontinuous function measurable, and Mathlib's weak topology is already available at that
generality.
-/

public section

open Filter MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
  {f : Ω → ℝ≥0∞}

/-- Monotone convergence applied to the approximating sequence `TauCeti.lscApprox`: the
integral of a lower semicontinuous `f` is the supremum of the integrals of bounded continuous
test functions below it. -/
theorem lintegral_eq_iSup_lintegral_lscApprox (hf : LowerSemicontinuous f) (μ : Measure Ω) :
    ∫⁻ x, f x ∂μ = ⨆ n : ℕ, ∫⁻ x, (lscApprox f n x : ℝ≥0∞) ∂μ := by
  rw [← lintegral_iSup (fun n ↦ (lscApprox f n).continuous.measurable.coe_nnreal_ennreal)
    (monotone_coe_lscApprox f)]
  exact lintegral_congr fun x ↦ (iSup_coe_lscApprox hf x).symm

/-- Integration of a lower semicontinuous `f : Ω → ℝ≥0∞` is lower semicontinuous in the finite
measure, for the topology of weak convergence. -/
theorem lowerSemicontinuous_lintegral_finiteMeasure (hf : LowerSemicontinuous f) :
    LowerSemicontinuous fun μ : FiniteMeasure Ω ↦ ∫⁻ x, f x ∂(μ : Measure Ω) := by
  have h : (fun μ : FiniteMeasure Ω ↦ ∫⁻ x, f x ∂(μ : Measure Ω)) =
      fun μ : FiniteMeasure Ω ↦ ⨆ n : ℕ, ∫⁻ x, (lscApprox f n x : ℝ≥0∞) ∂(μ : Measure Ω) :=
    funext fun μ ↦ lintegral_eq_iSup_lintegral_lscApprox hf _
  rw [h]
  exact lowerSemicontinuous_iSup fun n ↦
    (FiniteMeasure.continuous_lintegral_boundedContinuousFunction
      (lscApprox f n)).lowerSemicontinuous

/-- Integration of a lower semicontinuous `f : Ω → ℝ≥0∞` is lower semicontinuous in the
probability measure, for the topology of weak convergence. -/
theorem lowerSemicontinuous_lintegral_probabilityMeasure (hf : LowerSemicontinuous f) :
    LowerSemicontinuous fun μ : ProbabilityMeasure Ω ↦ ∫⁻ x, f x ∂(μ : Measure Ω) := by
  convert (lowerSemicontinuous_lintegral_finiteMeasure hf).comp
    ProbabilityMeasure.toFiniteMeasure_continuous using 1
  funext μ
  simp only [Function.comp_apply,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]

/-- The `liminf` form of lower semicontinuity: along a weakly convergent family of probability
measures, the integral of a lower semicontinuous integrand can only drop in the limit. -/
theorem le_liminf_lintegral_of_tendsto_probabilityMeasure {γ : Type*} {L : Filter γ}
    {μs : γ → ProbabilityMeasure Ω}
    {μ : ProbabilityMeasure Ω} (hf : LowerSemicontinuous f) (h : Tendsto μs L (𝓝 μ)) :
    ∫⁻ x, f x ∂(μ : Measure Ω) ≤ liminf (fun i ↦ ∫⁻ x, f x ∂(μs i : Measure Ω)) L := by
  refine ((lowerSemicontinuous_lintegral_probabilityMeasure hf).le_liminf μ).trans ?_
  simpa [Function.comp_def] using h.liminf_le_liminf_comp
    (u := fun ν : ProbabilityMeasure Ω ↦ ∫⁻ x, f x ∂(ν : Measure Ω))

/-- The same `liminf` inequality for a weakly convergent family of finite measures. -/
theorem le_liminf_lintegral_of_tendsto_finiteMeasure {γ : Type*} {L : Filter γ}
    {μs : γ → FiniteMeasure Ω} {μ : FiniteMeasure Ω} (hf : LowerSemicontinuous f)
    (h : Tendsto μs L (𝓝 μ)) :
    ∫⁻ x, f x ∂(μ : Measure Ω) ≤ liminf (fun i ↦ ∫⁻ x, f x ∂(μs i : Measure Ω)) L := by
  refine ((lowerSemicontinuous_lintegral_finiteMeasure hf).le_liminf μ).trans ?_
  simpa [Function.comp_def] using h.liminf_le_liminf_comp
    (u := fun ν : FiniteMeasure Ω ↦ ∫⁻ x, f x ∂(ν : Measure Ω))

/-- Sublevel sets of the finite-measure pairing against a lower semicontinuous integrand are
weakly closed. -/
theorem isClosed_setOfPred_lintegral_le_finiteMeasure (hf : LowerSemicontinuous f) (a : ℝ≥0∞) :
    IsClosed {μ : FiniteMeasure Ω | ∫⁻ x, f x ∂(μ : Measure Ω) ≤ a} :=
  (lowerSemicontinuous_lintegral_finiteMeasure hf).isClosed_preimage a

/-- Sublevel sets of the probability-measure pairing against a lower semicontinuous integrand are
weakly closed. -/
theorem isClosed_setOfPred_lintegral_le_probabilityMeasure (hf : LowerSemicontinuous f)
    (a : ℝ≥0∞) :
    IsClosed {μ : ProbabilityMeasure Ω | ∫⁻ x, f x ∂(μ : Measure Ω) ≤ a} :=
  (lowerSemicontinuous_lintegral_probabilityMeasure hf).isClosed_preimage a

/-- The direct method of the calculus of variations for a lower semicontinuous integrand: on a
nonempty compact set of probability measures, the integral attains its infimum. The minimum value
is allowed to be `∞`, which happens exactly when every measure in the set gives `f` infinite
integral. -/
theorem exists_isMinOn_lintegral {K : Set (ProbabilityMeasure Ω)} (hK : K.Nonempty)
    (hKc : IsCompact K) (hf : LowerSemicontinuous f) :
    ∃ μ ∈ K, IsMinOn (fun ν : ProbabilityMeasure Ω ↦ ∫⁻ x, f x ∂(ν : Measure Ω)) K μ :=
  ((lowerSemicontinuous_lintegral_probabilityMeasure hf).lowerSemicontinuousOn K).exists_isMinOn
    hK hKc

/-- The infimum of the integral over a nonempty compact set of probability measures is a minimum:
it is the value at some member of the set. -/
theorem exists_lintegral_eq_iInf {K : Set (ProbabilityMeasure Ω)} (hK : K.Nonempty)
    (hKc : IsCompact K) (hf : LowerSemicontinuous f) :
    ∃ μ ∈ K, ∫⁻ x, f x ∂(μ : Measure Ω) =
      ⨅ ν : K, ∫⁻ x, f x ∂((ν : ProbabilityMeasure Ω) : Measure Ω) := by
  obtain ⟨μ, hμK, hμ⟩ := exists_isMinOn_lintegral hK hKc hf
  refine ⟨μ, hμK, le_antisymm ?_ (iInf_le_of_le ⟨μ, hμK⟩ le_rfl)⟩
  exact le_iInf fun ν ↦ hμ ν.2

section Lusin

/-! ### Integrands that are continuous only on closed sets of uniformly large mass

An integrand `h ∘ Φ` with `h` lower semicontinuous but `Φ` merely measurable is not lower
semicontinuous, and its integral is not lower semicontinuous in the measure on all of
`ProbabilityMeasure Ω`. It still is on a set `S` of measures for which `Φ` is continuous on closed
sets carrying all but an arbitrarily small part of the mass of every member of `S` at once: the
uniformity is what lets the exceptional set be ignored along a convergent family. Lusin's theorem
supplies such closed sets whenever the members of `S` share a fixed image under a map through which
`Φ` factors, as the squares of the couplings of two fixed marginals do. -/

/-- **Lower semicontinuity under a uniform Lusin condition.** Let `h : W → ℝ≥0∞` be lower
semicontinuous, `Φ : Ω → W` arbitrary, and `S` a set of probability measures on `Ω` such that for
every `ε > 0` some closed set `C`, on which `Φ` is continuous, has complement of mass at most `ε`
for every member of `S`. If `h ∘ Φ` is almost-everywhere measurable for each member of `S`, then
`μ ↦ ∫⁻ x, h (Φ x) ∂μ` is lower semicontinuous on `S` for the weak topology. -/
theorem lowerSemicontinuousOn_lintegral_comp {W : Type*} [TopologicalSpace W] {h : W → ℝ≥0∞}
    {Φ : Ω → W} {S : Set (ProbabilityMeasure Ω)} (hh : LowerSemicontinuous h)
    (hΦ : ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ C, IsClosed C ∧ ContinuousOn Φ C ∧ ∀ μ ∈ S, (μ : Measure Ω) Cᶜ ≤ ε)
    (hm : ∀ μ ∈ S, AEMeasurable (fun x ↦ h (Φ x)) (μ : Measure Ω)) :
    LowerSemicontinuousOn (fun μ : ProbabilityMeasure Ω ↦ ∫⁻ x, h (Φ x) ∂(μ : Measure Ω)) S := by
  classical
  intro μ₀ hμ₀ c hc
  beta_reduce at hc ⊢
  -- Truncate `h ∘ Φ` at a finite height `M` without losing the strict inequality at `μ₀`.
  have hsup : ∫⁻ x, h (Φ x) ∂(μ₀ : Measure Ω) =
      ⨆ n : ℕ, ∫⁻ x, min (h (Φ x)) n ∂(μ₀ : Measure Ω) := by
    rw [← lintegral_iSup' (fun n ↦ (hm μ₀ hμ₀).min aemeasurable_const)
      (.of_forall fun x m n hmn ↦ min_le_min_left _ (Nat.cast_le.mpr hmn))]
    refine lintegral_congr fun x ↦ ?_
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  rw [hsup] at hc
  obtain ⟨M, hM⟩ := lt_iSup_iff.mp hc
  obtain ⟨c', hcc', hc'M⟩ := exists_between hM
  -- Off a closed set `C` of nearly full mass, replace the truncation by its maximal value `M`:
  -- the result `G` is lower semicontinuous and exceeds the truncation by at most `M` on `Cᶜ`.
  obtain ⟨C, hC, hΦC, hCS⟩ := hΦ ((c' - c) / M) (by
    simp [ENNReal.div_eq_zero_iff, tsub_eq_zero_iff_le, hcc'.not_ge])
  set G : Ω → ℝ≥0∞ := fun x ↦ if x ∈ C then min (h (Φ x)) M else M with hG_def
  have hG : LowerSemicontinuous G := by
    refine lowerSemicontinuous_iff.mpr fun x ↦ lowerSemicontinuousAt_iff.mpr fun y hy ↦ ?_
    by_cases hx : x ∈ C
    · simp only [hG_def, hx, ↓reduceIte, lt_min_iff] at hy
      have hev : ∀ᶠ x' in 𝓝[C] x, y < h (Φ x') :=
        (hΦC x hx).tendsto.eventually (lowerSemicontinuousAt_iff.mp (hh (Φ x)) y hy.1)
      filter_upwards [eventually_nhdsWithin_iff.mp hev] with x' hx'
      by_cases hx'C : x' ∈ C
      · simpa [hG_def, hx'C] using ⟨hx' hx'C, hy.2⟩
      · simpa [hG_def, hx'C] using hy.2
    · filter_upwards [hC.isOpen_compl.mem_nhds hx] with x' hx'
      simpa [hG_def, hx, show x' ∉ C from hx'] using hy
  have hG_le : ∀ x, G x ≤ h (Φ x) + Cᶜ.indicator (fun _ ↦ (M : ℝ≥0∞)) x := fun x ↦ by
    by_cases hx : x ∈ C <;> simp [hG_def, hx]
  have hc'G : c' < ∫⁻ x, G x ∂(μ₀ : Measure Ω) :=
    hc'M.trans_le (lintegral_mono fun x ↦ by by_cases hx : x ∈ C <;> simp [hG_def, hx])
  filter_upwards [nhdsWithin_le_nhds (lowerSemicontinuousAt_iff.mp
    (lowerSemicontinuous_lintegral_probabilityMeasure hG μ₀) c' hc'G), self_mem_nhdsWithin]
    with μ hμ hμS
  by_contra! hle
  refine (hμ.trans_le ((lintegral_mono hG_le).trans ?_)).false
  rw [lintegral_add_right _ (measurable_const.indicator hC.isOpen_compl.measurableSet),
    lintegral_indicator_const hC.isOpen_compl.measurableSet, ← add_tsub_cancel_of_le hcc'.le]
  have hMC : (M : ℝ≥0∞) * (μ : Measure Ω) Cᶜ ≤ (M : ℝ≥0∞) * ((c' - c) / M) := by
    gcongr
    exact hCS μ hμS
  exact add_le_add hle (hMC.trans ENNReal.mul_div_le)

end Lusin

end TauCeti
