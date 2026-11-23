/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Continuous functions and the `L^∞` seminorm

A function continuous on a compact set `K` is bounded there, so it lies in `L^∞(μ.restrict s)` for
every measurable `s ⊆ K` (`ContinuousOn.memLp_top_restrict_of_subset_isCompact`). Allowing `s ⊊ K`
covers the usual case of an open interval `(a, b)` inside the compact interval `[a, b]`. This is the
continuous counterpart of Mathlib's `MonotoneOn.memLp_top`, and the restricted-measure counterpart
of `Continuous.memLp_top_of_hasCompactSupport`.

Without compactness, a function continuous on a measurable set `s` and bounded there lies in
`L^∞(μ.restrict s)` (`ContinuousOn.memLp_top_restrict_of_bound`).

The same bound controls a pointwise composition `x ↦ A x ∘L B x` of operator families with `A`
continuous on `K`: `A ∘L B` lies in `Lᵖ(s)` whenever `B` does
(`MeasureTheory.MemLp.clm_comp_of_continuousOn`, Hölder's inequality
`ContinuousLinearMap.memLp_of_bilin` for `ContinuousLinearMap.compL` with exponents `(∞, p, p)`).

On a compact space with a measure that is finite on compact sets, every continuous function lies in
every `Lᵖ`, so for a finite exponent `p ≠ 0` its `Lᵖ` seminorm is the integral
`(∫ ‖f‖ ^ p dμ) ^ (1 / p)` (`Continuous.eLpNorm_eq_integral_rpow_norm`).

In the other direction, for a measure that charges every nonempty open set
(`MeasureTheory.Measure.IsOpenPosMeasure`), the `L^∞` seminorm bounds the value of `f` at every
point where `f` is continuous (`ContinuousAt.eNorm_le_eLpNorm_top`).
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SeminormedAddGroup E]

/-- A function continuous on a compact set `K` is essentially bounded on every measurable
`s ⊆ K`. -/
theorem ContinuousOn.memLp_top_restrict_of_subset_isCompact {f : X → E} {K s : Set X}
    {μ : Measure X}
    (hf : ContinuousOn f K) (hK : IsCompact K) (hs : MeasurableSet s) (hsK : s ⊆ K) :
    MemLp f ∞ (μ.restrict s) := by
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn (continuous_nnNorm.comp_continuousOn hf)).bddAbove
  refine memLp_top_of_bound_eNorm (hf.aestronglyMeasurable_of_subset_isCompact hK hs hsK) C ?_
  filter_upwards [ae_restrict_mem hs] with x hx using eNorm_le_coe.2 <| hC ⟨x, hsK hx, rfl⟩

/-- A function continuous and bounded on a measurable set `s` is essentially bounded on `s`. -/
theorem ContinuousOn.memLp_top_restrict_of_bound [SecondCountableTopologyEither X E] {f : X → E}
    {s : Set X} {μ : Measure X} (hf : ContinuousOn f s) (hs : MeasurableSet s) (C : ℝ)
    (hC : ∀ x ∈ s, ‖f x‖ ≤ C) : MemLp f ∞ (μ.restrict s) :=
  memLp_top_of_bound_eNorm (hf.aestronglyMeasurable hs) C.toNNReal <| (ae_restrict_iff' hs).2 <|
    .of_forall fun x hx ↦ (ofReal_norm (f x)).symm.trans_le (ENNReal.ofReal_le_ofReal (hC x hx))

omit [OpensMeasurableSpace X] in
/-- **The essential supremum dominates a value at a point of continuity.** If `f` is continuous
at `x` and the measure charges every nonempty open set, then `‖f x‖ₑ ≤ ‖f‖_{L^∞}`. -/
theorem ContinuousAt.eNorm_le_eLpNorm_top {μ : Measure X} [μ.IsOpenPosMeasure] {f : X → E}
    {x : X} (hf : ContinuousAt f x) : ‖f x‖ₑ ≤ eLpNorm f ∞ μ := by
  by_cases hm : AEStronglyMeasurable f μ
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hm]
    exact le_top
  by_contra h
  push Not at h
  -- Near `x`, `‖f‖ₑ` exceeds the essential supremum on a neighbourhood, of positive measure.
  have hV := hf.eNorm.eventually_const_lt h
  have hae : ∀ᵐ y ∂μ, ‖f y‖ₑ ≤ eLpNorm f ∞ μ := by
    rw [eLpNorm_exponent_top hm]
    exact eNorm_ae_le_eLpNormEssSup f μ
  have h0 : μ {y | eLpNorm f ∞ μ < ‖f y‖ₑ} = 0 := by simpa only [ae_iff, not_le] using hae
  exact (μ.measure_pos_of_mem_nhds hV).ne' h0

section CLMComp

variable {𝕜 F G H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {A : X → G →L[𝕜] H} {B : X → F →L[𝕜] G} {K s : Set X} {μ : Measure X}

/-- **Composing an `Lᵖ` operator family with a continuous one.** If `A` is continuous on a compact
set `K` and `B` is in `Lᵖ` on a measurable `s ⊆ K`, then so is `A ∘L B`. -/
theorem MeasureTheory.MemLp.clm_comp_of_continuousOn {p : ℝ≥0∞} (hB : MemLp B p (μ.restrict s))
    (hA : ContinuousOn A K) (hK : IsCompact K) (hs : MeasurableSet s) (hsK : s ⊆ K) :
    MemLp (fun x => (A x).comp (B x)) p (μ.restrict s) :=
  (ContinuousLinearMap.compL 𝕜 F G H).memLp_of_bilin p
    (hA.memLp_top_restrict_of_subset_isCompact hK hs hsK) hB

end CLMComp

/-- The `Lᵖ` seminorm of a continuous function on a compact space, for a finite exponent `p ≠ 0`
and a measure finite on compact sets, as an integral: `‖f‖_{Lᵖ} = (∫ ‖f‖ ^ p dμ) ^ (1 / p)`. -/
theorem Continuous.eLpNorm_eq_integral_rpow_norm {F : Type*} [NormedAddCommGroup F]
    [CompactSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {f : X → F} (hf : Continuous f)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm f p μ = ENNReal.ofReal ((∫ x, ‖f x‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹) :=
  (hf.memLp_of_hasCompactSupport (.of_compactSpace f)).eLpNorm_eq_integral_rpow_norm hp0 hpt
