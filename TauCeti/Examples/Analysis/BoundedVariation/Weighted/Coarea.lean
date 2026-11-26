/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Coarea
public import TauCeti.Analysis.BoundedVariation.Weighted.HalfSpace
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Checks for the weighted coarea formula

* **Indicators.** For `u = 1_U` the superlevel set `{u > t}` is the whole space for `t < 0`, `U`
  for `0 ≤ t < 1` and empty for `t ≥ 1`, so for a `C¹` weight
  `∫_ℝ P_μ({1_U > t}; Ω) dt = ∫_0^1 P_μ(U; Ω) dt = P_μ(U; Ω)`
  (`lintegral_weightedPerimeter_setOf_lt_indicator`), as the weighted coarea formula requires of
  `V_μ(1_U; Ω) = P_μ(U; Ω)` (`weightedPerimeter_eq_lintegral_weightedPerimeter_setOf_lt_indicator`).
* **The identity on the Gaussian line.** For `u(t) = t` on `ℝ` with the Gaussian weight, the
  superlevel sets are the half-lines `(s, ∞)`, of Gaussian perimeter `φ(s)`
  (`gaussianPerimeter_Ioi`), so `∫_ℝ P_γ((s, ∞)) ds = ∫ φ = 1`
  (`lintegral_gaussianPerimeter_Ioi`) and the weighted coarea formula gives `V_γ(id; ℝ) = 1`
  (`weightedVariation_gaussianWeight_id`).
-/

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal RealInnerProductSpace

public noncomputable section

namespace TauCeti.Examples.WeightedCoarea

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {Ω : Opens E}

/-- The weighted perimeters of the superlevel sets of an indicator integrate to the weighted
perimeter of the set: `∫_ℝ P_μ({1_U > t}; Ω) dt = P_μ(U; Ω)`. -/
theorem lintegral_weightedPerimeter_setOf_lt_indicator (hW : ContDiff ℝ 1 W) (U : Set E) :
    ∫⁻ t, weightedPerimeter W Ω {x | t < U.indicator (1 : E → ℝ) x} = weightedPerimeter W Ω U := by
  have h : (fun t : ℝ => weightedPerimeter W Ω {x | t < U.indicator (1 : E → ℝ) x}) =
      (Ico 0 1).indicator fun _ => weightedPerimeter W Ω U := by
    funext t
    by_cases ht0 : t < 0
    · have : {x | t < U.indicator (1 : E → ℝ) x} = univ :=
        eq_univ_of_forall fun x => ht0.trans_le (indicator_nonneg (fun _ _ => zero_le_one) x)
      rw [this, weightedPerimeter_univ hW, indicator_of_notMem (by simp [ht0])]
    by_cases ht1 : t < 1
    · have : {x | t < U.indicator (1 : E → ℝ) x} = U := by
        ext x
        by_cases hx : x ∈ U <;> simp [hx, ht1, not_lt.1 ht0]
      rw [this, indicator_of_mem (by simp [not_lt.1 ht0, ht1])]
    · have : {x | t < U.indicator (1 : E → ℝ) x} = ∅ := by
        ext x
        by_cases hx : x ∈ U <;> simp [hx, not_lt.1 ht0, not_lt.1 ht1]
      rw [this, weightedPerimeter_empty, indicator_of_notMem (by simp [ht1])]
  rw [h, lintegral_indicator_const measurableSet_Ico, Real.volume_Ico, sub_zero,
    ENNReal.ofReal_one, mul_one]

/-- The weighted coarea formula for an indicator is the identity `P_μ(U; Ω) = P_μ(U; Ω)`. -/
theorem weightedPerimeter_eq_lintegral_weightedPerimeter_setOf_lt_indicator (hW : ContDiff ℝ 1 W)
    {U : Set E} (hU : MeasurableSet U) :
    weightedPerimeter W Ω U = ∫⁻ t, weightedPerimeter W Ω {x | t < U.indicator (1 : E → ℝ) x} := by
  rw [weightedPerimeter_def]
  exact weightedVariation_eq_lintegral_weightedPerimeter hW
    (locallyIntegrableOn_indicator_const hU.nullMeasurableSet (1 : ℝ))

/-- The Gaussian perimeter of the half-line `(s, ∞)` is `φ(s)`. -/
theorem gaussianPerimeter_Ioi (s : ℝ) :
    gaussianPerimeter (Ioi s) = ENNReal.ofReal (gaussianPDFReal 0 1 s) := by
  have h : Ioi s =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] {x : ℝ | ⟪x, (1 : ℝ)⟫ < s}ᶜ := by
    refine ae_restrict_of_ae ?_
    have : {x : ℝ | ⟪x, (1 : ℝ)⟫ < s}ᶜ = Ici s := by ext x; simp
    rw [this]
    exact Ioi_ae_eq_Ici
  rw [gaussianPerimeter_def, weightedPerimeter_congr_ae h,
    weightedPerimeter_compl contDiff_gaussianWeight, ← gaussianPerimeter_def,
    gaussianPerimeter_setOf_inner_lt (by simp) s]

/-- `∫_ℝ P_γ((s, ∞)) ds = ∫ φ = 1`. -/
theorem lintegral_gaussianPerimeter_Ioi : ∫⁻ s : ℝ, gaussianPerimeter (Ioi s) = 1 := by
  simp_rw [gaussianPerimeter_Ioi]
  exact lintegral_gaussianPDFReal_eq_one 0 one_ne_zero

/-- **The weighted coarea formula on the Gaussian line**: `V_γ(id; ℝ) = ∫_ℝ P_γ((s, ∞)) ds = 1`. -/
theorem weightedVariation_gaussianWeight_id :
    weightedVariation (gaussianWeight ℝ) ⊤ id = 1 := by
  rw [weightedVariation_eq_lintegral_weightedPerimeter contDiff_gaussianWeight
    (continuous_id.locallyIntegrable.locallyIntegrableOn _), ← lintegral_gaussianPerimeter_Ioi]
  -- The superlevel set `{x | t < id x}` is the half-line `Ioi t`.
  simp_rw [gaussianPerimeter_def, id_eq, ← Set.Ioi_def]

end TauCeti.Examples.WeightedCoarea
