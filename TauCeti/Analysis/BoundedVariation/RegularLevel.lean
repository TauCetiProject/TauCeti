/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Coarea
public import TauCeti.Analysis.Calculus.FDeriv.LevelSet
import Mathlib.MeasureTheory.Integral.Average
import TauCeti.Analysis.Calculus.Sard.OutermostStratum

/-!
# Quantitative selection of regular superlevel sets

Every interval of levels of a smooth scalar function contains a regular value whose superlevel
set has perimeter at most the total variation divided by the interval's length. For a compactly
supported function and a positive interval, the selected superlevel set has compact closure,
and its frontier is precisely the regular level set. These are the regular-value and perimeter
estimates used when approximating sets of finite perimeter by bounded open sets with smooth
boundary.

The selection combines the scalar BV coarea formula with the Morse--Sard theorem from
`TauCeti.Analysis.Calculus.Sard.OutermostStratum` and Mathlib's first-moment method
`MeasureTheory.exists_notMem_null_le_laverage`. No identification of perimeter with surface
measure is asserted here.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.2.2.
-/

public section

open Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {u : E → ℝ} {Ω : Opens E} {a b : ℝ}

/-- A smooth function has a regular value in every nonempty interval such that the perimeter
of its superlevel set is at most its variation divided by the interval's length. The estimate
also holds when the variation is infinite. -/
theorem ContDiff.exists_mem_Ioo_surjective_fderiv_perimeter_le (hu : ContDiff ℝ ∞ u)
    (hab : a < b) :
    ∃ t ∈ Ioo a b, (∀ x, u x = t → Surjective (fderiv ℝ u x)) ∧
      TauCeti.perimeter μ Ω {x | t < u x} ≤
        TauCeti.totalVariationOn μ Ω u / ENNReal.ofReal (b - a) := by
  let ν : Measure ℝ := volume.restrict (Ioo a b)
  let N : Set ℝ := (Ioo a b)ᶜ ∪ u '' {x | ¬ Surjective (fderiv ℝ u x)}
  have hν : ν ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioo, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (sub_pos.mpr hab)
  have hN : ν N = 0 := by
    refine measure_union_null ?_ ?_
    · simp [ν]
    · exact le_antisymm ((Measure.restrict_apply_le _ _).trans_eq
        (hu.addHaar_image_criticalPoints_eq_zero volume
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl _))) bot_le
  have hmeas : Measurable (fun t ↦ TauCeti.perimeter μ Ω {x | t < u x}) :=
    TauCeti.measurable_perimeter_setOf_lt hu.continuous.measurable.aemeasurable
  obtain ⟨t, htN, ht⟩ := exists_notMem_null_le_laverage hν hmeas.aemeasurable hN
  have htI : t ∈ Ioo a b := by simpa [N] using (not_or.mp htN).1
  refine ⟨t, htI, ?_, ht.trans ?_⟩
  · intro x hx
    by_contra hcrit
    exact (not_or.mp htN).2 ⟨x, hcrit, hx⟩
  · rw [laverage_eq, Measure.restrict_apply_univ, Real.volume_Ioo]
    gcongr
    exact (setLIntegral_le_lintegral (Ioo a b) _).trans_eq
      (TauCeti.totalVariationOn_eq_lintegral_perimeter
        (hu.continuous.locallyIntegrable.locallyIntegrableOn Ω)).symm

/-- For a compactly supported smooth function, a positive interval contains a regular value
whose strict superlevel set has compact closure and the quantitative perimeter bound. Its
frontier is the corresponding regular level set. -/
theorem ContDiff.exists_mem_Ioo_isCompact_closure_perimeter_le (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (ha : 0 ≤ a) (hab : a < b) :
    ∃ t ∈ Ioo a b, (∀ x, u x = t → Surjective (fderiv ℝ u x)) ∧
      IsCompact (closure {x | t < u x}) ∧
      frontier {x | t < u x} = {x | u x = t} ∧
      TauCeti.perimeter μ Ω {x | t < u x} ≤
        TauCeti.totalVariationOn μ Ω u / ENNReal.ofReal (b - a) := by
  obtain ⟨t, ht, hreg, hP⟩ := hu.exists_mem_Ioo_surjective_fderiv_perimeter_le
    (μ := μ) (Ω := Ω) hab
  refine ⟨t, ht, hreg, ?_, ?_, hP⟩
  · refine hc.isCompact.of_isClosed_subset isClosed_closure ?_
    refine closure_minimal (fun x hx ↦ subset_tsupport u ?_) (isClosed_tsupport u)
    exact ne_of_gt (lt_trans (lt_of_le_of_lt ha ht.1) hx)
  · exact hu.continuous.frontier_setOf_lt_eq_of_fderiv_ne_zero fun x hx hzero ↦ by
      obtain ⟨v, hv⟩ := hreg x hx 1
      simp [hzero] at hv
