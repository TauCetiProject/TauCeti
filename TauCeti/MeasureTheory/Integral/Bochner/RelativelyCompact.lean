/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.MeasureTheory.VectorMeasure.WithDensity

/-!
# Relative compactness of the set integrals of an integrable function

For an integrable function `h : S → E` into a real normed space, the set of its set integrals
`{∫ s in A, h s ∂μ | A : Set S}` is totally bounded, and hence relatively compact. The same
therefore holds for the range of the vector measure `μ.withDensityᵥ h`: a vector measure with a
Bochner-integrable density has relatively norm compact range.

The set integrals of an integrable simple function `∑ⱼ 𝟙_{Bⱼ} xⱼ` lie in the compact image of
the box `∏ⱼ [0, μ(Bⱼ)]` under `t ↦ ∑ⱼ tⱼ xⱼ`. A general integrable function is approximated in
`L¹` by such simple functions, and the set integrals move by at most the `L¹` distance.

Completeness of `E` is not assumed: without it every Bochner integral vanishes, and all
statements hold trivially.

## Main declarations

* `MeasureTheory.Integrable.totallyBounded_range_setIntegral`: the set integrals of an integrable
  function form a totally bounded set.
* `MeasureTheory.Integrable.isCompact_closure_range_setIntegral`: they form a relatively compact
  set.
* `MeasureTheory.Measure.totallyBounded_range_withDensityᵥ`,
  `MeasureTheory.Measure.isCompact_closure_range_withDensityᵥ`: the same for the range of the
  vector measure `μ.withDensityᵥ h`.

## References

* J. Diestel and J. J. Uhl, *Vector Measures*, Chapter II, §2, and Chapter III, §1.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} {h : S → E}

/-- The set integrals of an integrable simple function lie in a common compact set: the image of
the box `∏_{y ≠ 0} [0, μ (g ⁻¹' {y})]` under `t ↦ ∑_y t_y • y`. -/
private theorem SimpleFunc.exists_isCompact_forall_setIntegral_mem (g : SimpleFunc S E)
    (hg : Integrable g μ) : ∃ K : Set E, IsCompact K ∧ ∀ A : Set S, ∫ s in A, g s ∂μ ∈ K := by
  classical
  by_cases hE : CompleteSpace E
  swap
  · exact ⟨{0}, isCompact_singleton, fun A ↦ integral_of_not_completeSpace hE⟩
  let F : Finset E := {y ∈ g.range | y ≠ 0}
  refine ⟨(fun t : F → ℝ ↦ ∑ y : F, t y • (y : E)) '' Icc 0 fun y ↦ μ.real (g ⁻¹' {(y : E)}),
    isCompact_Icc.image (by fun_prop), fun A ↦ ⟨fun y ↦ (μ.restrict A).real (g ⁻¹' {(y : E)}),
    ⟨fun _ ↦ measureReal_nonneg, fun y ↦ ?_⟩, ?_⟩⟩
  · exact ENNReal.toReal_mono
      (g.measure_preimage_lt_top_of_integrable hg (Finset.mem_filter.1 y.property).2).ne
      (Measure.restrict_apply_le A _)
  · rw [← SimpleFunc.integral_eq_integral g hg.restrict, SimpleFunc.integral_eq_sum_filter]
    exact Finset.sum_coe_sort F fun y ↦ (μ.restrict A).real (g ⁻¹' {y}) • y

/-- The set integrals `∫ s in A, h s ∂μ` of an integrable function `h`, over all sets `A`, form a
totally bounded set. -/
theorem Integrable.totallyBounded_range_setIntegral (hh : Integrable h μ) :
    TotallyBounded (range fun A : Set S ↦ ∫ s in A, h s ∂μ) := by
  refine EMetric.totallyBounded_iff.2 fun ε hε ↦ ?_
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨g, hhg, hg⟩ :=
    (memLp_one_iff_integrable.2 hh).exists_simpleFunc_eLpNorm_sub_lt ENNReal.one_ne_top hε2.ne'
  have hg : Integrable g μ := memLp_one_iff_integrable.1 hg
  obtain ⟨K, hK, hgK⟩ := g.exists_isCompact_forall_setIntegral_mem hg
  obtain ⟨t, ht, hKt⟩ := EMetric.totallyBounded_iff.1 hK.totallyBounded (ε / 2) hε2
  refine ⟨t, ht, ?_⟩
  rintro - ⟨A, rfl⟩
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.1 (hKt (hgK A))
  refine mem_iUnion₂.2 ⟨y, hyt, ?_⟩
  have hAg : edist (∫ s in A, h s ∂μ) (∫ s in A, g s ∂μ) < ε / 2 := by
    rw [eDist_eq_eNorm_sub, ← integral_sub hh.integrableOn hg.integrableOn]
    calc ‖∫ s in A, h s - g s ∂μ‖ₑ ≤ ∫⁻ s in A, ‖h s - g s‖ₑ ∂μ :=
          eNorm_integral_le_lintegral_eNorm _
      _ ≤ ∫⁻ s, ‖h s - g s‖ₑ ∂μ := setLIntegral_le_lintegral _ _
      _ = eLpNorm (h - ⇑g) 1 μ :=
          (eLpNorm_one_eq_lintegral_eNorm (hh.sub hg).aestronglyMeasurable).symm
      _ < ε / 2 := hhg
  calc edist (∫ s in A, h s ∂μ) y ≤ edist (∫ s in A, h s ∂μ) (∫ s in A, g s ∂μ) + edist _ y :=
        edist_triangle _ _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hAg hy
    _ = ε := ENNReal.add_halves ε

/-- The set integrals `∫ s in A, h s ∂μ` of an integrable function `h`, over all sets `A`, form a
relatively compact set. -/
theorem Integrable.isCompact_closure_range_setIntegral (hh : Integrable h μ) :
    IsCompact (closure (range fun A : Set S ↦ ∫ s in A, h s ∂μ)) := by
  by_cases hE : CompleteSpace E
  · exact hh.totallyBounded_range_setIntegral.closure.isCompact_of_isClosed isClosed_closure
  · simp [integral_of_not_completeSpace hE]

/-- Every value of the vector measure `μ.withDensityᵥ h` is a set integral of `h`. -/
theorem Measure.range_withDensityᵥ_subset (μ : Measure S) (h : S → E) :
    range (μ.withDensityᵥ h) ⊆ range fun A : Set S ↦ ∫ s in A, h s ∂μ := by
  rintro - ⟨A, rfl⟩
  by_cases hA : MeasurableSet A
  · by_cases hh : Integrable h μ
    · exact ⟨A, (withDensityᵥ_apply hh hA).symm⟩
    · exact ⟨∅, by simp [withDensityᵥ_of_not_integrable hh]⟩
  · exact ⟨∅, by simp [VectorMeasure.not_measurable _ hA]⟩

/-- The range of the vector measure `μ.withDensityᵥ h` is totally bounded. -/
theorem Measure.totallyBounded_range_withDensityᵥ (μ : Measure S) (h : S → E) :
    TotallyBounded (range (μ.withDensityᵥ h)) := by
  by_cases hh : Integrable h μ
  · exact hh.totallyBounded_range_setIntegral.subset (μ.range_withDensityᵥ_subset h)
  · simp [withDensityᵥ_of_not_integrable hh]

/-- The range of the vector measure `μ.withDensityᵥ h` is relatively compact. -/
theorem Measure.isCompact_closure_range_withDensityᵥ (μ : Measure S) (h : S → E) :
    IsCompact (closure (range (μ.withDensityᵥ h))) := by
  by_cases hh : Integrable h μ
  · exact hh.isCompact_closure_range_setIntegral.of_isClosed_subset isClosed_closure
      (closure_mono (μ.range_withDensityᵥ_subset h))
  · simp [withDensityᵥ_of_not_integrable hh]

end MeasureTheory
