/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Relative compactness of the set integrals of an integrable function

For an integrable function `h : S → E` into a real normed space, the set of its set integrals
`{∫ s in A, h s ∂μ | A : Set S}` is totally bounded, and hence relatively compact. The
consequences for the range of the vector measure `μ.withDensityᵥ h` are in
`TauCeti.MeasureTheory.VectorMeasure.WithDensity`.

Let `g` be an integrable simple function, and let `F` be the finite set of nonzero values in its
range. Each fiber `g ⁻¹' {y}` with `y ∈ F` has finite measure. The set integrals of `g` lie in the
compact image of the box `∏_{y ∈ F} [0, μ.real (g ⁻¹' {y})]` under `t ↦ ∑_{y ∈ F} t_y • y`.
A general integrable function is approximated in `L¹` by such simple functions, and the set
integrals move by at most the `L¹` distance, by `MeasureTheory.edist_setIntegral_le_eLpNorm_sub`
from `TauCeti.MeasureTheory.Integral.Bochner.Set`.

Completeness of `E` is not assumed: without it every Bochner integral vanishes, and all
statements hold trivially.

## Main declarations

* `MeasureTheory.SimpleFunc.exists_isCompact_forall_setIntegral_mem`: the set integrals of an
  integrable simple function lie in a common compact set.
* `MeasureTheory.Integrable.totallyBounded_range_setIntegral`: the set integrals of an integrable
  function form a totally bounded set.
* `MeasureTheory.Integrable.isCompact_closure_range_setIntegral`: they form a relatively compact
  set.

## References

* J. Diestel and J. J. Uhl, *Vector Measures*, Chapter II, §2, and Chapter III, §1.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure S} {h : S → E}

/-- The set integrals of an integrable simple function lie in a common compact set. Writing `F`
for the finite set of nonzero values in the range of `g`, this is the image of the box
`∏_{y ∈ F} [0, μ.real (g ⁻¹' {y})]` under `t ↦ ∑_{y ∈ F} t_y • y`. -/
theorem SimpleFunc.exists_isCompact_forall_setIntegral_mem (g : SimpleFunc S E)
    (hg : Integrable g μ) : ∃ K : Set E, IsCompact K ∧ ∀ A : Set S, ∫ s in A, g s ∂μ ∈ K := by
  classical
  by_cases hE : CompleteSpace E
  swap
  · exact ⟨{0}, isCompact_singleton,
      fun A ↦ mem_singleton_iff.mpr (integral_of_not_completeSpace hE)⟩
  let F : Finset E := {y ∈ g.range | y ≠ 0}
  refine ⟨(fun t : F → ℝ ↦ ∑ y : F, t y • (y : E)) '' Icc 0 fun y ↦ μ.real (g ⁻¹' {(y : E)}),
    isCompact_Icc.image (by fun_prop), fun A ↦ ⟨fun y ↦ (μ.restrict A).real (g ⁻¹' {(y : E)}),
    mem_Icc.mpr ⟨fun _ ↦ measureReal_nonneg, fun y ↦ ?_⟩, ?_⟩⟩
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
  refine mem_iUnion₂.2 ⟨y, hyt, Metric.mem_eball.mpr ?_⟩
  calc edist (∫ s in A, h s ∂μ) y ≤ edist (∫ s in A, h s ∂μ) (∫ s in A, g s ∂μ) + edist _ y :=
        edist_triangle _ _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add
        ((edist_setIntegral_le_eLpNorm_sub hh hg A).trans_lt hhg) (Metric.mem_eball.mp hy)
    _ = ε := ENNReal.add_halves ε

/-- The set integrals `∫ s in A, h s ∂μ` of an integrable function `h`, over all sets `A`, form a
relatively compact set. -/
theorem Integrable.isCompact_closure_range_setIntegral (hh : Integrable h μ) :
    IsCompact (closure (range fun A : Set S ↦ ∫ s in A, h s ∂μ)) := by
  by_cases hE : CompleteSpace E
  · exact hh.totallyBounded_range_setIntegral.closure.isCompact_of_isClosed isClosed_closure
  · simp [integral_of_not_completeSpace hE]

end MeasureTheory
