/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Jensen's inequality for semicontinuous functions, closed convex hulls, and logarithmic Jensen

Mathlib proves Jensen's inequality `g (⨍ x, f x ∂μ) ≤ ⨍ x, g (f x) ∂μ` for a Bochner integrable
`f : α → E` with values almost everywhere in a closed convex set `s`, and a convex function `g`
that is *continuous* on `s` (`ConvexOn.map_average_le`). This file weakens continuity to lower
semicontinuity on `s`. A convex function that is lower semicontinuous on a closed convex set need
not be continuous at its boundary, and in infinite dimensions closed convex sets often have empty
interior. For instance, on `s = {(x, y) ∈ ℝ² | y ^ 2 ≤ x ≤ 1}` the function with
`g (x, y) = y ^ 2 / x` for `x > 0` and `g (0, 0) = 0` is convex (a perspective of `y ^ 2`) and
lower semicontinuous on `s` (as `g ≥ 0 = g (0, 0)`), but not continuous at the origin, since
`g = 1` along the curve `x = y ^ 2`. Only the values of `g` on `s` matter, so a convex function
defined on `s` alone may be extended to `E` arbitrarily.

It also provides a weighted logarithmic Jensen inequality: for an almost everywhere nonnegative
integrable weight `w : Ω → ℝ` of positive total mass `∫ s, w s ∂μ = α > 0` and an almost
everywhere positive real integrand `u : Ω → ℝ` such that `u * w` and `(Real.log ∘ u) * w` are
integrable, `α⁻¹ * ∫ s, Real.log (u s) * w s ∂μ ≤ Real.log (α⁻¹ * ∫ s, u s * w s ∂μ)`.

## Implementation notes

Lower semicontinuity of `g` on the closed set `s` is exactly closedness of the epigraph
`{p | p.1 ∈ s ∧ g p.1 ≤ p.2}` (`lowerSemicontinuousOn_iff_isClosed_epigraph`), and the epigraph of
a convex function is convex, so `Convex.average_mem` applies to `x ↦ (f x, g (f x))`. Concave,
upper semicontinuous functions are treated through hypographs.

The statements, their order and the proofs are adapted from Mathlib's
`Mathlib/Analysis/Convex/Integral.lean` (`ConvexOn.average_mem_epigraph`,
`ConcaveOn.average_mem_hypograph`, `ConvexOn.map_average_le`, `ConvexOn.map_set_average_le`,
`ConvexOn.map_integral_le` and their concave counterparts), with `ContinuousOn` replaced by
semicontinuity through `lowerSemicontinuousOn_iff_isClosed_epigraph` and
`upperSemicontinuousOn_iff_isClosed_hypograph`.

## Main results

* `ConvexOn.map_average_le_of_lowerSemicontinuousOn`,
  `ConvexOn.map_setAverage_le_of_lowerSemicontinuousOn` and
  `ConvexOn.map_integral_le_of_lowerSemicontinuousOn`: Jensen's inequality for averages over a
  finite nonzero measure, for averages over a set of finite positive measure, and for integrals
  against a probability measure, for convex functions lower semicontinuous on a closed convex set.
* `ConcaveOn.le_map_average_of_upperSemicontinuousOn`,
  `ConcaveOn.le_map_setAverage_of_upperSemicontinuousOn` and
  `ConcaveOn.le_map_integral_of_upperSemicontinuousOn`: the concave counterparts.
* `MeasureTheory.Integrable.integral_mem_closedConvexHull_image`,
  `MeasureTheory.Integrable.average_mem_closedConvexHull_image` and
  `MeasureTheory.IntegrableOn.setAverage_mem_closedConvexHull_image`: an integral against a
  probability measure, or an average, lies in the closed convex hull of the values of the
  function on any set of full measure.
* `MeasureTheory.inv_mul_integral_log_mul_le`: weighted logarithmic Jensen inequality.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Springer, 2016, Propositions 1.2.11 and 1.2.12.
-/

public section

open MeasureTheory Set
open scoped ENNReal

variable {α E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure α} {s : Set E} {t : Set α} {f : α → E} {g : E → ℝ}

/-! ### Jensen's inequality for semicontinuous functions -/

/-- If `g` is convex and lower semicontinuous on a closed convex set `s`, `μ` is a finite nonzero
measure and `f` sends `μ`-almost every point to `s`, then the pair of averages of `f` and `g ∘ f`
lies in the epigraph of `g` over `s`, provided both `f` and `g ∘ f` are integrable. -/
theorem ConvexOn.average_mem_epigraph_of_lowerSemicontinuousOn [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConvexOn ℝ s g) (hgc : LowerSemicontinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} :=
  average_pair hfi hgi ▸ hg.convex_epigraph.average_mem
    ((lowerSemicontinuousOn_iff_isClosed_epigraph hsc).1 hgc)
    (hfs.mono fun _ hx ↦ ⟨hx, le_rfl⟩) (hfi.prodMk hgi)

/-- If `g` is concave and upper semicontinuous on a closed convex set `s`, `μ` is a finite nonzero
measure and `f` sends `μ`-almost every point to `s`, then the pair of averages of `f` and `g ∘ f`
lies in the hypograph of `g` over `s`, provided both `f` and `g ∘ f` are integrable. -/
theorem ConcaveOn.average_mem_hypograph_of_upperSemicontinuousOn [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConcaveOn ℝ s g) (hgc : UpperSemicontinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} :=
  average_pair hfi hgi ▸ hg.convex_hypograph.average_mem
    ((upperSemicontinuousOn_iff_isClosed_hypograph hsc).1 hgc)
    (hfs.mono fun _ hx ↦ ⟨hx, le_rfl⟩) (hfi.prodMk hgi)

/-- **Jensen's inequality** for lower semicontinuous functions: if `g` is convex and lower
semicontinuous on a closed convex set `s`, `μ` is a finite nonzero measure and `f` sends
`μ`-almost every point to `s`, then the value of `g` at the average of `f` is at most the average
of `g ∘ f`, provided both `f` and `g ∘ f` are integrable. -/
theorem ConvexOn.map_average_le_of_lowerSemicontinuousOn [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConvexOn ℝ s g) (hgc : LowerSemicontinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    g (⨍ x, f x ∂μ) ≤ ⨍ x, g (f x) ∂μ :=
  (hg.average_mem_epigraph_of_lowerSemicontinuousOn hgc hsc hfs hfi hgi).2

/-- **Jensen's inequality** for upper semicontinuous functions: if `g` is concave and upper
semicontinuous on a closed convex set `s`, `μ` is a finite nonzero measure and `f` sends
`μ`-almost every point to `s`, then the average of `g ∘ f` is at most the value of `g` at the
average of `f`, provided both `f` and `g ∘ f` are integrable. -/
theorem ConcaveOn.le_map_average_of_upperSemicontinuousOn [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConcaveOn ℝ s g) (hgc : UpperSemicontinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    ⨍ x, g (f x) ∂μ ≤ g (⨍ x, f x ∂μ) :=
  (hg.average_mem_hypograph_of_upperSemicontinuousOn hgc hsc hfs hfi hgi).2

/-- **Jensen's inequality** for lower semicontinuous functions and set averages: if `g` is convex
and lower semicontinuous on a closed convex set `s` and `f` sends almost every point of a set `t`
of finite positive measure to `s`, then the value of `g` at the average of `f` over `t` is at most
the average of `g ∘ f` over `t`, provided both `f` and `g ∘ f` are integrable on `t`. -/
theorem ConvexOn.map_setAverage_le_of_lowerSemicontinuousOn (hg : ConvexOn ℝ s g)
    (hgc : LowerSemicontinuousOn g s) (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞)
    (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) (hfi : IntegrableOn f t μ)
    (hgi : IntegrableOn (g ∘ f) t μ) :
    g (⨍ x in t, f x ∂μ) ≤ ⨍ x in t, g (f x) ∂μ :=
  have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hg.map_average_le_of_lowerSemicontinuousOn hgc hsc hfs hfi hgi

/-- **Jensen's inequality** for upper semicontinuous functions and set averages: if `g` is concave
and upper semicontinuous on a closed convex set `s` and `f` sends almost every point of a set `t`
of finite positive measure to `s`, then the average of `g ∘ f` over `t` is at most the value of
`g` at the average of `f` over `t`, provided both `f` and `g ∘ f` are integrable on `t`. -/
theorem ConcaveOn.le_map_setAverage_of_upperSemicontinuousOn (hg : ConcaveOn ℝ s g)
    (hgc : UpperSemicontinuousOn g s) (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞)
    (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) (hfi : IntegrableOn f t μ)
    (hgi : IntegrableOn (g ∘ f) t μ) :
    ⨍ x in t, g (f x) ∂μ ≤ g (⨍ x in t, f x ∂μ) :=
  have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hg.le_map_average_of_upperSemicontinuousOn hgc hsc hfs hfi hgi

/-- **Jensen's inequality** for lower semicontinuous functions and probability measures: if `g` is
convex and lower semicontinuous on a closed convex set `s` and `f` sends `μ`-almost every point to
`s`, then `g (∫ f) ≤ ∫ g ∘ f`, provided both `f` and `g ∘ f` are integrable. -/
theorem ConvexOn.map_integral_le_of_lowerSemicontinuousOn [IsProbabilityMeasure μ]
    (hg : ConvexOn ℝ s g) (hgc : LowerSemicontinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ := by
  simpa only [average_eq_integral] using
    hg.map_average_le_of_lowerSemicontinuousOn hgc hsc hfs hfi hgi

/-- **Jensen's inequality** for upper semicontinuous functions and probability measures: if `g` is
concave and upper semicontinuous on a closed convex set `s` and `f` sends `μ`-almost every point to
`s`, then `∫ g ∘ f ≤ g (∫ f)`, provided both `f` and `g ∘ f` are integrable. -/
theorem ConcaveOn.le_map_integral_of_upperSemicontinuousOn [IsProbabilityMeasure μ]
    (hg : ConcaveOn ℝ s g) (hgc : UpperSemicontinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    ∫ x, g (f x) ∂μ ≤ g (∫ x, f x ∂μ) := by
  simpa only [average_eq_integral] using
    hg.le_map_average_of_upperSemicontinuousOn hgc hsc hfs hfi hgi

/-! ### Closed convex hulls of the values -/

/-- The integral of an integrable function against a probability measure lies in the closed convex
hull of the values of the function on any set of full measure. -/
theorem MeasureTheory.Integrable.integral_mem_closedConvexHull_image [IsProbabilityMeasure μ]
    (hfi : Integrable f μ) (ht : ∀ᵐ x ∂μ, x ∈ t) : ∫ x, f x ∂μ ∈ closedConvexHull ℝ (f '' t) :=
  convex_closedConvexHull.integral_mem isClosed_closedConvexHull
    (ht.mono fun _ hx ↦ subset_closedConvexHull (mem_image_of_mem f hx)) hfi

/-- The average of an integrable function over a finite nonzero measure lies in the closed convex
hull of the values of the function on any set of full measure. -/
theorem MeasureTheory.Integrable.average_mem_closedConvexHull_image [IsFiniteMeasure μ]
    [NeZero μ] (hfi : Integrable f μ) (ht : ∀ᵐ x ∂μ, x ∈ t) :
    ⨍ x, f x ∂μ ∈ closedConvexHull ℝ (f '' t) :=
  convex_closedConvexHull.average_mem isClosed_closedConvexHull
    (ht.mono fun _ hx ↦ subset_closedConvexHull (mem_image_of_mem f hx)) hfi

/-- The average of a function over a null measurable set `t` of finite positive measure, on which
it is integrable, lies in the closed convex hull of its values on `t`. -/
theorem MeasureTheory.IntegrableOn.setAverage_mem_closedConvexHull_image
    (hfi : IntegrableOn f t μ) (htm : NullMeasurableSet t μ) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) :
    ⨍ x in t, f x ∂μ ∈ closedConvexHull ℝ (f '' t) :=
  convex_closedConvexHull.set_average_mem isClosed_closedConvexHull h0 ht
    ((ae_restrict_mem₀ htm).mono fun _ hx ↦ subset_closedConvexHull (mem_image_of_mem f hx)) hfi

/-! ### Weighted logarithmic Jensen inequality -/

namespace MeasureTheory

/-- **Weighted logarithmic Jensen inequality.** For an almost everywhere nonnegative integrable
weight `w : Ω → ℝ` with positive total mass `∫ s, w s ∂μ = α > 0`, and an almost everywhere
positive real integrand `u : Ω → ℝ` such that `s ↦ u s * w s` and `s ↦ Real.log (u s) * w s` are
integrable, `α⁻¹ * ∫ s, Real.log (u s) * w s ∂μ ≤ Real.log (α⁻¹ * ∫ s, u s * w s ∂μ)`. -/
theorem inv_mul_integral_log_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {u w : Ω → ℝ} {α : ℝ} (hα : 0 < α) (hu_pos : ∀ᵐ s ∂μ, 0 < u s)
    (hw_int : Integrable w μ) (hw_nonneg : 0 ≤ᵐ[μ] w) (hw_sum : ∫ s, w s ∂μ = α)
    (hu_int : Integrable (fun s ↦ u s * w s) μ)
    (hlog_int : Integrable (fun s ↦ Real.log (u s) * w s) μ) :
    α⁻¹ * ∫ s, Real.log (u s) * w s ∂μ ≤ Real.log (α⁻¹ * ∫ s, u s * w s ∂μ) := by
  have huw_nn : 0 ≤ᵐ[μ] fun s ↦ u s * w s :=
    hu_pos.mp (hw_nonneg.mono fun _ hw hu ↦ mul_nonneg hu.le hw)
  have hI : 0 < ∫ s, u s * w s ∂μ := by
    refine lt_of_le_of_ne (integral_nonneg_of_ae huw_nn) fun h0 ↦ hα.ne' ?_
    have huw0 : (fun s ↦ u s * w s) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae huw_nn hu_int).1 h0.symm
    have hw0 : w =ᵐ[μ] 0 := huw0.mp (hu_pos.mono fun _ hu h ↦ (mul_eq_zero.1 h).resolve_left hu.ne')
    exact hw_sum.symm.trans (integral_eq_zero_of_ae hw0)
  set I := ∫ s, u s * w s ∂μ
  set c := α⁻¹ * I
  have hc : 0 < c := mul_pos (inv_pos.2 hα) hI
  have hpt : ∀ᵐ s ∂μ, Real.log (u s) * w s - Real.log c * w s ≤ c⁻¹ * (u s * w s) - w s := by
    filter_upwards [hu_pos, hw_nonneg] with s hus hws
    have hlog := (Real.log_le_sub_one_of_pos (div_pos hus hc)).trans_eq (by
      rw [div_eq_inv_mul])
    rw [Real.log_div hus.ne' hc.ne'] at hlog
    have := mul_le_mul_of_nonneg_right hlog hws
    linarith
  have hint : (∫ s, Real.log (u s) * w s ∂μ) - Real.log c * α ≤ c⁻¹ * I - α := by
    have h : (∫ s, (Real.log (u s) * w s - Real.log c * w s) ∂μ) ≤
        ∫ s, (c⁻¹ * (u s * w s) - w s) ∂μ :=
      integral_mono_ae (hlog_int.sub (hw_int.const_mul _))
        ((hu_int.const_mul _).sub hw_int) hpt
    rwa [integral_sub hlog_int (hw_int.const_mul _), integral_sub (hu_int.const_mul _) hw_int,
      integral_const_mul, integral_const_mul, hw_sum] at h
  have hcI : c⁻¹ * I = α := by
    dsimp [c]
    field_simp
  rw [hcI, sub_self, sub_nonpos, mul_comm (Real.log c) α] at hint
  exact (inv_mul_le_iff₀ hα).2 hint

end MeasureTheory
