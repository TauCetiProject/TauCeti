/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Convex.Continuous
import TauCeti.Analysis.Convex.Function.Basic

/-!
# Jensen's inequality for semicontinuous functions and closed convex hulls

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
* `ConvexOn.intervalIntegrable`: a real function convex on `uIcc a b` is interval integrable on
  `a..b`.
* `ConvexOn.sub_mul_le_intervalIntegral`: midpoint Jensen's inequality (left Hermite–Hadamard
  inequality) for a convex function on `[a, b]`.

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

/-! ### Interval integrability and midpoint Jensen's inequality -/

/-- A real-valued function convex on `uIcc a b` is interval integrable on `a..b` with respect
to Lebesgue measure. -/
theorem ConvexOn.intervalIntegrable {g : ℝ → ℝ} {a b : ℝ} (hg : ConvexOn ℝ (Set.uIcc a b) g) :
    IntervalIntegrable g volume a b := by
  wlog hab : a ≤ b generalizing a b
  · rw [Set.uIcc_comm] at hg
    exact (this hg (le_of_not_ge hab)).symm
  rw [Set.uIcc_of_le hab] at hg
  obtain ⟨C, hC⟩ := hg.norm_le_on_Ioo
  have hcont : ContinuousOn g (Set.Ioo a b) := by
    simpa only [interior_Icc] using hg.continuousOn_interior
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 <|
    (integrableOn_Icc_iff_integrableOn_Ioo).2 <|
      IntegrableOn.of_bound measure_Ioo_lt_top
        (hcont.aestronglyMeasurable measurableSet_Ioo) C
        (ae_restrict_of_forall_mem measurableSet_Ioo hC)

/-- **Midpoint Jensen's inequality** (left Hermite–Hadamard inequality) on `[a, b]`: for `a ≤ b`
and a function `g : ℝ → ℝ` convex on `[a, b]`,
`(b - a) * g ((a + b) / 2) ≤ ∫ x in a..b, g x`. -/
theorem ConvexOn.sub_mul_le_intervalIntegral {g : ℝ → ℝ} {a b : ℝ}
    (hg : ConvexOn ℝ (Set.Icc a b) g) (hab : a ≤ b) :
    (b - a) * g ((a + b) / 2) ≤ ∫ x in a..b, g x := by
  have hg_int : IntervalIntegrable g volume a b := (Set.uIcc_of_le hab ▸ hg).intervalIntegrable
  have hg_ref_int : IntervalIntegrable (fun x ↦ g (a + b - x)) volume a b := by
    simpa only [add_sub_cancel_left, add_sub_cancel_right] using
      (hg_int.comp_sub_left (a + b)).symm
  have hmono := intervalIntegral.integral_mono_on hab intervalIntegrable_const
    (hg_int.add hg_ref_int) fun x hx ↦ hg.two_mul_add_div_two_le hx
  have hconst : ∫ _ in a..b, 2 * g ((a + b) / 2) = 2 * ((b - a) * g ((a + b) / 2)) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have href : ∫ x in a..b, g (a + b - x) = ∫ x in a..b, g x := by
    simpa only [add_sub_cancel_left, add_sub_cancel_right] using
      intervalIntegral.integral_comp_sub_left g (a + b) (a := a) (b := b)
  rw [hconst, intervalIntegral.integral_add hg_int hg_ref_int, href, ← two_mul] at hmono
  linarith
