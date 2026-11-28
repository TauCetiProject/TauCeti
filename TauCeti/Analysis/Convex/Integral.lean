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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalAverage

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

/-! ### Midpoint Jensen's inequality for interval integrals -/

private lemma ConvexOn.sub_mul_le_intervalIntegral_of_continuousOn {g : ℝ → ℝ} {a b : ℝ}
    (hg : ConvexOn ℝ (Set.Icc a b) g) (hgc : ContinuousOn g (Set.Icc a b)) (hab : a ≤ b) :
    (b - a) * g ((a + b) / 2) ≤ ∫ x in a..b, g x := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  have hpos : 0 < b - a := sub_pos.mpr hlt
  have hμ : volume (Set.uIoc a b) = ENNReal.ofReal (b - a) := by
    rw [Set.uIoc_of_le hab, Real.volume_Ioc]
  have h0 : volume (Set.uIoc a b) ≠ 0 := by simp [hμ, hlt]
  have htop : volume (Set.uIoc a b) ≠ ∞ := by simp [hμ]
  have hsub : Set.uIoc a b ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hab]
    exact Set.Ioc_subset_Icc_self
  have hfs : ∀ᵐ x ∂volume.restrict (Set.uIoc a b), (id x : ℝ) ∈ Set.Icc a b :=
    (ae_restrict_mem measurableSet_uIoc).mono fun _ hx ↦ hsub hx
  have hid_int : IntegrableOn id (Set.uIoc a b) :=
    continuous_id.continuousOn.integrableOn_Icc.mono_set hsub
  have hg_int : IntegrableOn (g ∘ id) (Set.uIoc a b) :=
    hgc.integrableOn_Icc.mono_set hsub
  have hj := hg.map_set_average_le hgc isClosed_Icc h0 htop hfs hid_int hg_int
  have havg_id : ⨍ x in Set.uIoc a b, id x = (a + b) / 2 := by
    rw [interval_average_eq id a b, smul_eq_mul, show (∫ x in a..b, id x) = ∫ x in a..b, x from rfl,
      integral_id]
    field_simp [hpos.ne']
    ring
  rw [havg_id, show (⨍ x in Set.uIoc a b, g (id x)) = ⨍ x in a..b, g x from rfl,
    interval_average_eq g a b, smul_eq_mul] at hj
  exact (le_inv_mul_iff₀ hpos).mp hj

private lemma ConvexOn.norm_le_on_Ioo {g : ℝ → ℝ} {a b : ℝ} (hg : ConvexOn ℝ (Set.Icc a b) g)
    (hab : a < b) :
    ∃ C : ℝ, ∀ x ∈ Set.Ioo a b, ‖g x‖ ≤ C := by
  let M : ℝ := max (g a) (g b)
  refine ⟨max |M| |2 * g ((a + b) / 2) - M|, fun x hx ↦ ?_⟩
  have hupper (y : ℝ) (hy : y ∈ Set.Ioo a b) : g y ≤ M := by
    have hba : 0 < b - a := sub_pos.mpr hab
    have h1 : 0 ≤ (b - y) / (b - a) := div_nonneg (sub_nonneg.mpr hy.2.le) hba.le
    have h2 : 0 ≤ (y - a) / (b - a) := div_nonneg (sub_nonneg.mpr hy.1.le) hba.le
    have hsum : (b - y) / (b - a) + (y - a) / (b - a) = 1 := by field_simp [hba.ne']; ring
    have hcomb : ((b - y) / (b - a)) • a + ((y - a) / (b - a)) • b = y := by
      rw [smul_eq_mul, smul_eq_mul]; field_simp [hba.ne']; ring
    have hconv := hg.2 (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le) h1 h2 hsum
    rw [hcomb, smul_eq_mul, smul_eq_mul] at hconv
    calc
      g y ≤ (b - y) / (b - a) * g a + (y - a) / (b - a) * g b := hconv
      _ ≤ (b - y) / (b - a) * M + (y - a) / (b - a) * M := by
          gcongr <;> [exact le_max_left _ _; exact le_max_right _ _]
      _ = ((b - y) / (b - a) + (y - a) / (b - a)) * M := by ring
      _ = M := by rw [hsum, one_mul]
  have hy' : a + b - x ∈ Set.Ioo a b := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hmid := hg.2 (Set.Ioo_subset_Icc_self hx) (Set.Ioo_subset_Icc_self hy')
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [smul_eq_mul, smul_eq_mul, show (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * (a + b - x) =
    (a + b) / 2 by ring, smul_eq_mul, smul_eq_mul] at hmid
  have hgx_le : g x ≤ M := hupper x hx
  have hgx_ge : 2 * g ((a + b) / 2) - M ≤ g x := by linarith [hupper (a + b - x) hy']
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by
      linarith [neg_abs_le (2 * g ((a + b) / 2) - M),
        le_max_right |M| |2 * g ((a + b) / 2) - M|],
    by linarith [le_abs_self M, le_max_left |M| |2 * g ((a + b) / 2) - M|]⟩

private lemma tendsto_integral_shrink {g : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hcont : ContinuousOn g (Set.Ioo a b)) (hC : ∀ x ∈ Set.Ioo a b, ‖g x‖ ≤ C) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ x in (a + (b - a) / (n + 3))..(b - (b - a) / (n + 3)), g x)
      Filter.atTop (nhds (∫ x in a..b, g x)) := by
  let d : ℕ → ℝ := fun n ↦ (b - a) / (n + 3)
  let u : ℕ → ℝ := fun n ↦ a + d n
  let v : ℕ → ℝ := fun n ↦ b - d n
  have hd_pos (n : ℕ) : 0 < d n := div_pos (sub_pos.mpr hab) (by positivity)
  have huv_le (n : ℕ) : u n ≤ v n := by
    have : 2 * d n ≤ b - a := by
      dsimp only [d]; rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [hab]
    dsimp only [u, v]; linarith
  have hsub (n : ℕ) : Set.Ioc (u n) (v n) ⊆ Set.Ioo a b := fun _ hx ↦
    ⟨lt_trans (by linarith [hd_pos n]) hx.1, lt_of_le_of_lt hx.2 (by linarith [hd_pos n])⟩
  have hint_eq (n : ℕ) :
      ∫ x in u n..v n, g x = ∫ x, (Set.Ioc (u n) (v n)).indicator g x := by
    rw [intervalIntegral.integral_of_le (huv_le n),
      MeasureTheory.integral_indicator measurableSet_Ioc]
  have h0 : Filter.Tendsto d Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop)
  change Filter.Tendsto (fun n : ℕ ↦ ∫ x in u n..v n, g x) Filter.atTop (nhds (∫ x in a..b, g x))
  simp_rw [hint_eq]
  rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← MeasureTheory.integral_indicator measurableSet_Ioo]
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := (Set.Ioo a b).indicator (fun _ ↦ C)) ?_ ?_ ?_ ?_
  · exact fun n ↦ (aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr
      ((hcont.mono (hsub n)).aestronglyMeasurable measurableSet_Ioc)
  · exact integrableOn_const (by simp [Real.volume_Ioo]) |>.integrable_indicator measurableSet_Ioo
  · refine fun n ↦ Filter.Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ Set.Ioc (u n) (v n)
    · simpa [hx, hsub n hx] using hC x (hsub n hx)
    · have hC0 : 0 ≤ C := (norm_nonneg (g ((a + b) / 2))).trans
        (hC ((a + b) / 2) ⟨by linarith, by linarith⟩)
      by_cases hx' : x ∈ Set.Ioo a b <;> simp [hx, hx', hC0]
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ Set.Ioo a b
    · have hu_lim : Filter.Tendsto u Filter.atTop (nhds a) := by
        simpa [u] using tendsto_const_nhds.add h0
      have hv_lim : Filter.Tendsto v Filter.atTop (nhds b) := by
        simpa [v] using tendsto_const_nhds.sub h0
      have hev : ∀ᶠ n : ℕ in Filter.atTop, x ∈ Set.Ioc (u n) (v n) :=
        (hu_lim.eventually_lt_const hx.1).and (hv_lim (Ici_mem_nhds hx.2))
      simp only [Set.indicator_of_mem hx]
      exact tendsto_const_nhds.congr' (hev.mono fun n hn ↦ by simp [hn])
    · refine tendsto_const_nhds.congr fun n ↦ ?_
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem fun h ↦ hx (hsub n h)]

/-- **Midpoint Jensen's inequality** (left Hermite–Hadamard inequality) on `[a, b]`: for `a ≤ b`
and a function `g : ℝ → ℝ` convex on `[a, b]`,
`(b - a) * g ((a + b) / 2) ≤ ∫ x in a..b, g x`. -/
theorem ConvexOn.sub_mul_le_intervalIntegral {g : ℝ → ℝ} {a b : ℝ}
    (hg : ConvexOn ℝ (Set.Icc a b) g) (hab : a ≤ b) :
    (b - a) * g ((a + b) / 2) ≤ ∫ x in a..b, g x := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  let u : ℕ → ℝ := fun n ↦ a + (b - a) / (n + 3)
  let v : ℕ → ℝ := fun n ↦ b - (b - a) / (n + 3)
  have hu_gt (n : ℕ) : a < u n := by
    have : 0 < (b - a) / ((n : ℝ) + 3) := div_pos (sub_pos.mpr hlt) (by positivity)
    dsimp only [u]; linarith
  have hv_lt (n : ℕ) : v n < b := by
    have : 0 < (b - a) / ((n : ℝ) + 3) := div_pos (sub_pos.mpr hlt) (by positivity)
    dsimp only [v]; linarith
  have huv_le (n : ℕ) : u n ≤ v n := by
    have hstep : 2 * ((b - a) / ((n : ℝ) + 3)) ≤ b - a := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [sub_pos.mpr hlt]
    dsimp only [u, v]; linarith
  have hcont_Ioo : ContinuousOn g (Set.Ioo a b) := by
    simpa only [interior_Icc] using ConvexOn.continuousOn_interior hg
  have hstep (n : ℕ) : (v n - u n) * g ((a + b) / 2) ≤ ∫ x in u n..v n, g x := by
    have hmid : (u n + v n) / 2 = (a + b) / 2 := by dsimp only [u, v]; ring
    have hsub : Set.Icc (u n) (v n) ⊆ Set.Ioo a b :=
      fun _ hx ↦ ⟨(hu_gt n).trans_le hx.1, hx.2.trans_lt (hv_lt n)⟩
    rw [← hmid]
    exact (hg.subset (Set.Icc_subset_Icc (hu_gt n).le (hv_lt n).le)
      (convex_Icc _ _)).sub_mul_le_intervalIntegral_of_continuousOn
        (hcont_Ioo.mono hsub) (huv_le n)
  obtain ⟨C, hC⟩ := hg.norm_le_on_Ioo hlt
  have h0 : Filter.Tendsto (fun n : ℕ ↦ (b - a) / ((n : ℝ) + 3)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop)
  have heq (n : ℕ) : v n - u n = (b - a) - 2 * ((b - a) / ((n : ℝ) + 3)) := by
    dsimp only [u, v]; ring
  have hlim_lhs : Filter.Tendsto (fun n : ℕ ↦ (v n - u n) * g ((a + b) / 2)) Filter.atTop
      (nhds ((b - a) * g ((a + b) / 2))) :=
    (by simpa [heq] using tendsto_const_nhds.sub (h0.const_mul 2) :
      Filter.Tendsto (fun n : ℕ ↦ v n - u n) Filter.atTop (nhds (b - a))).mul_const _
  exact le_of_tendsto_of_tendsto' hlim_lhs (tendsto_integral_shrink hlt hcont_Ioo hC) hstep
