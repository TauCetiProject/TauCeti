/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import TauCeti.Geometry.Euclidean.Volume.Measure
public import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Eilenberg's inequality

Let `f : X → Y` be `K`-Lipschitz on a set `A` of an extended metric space, where `Y` is a real
normed space of finite dimension `m` carrying an additive Haar measure `μ`. For `t ≥ 0`,
**Eilenberg's inequality** (the coarea inequality) bounds the Hausdorff measures of the fibers
of `f` on average:

`∫* μH[t] (A ∩ f ⁻¹' {y}) dμ(y) ≤ μ (ball 0 1) * K ^ m * μH[m + t] A`.

No measurability of `A`, of the fibers, or of the fiber-measure function is assumed. The
integral on the left is an upper integral: we produce a measurable majorant of
`y ↦ μH[t] (A ∩ f ⁻¹' {y})` with integral bounded by the right-hand side. Consequently, if
`μH[m + t] A = 0` then almost every fiber is `μH[t]`-null, and if `μH[m + t] A < ∞` then almost
every fiber has finite `μH[t]` measure. These are the exceptional-set statements used in the
proof of the coarea formula, where `X` is `n`-dimensional, `t = n - m`, and `μ` is Lebesgue
measure. We also give them for the Euclidean-normalized Hausdorff measures `μHE[k]`.

The constant is not sharp: it comes from enclosing a set of diameter `d` in a ball of radius
`d`, whereas the isodiametric inequality would give the optimal constant.

## The argument

Cover `A` by sets `c i` of diameter at most `δ` whose `(m + t)`-dimensional Hausdorff sum is
close to `μH[m + t] A`. For every `y`, the sets `c i ∩ A ∩ f ⁻¹' {y}` cover the fiber over `y`,
so its `δ`-approximate `t`-dimensional Hausdorff content is at most
`∑ i, ediam (c i ∩ A) ^ t * 1[y ∈ closure (f '' (c i ∩ A))]`. The closure of
`f '' (c i ∩ A)` has diameter at most `K * ediam (c i ∩ A)`, hence measure at most
`μ (ball 0 1) * (K * ediam (c i ∩ A)) ^ m`, so the integral of this majorant is at most
`μ (ball 0 1) * K ^ m * ∑ i, ediam (c i) ^ (m + t)`. Letting `δ → 0`, Fatou's lemma bounds the
integral of the lower limit of the majorants.

## Main declarations

* `LipschitzOnWith.exists_measurable_hausdorffMeasure_inter_preimage_le`: Eilenberg's inequality
  with a measurable majorant of the fiber measures.
* `LipschitzOnWith.lintegral_hausdorffMeasure_inter_preimage_le`: the integral form.
* `LipschitzOnWith.ae_hausdorffMeasure_inter_preimage_eq_zero` and
  `LipschitzOnWith.ae_hausdorffMeasure_inter_preimage_lt_top`: almost every fiber is null,
  respectively of finite measure, under the corresponding hypothesis on `A`.
* `LipschitzOnWith.ae_euclideanHausdorffMeasure_inter_preimage_eq_zero` and
  `LipschitzOnWith.ae_euclideanHausdorffMeasure_inter_preimage_lt_top`: the same for `μHE`.

## References

* H. Federer, *Geometric Measure Theory*, 2.10.25.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §3.4.1 (the coarea formula, preliminaries).
-/

public section

open MeasureTheory Measure Metric Set Filter Module
open scoped ENNReal NNReal

variable {X Y : Type*} [EMetricSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y]
  [BorelSpace Y] (μ : Measure Y) [μ.IsAddHaarMeasure] {K : ℝ≥0} {f : X → Y} {A : Set X} {t : ℝ}

namespace LipschitzOnWith

/-- A single countable cover `c` of `A` yields a measurable function dominating, at every `y`,
the approximate `t`-dimensional Hausdorff content of the fiber over `y` at every scale bounding
the diameters of the cover. Its integral is controlled by the `(m + t)`-dimensional sum of the
cover. -/
private lemma exists_measurable_of_cover (hf : LipschitzOnWith K f A) (ht : 0 ≤ t)
    (c : ℕ → Set X) (hc : A ⊆ ⋃ n, c n) :
    ∃ G : Y → ℝ≥0∞, Measurable G ∧
      (∀ y r, (∀ n, ediam (c n) ≤ r) →
        ⨅ (u : ℕ → Set X) (_ : A ∩ f ⁻¹' {y} ⊆ ⋃ n, u n) (_ : ∀ n, ediam (u n) ≤ r),
          ∑' n, ⨆ _ : (u n).Nonempty, ediam (u n) ^ t ≤ G y) ∧
      ∫⁻ y, G y ∂μ ≤ μ (ball 0 1) * K ^ finrank ℝ Y *
        ∑' n, ⨆ _ : (c n).Nonempty, ediam (c n) ^ ((finrank ℝ Y : ℝ) + t) := by
  have hmeas (n : ℕ) : Measurable ((closure (f '' (c n ∩ A))).indicator
      fun _ ↦ ediam (c n ∩ A) ^ t) :=
    measurable_const.indicator isClosed_closure.measurableSet
  refine ⟨fun y ↦ ∑' n, (closure (f '' (c n ∩ A))).indicator (fun _ ↦ ediam (c n ∩ A) ^ t) y,
    Measurable.tsum hmeas, fun y r hr ↦ ?_, ?_⟩
  · refine iInf₂_le_of_le (fun n ↦ c n ∩ A ∩ f ⁻¹' {y}) (fun x hx ↦ ?_) <| iInf_le_of_le
      (fun n ↦ (ediam_mono (inter_subset_left.trans inter_subset_left)).trans (hr n)) ?_
    · obtain ⟨n, hn⟩ := mem_iUnion.1 (hc hx.1)
      exact mem_iUnion.2 ⟨n, ⟨hn, hx.1⟩, hx.2⟩
    · refine ENNReal.tsum_le_tsum fun n ↦ iSup_le fun hne ↦ ?_
      obtain ⟨x, hx, hfx⟩ := hne
      rw [indicator_of_mem (subset_closure (show y ∈ f '' (c n ∩ A) from ⟨x, hx, hfx⟩))]
      exact ENNReal.rpow_le_rpow (ediam_mono inter_subset_left) ht
  · rw [lintegral_tsum fun n ↦ (hmeas n).aemeasurable, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun n ↦ ?_
    rw [lintegral_indicator_const isClosed_closure.measurableSet]
    rcases (c n ∩ A).eq_empty_or_nonempty with h | h
    · simp [h]
    calc ediam (c n ∩ A) ^ t * μ (closure (f '' (c n ∩ A)))
        ≤ ediam (c n ∩ A) ^ t *
            (μ (ball 0 1) * K ^ finrank ℝ Y * ediam (c n ∩ A) ^ finrank ℝ Y) := by
          gcongr
          exact addHaar_closure_image_le_mul_ediam_pow μ (hf.mono inter_subset_right)
      _ = μ (ball 0 1) * K ^ finrank ℝ Y * ediam (c n ∩ A) ^ ((finrank ℝ Y : ℝ) + t) := by
          rw [ENNReal.rpow_add_of_nonneg _ _ (Nat.cast_nonneg _) ht, ENNReal.rpow_natCast]
          ring
      _ ≤ _ := by
          rw [iSup_pos (h.mono inter_subset_left)]
          gcongr
          exact inter_subset_left

omit [BorelSpace Y] in
/-- The constant in Eilenberg's inequality is finite. -/
private lemma constant_ne_top (K : ℝ≥0) : μ (ball 0 1) * K ^ finrank ℝ Y ≠ ∞ :=
  ENNReal.mul_ne_top measure_ball_lt_top.ne (ENNReal.pow_ne_top ENNReal.coe_ne_top)

variable [MeasurableSpace X] [BorelSpace X]

/-- Eilenberg's inequality when `μH[m + t] A` is finite: use covers of mesh `1 / k` whose
Hausdorff sums are within `1 / k` of `μH[m + t] A`, and take the lower limit of the
corresponding majorants. -/
private lemma exists_measurable_of_ne_top (hf : LipschitzOnWith K f A) (ht : 0 ≤ t)
    (hA : μH[finrank ℝ Y + t] A ≠ ∞) :
    ∃ G : Y → ℝ≥0∞, Measurable G ∧ (∀ y, μH[t] (A ∩ f ⁻¹' {y}) ≤ G y) ∧
      ∫⁻ y, G y ∂μ ≤ μ (ball 0 1) * K ^ finrank ℝ Y * μH[finrank ℝ Y + t] A := by
  have hpos (k : ℕ) : 0 < (k : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.2 (ENNReal.natCast_ne_top k)
  have hcov (k : ℕ) : ∃ c : ℕ → Set X, A ⊆ ⋃ n, c n ∧ (∀ n, ediam (c n) ≤ (k : ℝ≥0∞)⁻¹) ∧
      ∑' n, ⨆ _ : (c n).Nonempty, ediam (c n) ^ ((finrank ℝ Y : ℝ) + t) <
        μH[finrank ℝ Y + t] A + (k : ℝ≥0∞)⁻¹ := by
    have h := (le_iSup₂ (f := fun r (_ : 0 < r) ↦
      ⨅ (c : ℕ → Set X) (_ : A ⊆ ⋃ n, c n) (_ : ∀ n, ediam (c n) ≤ r),
        ∑' n, ⨆ _ : (c n).Nonempty, ediam (c n) ^ ((finrank ℝ Y : ℝ) + t)) _ (hpos k)).trans_eq
      (hausdorffMeasure_apply _ A).symm
    obtain ⟨c, hc⟩ := iInf_lt_iff.1 (h.trans_lt (ENNReal.lt_add_right hA (hpos k).ne'))
    obtain ⟨hcA, hc⟩ := iInf_lt_iff.1 hc
    obtain ⟨hcr, hc⟩ := iInf_lt_iff.1 hc
    exact ⟨c, hcA, hcr, hc⟩
  choose c hcA hcr hcsum using hcov
  choose G hGm hGle hGint using fun k ↦ exists_measurable_of_cover μ hf ht (c k) (hcA k)
  refine ⟨fun y ↦ liminf (fun k ↦ G k y) atTop, Measurable.liminf hGm, fun y ↦ ?_, ?_⟩
  · rw [hausdorffMeasure_apply]
    refine iSup₂_le fun r hr ↦ le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [(tendsto_order.1 ENNReal.tendsto_inv_nat_nhds_zero).2 r hr] with k hk
    exact hGle k y r fun n ↦ (hcr k n).trans hk.le
  calc ∫⁻ y, liminf (fun k ↦ G k y) atTop ∂μ ≤ liminf (fun k ↦ ∫⁻ y, G k y ∂μ) atTop :=
        lintegral_liminf_le hGm
    _ ≤ liminf (fun k : ℕ ↦ μ (ball 0 1) * K ^ finrank ℝ Y *
          (μH[finrank ℝ Y + t] A + (k : ℝ≥0∞)⁻¹)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun k ↦
          (hGint k).trans (by gcongr; exact (hcsum k).le))
    _ = μ (ball 0 1) * K ^ finrank ℝ Y * μH[finrank ℝ Y + t] A := by
        refine Tendsto.liminf_eq ?_
        simpa using ENNReal.Tendsto.const_mul
          (tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero)
          (Or.inr (constant_ne_top μ K))

/-- **Eilenberg's inequality**, in its strong form. If `f` is `K`-Lipschitz on a set `A` with
values in an `m`-dimensional real normed space with additive Haar measure `μ`, and `t ≥ 0`, then
the fiber measures `y ↦ μH[t] (A ∩ f ⁻¹' {y})` have a measurable majorant whose integral is at
most `μ (ball 0 1) * K ^ m * μH[m + t] A`. In other words, the upper integral of the fiber
measures obeys this bound. Neither `A` nor the fibers need be measurable. -/
theorem exists_measurable_hausdorffMeasure_inter_preimage_le (hf : LipschitzOnWith K f A)
    (ht : 0 ≤ t) :
    ∃ G : Y → ℝ≥0∞, Measurable G ∧ (∀ y, μH[t] (A ∩ f ⁻¹' {y}) ≤ G y) ∧
      ∫⁻ y, G y ∂μ ≤ μ (ball 0 1) * K ^ finrank ℝ Y * μH[finrank ℝ Y + t] A := by
  by_cases hA : μH[finrank ℝ Y + t] A ≠ ∞
  · exact exists_measurable_of_ne_top μ hf ht hA
  rw [not_ne_iff] at hA
  -- Infinite measure: dominate by `∞` on the closure of the image, which is null when the
  -- constant vanishes, that is, when `f` is constant on `A` and `m ≠ 0`.
  refine ⟨(closure (f '' A)).indicator fun _ ↦ ∞,
    measurable_const.indicator isClosed_closure.measurableSet, fun y ↦ ?_, ?_⟩
  · by_cases hy : y ∈ closure (f '' A)
    · simp [indicator_of_mem hy]
    · have : A ∩ f ⁻¹' {y} = ∅ :=
        eq_empty_of_forall_notMem fun x hx ↦
          hy (subset_closure (show y ∈ f '' A from ⟨x, hx.1, hx.2⟩))
      simp [this]
  · rw [lintegral_indicator_const isClosed_closure.measurableSet, hA]
    rcases eq_or_ne (μ (ball 0 1) * K ^ finrank ℝ Y) 0 with hC | hC
    · have h0 : μ (closure (f '' A)) = 0 := by
        simpa [hC] using addHaar_closure_image_le_mul_ediam_pow μ hf
      simp [h0]
    · rw [ENNReal.mul_top hC]
      exact le_top
/-- **Eilenberg's inequality**: for `f` `K`-Lipschitz on `A` with values in an `m`-dimensional
real normed space with additive Haar measure `μ`, and `t ≥ 0`,
`∫⁻ y, μH[t] (A ∩ f ⁻¹' {y}) ∂μ ≤ μ (ball 0 1) * K ^ m * μH[m + t] A`.
See `LipschitzOnWith.exists_measurable_hausdorffMeasure_inter_preimage_le` for the stronger
upper-integral form, which does not require measurability of the integrand. -/
theorem lintegral_hausdorffMeasure_inter_preimage_le (hf : LipschitzOnWith K f A) (ht : 0 ≤ t) :
    ∫⁻ y, μH[t] (A ∩ f ⁻¹' {y}) ∂μ ≤
      μ (ball 0 1) * K ^ finrank ℝ Y * μH[finrank ℝ Y + t] A := by
  obtain ⟨G, -, hle, hint⟩ := hf.exists_measurable_hausdorffMeasure_inter_preimage_le μ ht
  exact (lintegral_mono hle).trans hint

/-- If `f` is Lipschitz on `A` with values in an `m`-dimensional real normed space and
`μH[m + t] A = 0`, then for almost every `y` the fiber `A ∩ f ⁻¹' {y}` is `μH[t]`-null. -/
theorem ae_hausdorffMeasure_inter_preimage_eq_zero (hf : LipschitzOnWith K f A) (ht : 0 ≤ t)
    (hA : μH[finrank ℝ Y + t] A = 0) : ∀ᵐ y ∂μ, μH[t] (A ∩ f ⁻¹' {y}) = 0 := by
  obtain ⟨G, hGm, hle, hint⟩ := hf.exists_measurable_hausdorffMeasure_inter_preimage_le μ ht
  rw [hA, mul_zero, nonpos_iff_eq_zero, lintegral_eq_zero_iff hGm] at hint
  filter_upwards [hint] with y hy
  exact nonpos_iff_eq_zero.1 ((hle y).trans_eq hy)

/-- If `f` is Lipschitz on `A` with values in an `m`-dimensional real normed space and
`μH[m + t] A < ∞`, then for almost every `y` the fiber `A ∩ f ⁻¹' {y}` has finite `μH[t]`
measure. -/
theorem ae_hausdorffMeasure_inter_preimage_lt_top (hf : LipschitzOnWith K f A) (ht : 0 ≤ t)
    (hA : μH[finrank ℝ Y + t] A ≠ ∞) : ∀ᵐ y ∂μ, μH[t] (A ∩ f ⁻¹' {y}) < ∞ := by
  obtain ⟨G, hGm, hle, hint⟩ := hf.exists_measurable_hausdorffMeasure_inter_preimage_le μ ht
  filter_upwards [ae_lt_top hGm
    (hint.trans_lt (ENNReal.mul_lt_top (constant_ne_top μ K).lt_top hA.lt_top)).ne]
    with y hy
  exact (hle y).trans_lt hy

/-- If `f` is Lipschitz on `A` with values in an `m`-dimensional real normed space and
`μHE[m + k] A = 0`, then for almost every `y` the fiber `A ∩ f ⁻¹' {y}` is `μHE[k]`-null. -/
theorem ae_euclideanHausdorffMeasure_inter_preimage_eq_zero (hf : LipschitzOnWith K f A)
    {k : ℕ} (hA : μHE[finrank ℝ Y + k] A = 0) : ∀ᵐ y ∂μ, μHE[k] (A ∩ f ⁻¹' {y}) = 0 := by
  rw [euclideanHausdorffMeasure_eq_zero_iff, Nat.cast_add] at hA
  filter_upwards [hf.ae_hausdorffMeasure_inter_preimage_eq_zero μ k.cast_nonneg hA] with y hy
  exact euclideanHausdorffMeasure_eq_zero_iff.2 hy

/-- If `f` is Lipschitz on `A` with values in an `m`-dimensional real normed space and
`μHE[m + k] A < ∞`, then for almost every `y` the fiber `A ∩ f ⁻¹' {y}` has finite `μHE[k]`
measure. -/
theorem ae_euclideanHausdorffMeasure_inter_preimage_lt_top (hf : LipschitzOnWith K f A)
    {k : ℕ} (hA : μHE[finrank ℝ Y + k] A ≠ ∞) : ∀ᵐ y ∂μ, μHE[k] (A ∩ f ⁻¹' {y}) < ∞ := by
  rw [← lt_top_iff_ne_top, euclideanHausdorffMeasure_lt_top_iff, Nat.cast_add,
    lt_top_iff_ne_top] at hA
  filter_upwards [hf.ae_hausdorffMeasure_inter_preimage_lt_top μ k.cast_nonneg hA] with y hy
  exact euclideanHausdorffMeasure_lt_top_iff.2 hy

end LipschitzOnWith
