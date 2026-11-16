/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.HasLaw
public import TauCeti.Probability.ConditionalProbability
public import TauCeti.Probability.Quantile
public import TauCeti.MeasureTheory.Measure.LowerSet

/-!
# Interval truncation of real probability laws

Conditioning a real probability law `μ` on an interval retains its mass between the endpoints
and renormalizes it. This file computes the resulting cumulative distribution function and
quantile for all four finite endpoint conventions, retaining endpoint atoms. This distinction
also matters for conditioning degenerate laws, such as a Gaussian with zero variance.

Write `L` for the mass excluded at the lower end and `R` for the mass up to the upper end,
including the upper atom precisely when that endpoint is retained. The conditional cdf is

```text
(min R (max L (cdf μ x)) - L) / (R - L).
```

Consequently, at an interior level `u`, its quantile is the quantile of `μ` at the rescaled level
`L + u * (R - L)`. The strict hypothesis `L < R` says exactly that the conditioning interval has
positive mass. No atomlessness or nondegeneracy assumption on the conditional law is needed.
The underlying statements for differences of lower sets also allow unbounded cuts.

Any real affine map `x ↦ a + b * x` (including at zero slope) commutes with conditioning on the
preimage of an arbitrary event, and an invertible affine map (`b ≠ 0`) commutes with truncation by
pushing forward both the underlying measure and the conditioning event, without requiring the event
to be measurable or to have positive or finite mass. Positive slopes preserve interval and ray
endpoint flags, whereas negative slopes reverse bounded interval endpoints, exchange half-open
flags, and swap lower and upper rays.

## Main results

* `MeasureTheory.Measure.cdf_cond` — the cdf of a law conditioned on an event;
* `MeasureTheory.Measure.cdf_cond_sdiff`, `MeasureTheory.Measure.quantile_cond_sdiff` —
  truncation between lower cuts;
* `MeasureTheory.Measure.cdf_cond_Ioc`, `MeasureTheory.Measure.cdf_cond_Icc`,
  `MeasureTheory.Measure.cdf_cond_Ioo`, `MeasureTheory.Measure.cdf_cond_Ico` — finite intervals;
* `MeasureTheory.Measure.quantile_cond_Ioc`, `MeasureTheory.Measure.quantile_cond_Icc`,
  `MeasureTheory.Measure.quantile_cond_Ioo`, `MeasureTheory.Measure.quantile_cond_Ico` —
  the corresponding interior quantile formulas;
* `MeasureTheory.Measure.map_affine_cond_preimage`, `MeasureTheory.Measure.map_affine_cond`, and
  `ProbabilityTheory.HasLaw.affine_cond` — affine pushforward of truncated measures and random
  variables;
* `MeasureTheory.Measure.map_affine_cond_Icc_pos`,
  `MeasureTheory.Measure.map_affine_cond_Icc_neg`, and the corresponding `Ioo`, `Ico`, `Ioc`,
  `Ici`, `Ioi`, `Iic`, and `Iio` forms — signed affine transport of bounded intervals and
  unbounded rays.
-/

public section

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable (μ : Measure ℝ)

/-- The cdf of `μ` conditioned on an event of nonzero mass is the proportion of that event lying
below the cdf argument. -/
theorem cdf_cond [IsFiniteMeasure μ] {A : Set ℝ} (hμA : μ A ≠ 0) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ A) x = μ.real (A ∩ Iic x) / μ.real A := by
  have := ProbabilityTheory.cond_isProbabilityMeasure hμA
  simp [cdf_eq_real, measureReal_def, ProbabilityTheory.cond_apply' (measurableSet_Iic (a := x)),
    div_eq_inv_mul]

variable [IsProbabilityMeasure μ]

/-- Conditioning between two lower cuts clips and rescales the original cdf.
Taking either cut to be an open or closed ray retains its endpoint convention; the empty and
universal cuts also allow unbounded truncations. -/
theorem cdf_cond_sdiff {A B : Set ℝ} (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hLR : μ.real A < μ.real B) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ (B \ A)) x =
      (min (μ.real B) (max (μ.real A) (cdf μ x)) - μ.real A) /
        (μ.real B - μ.real A) := by
  have hmA : MeasurableSet A := hA.ordConnected.measurableSet
  have hmass : μ.real (B \ A) = μ.real B - μ.real A := by
    rw [μ.measureReal_sdiff_of_isLowerSet hB hA hmA, max_eq_left (sub_nonneg.mpr hLR.le)]
  have hne : μ (B \ A) ≠ 0 := by
    rw [← measureReal_ne_zero_iff, hmass]
    exact (sub_pos.mpr hLR).ne'
  have hinter : (B \ A) ∩ Iic x = (B ∩ Iic x) \ A := inter_sdiff_right_comm.symm
  rw [cdf_cond μ hne, hinter, hmass,
    μ.measureReal_sdiff_of_isLowerSet (hB.inter (IsLowerSet.Iic x)) hA hmA,
    μ.measureReal_inter_of_isLowerSet hB (IsLowerSet.Iic x), ← cdf_eq_real]
  congr 1
  rw [min_max_distrib_left, min_eq_right hLR.le, ← max_sub_sub_right, sub_self, max_comm]

/-- At an interior level, conditioning between two lower cuts amounts to an affine
rescaling of the source quantile's probability level. Atoms and flat cdf intervals are allowed. -/
theorem quantile_cond_sdiff {A B : Set ℝ} (hA : IsLowerSet A) (hB : IsLowerSet B)
    (hLR : μ.real A < μ.real B)
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (ProbabilityTheory.cond μ (B \ A)).quantile u =
      μ.quantile (μ.real A + u * (μ.real B - μ.real A)) := by
  let L := μ.real A
  let R := μ.real B
  have hD : 0 < R - L := sub_pos.mpr hLR
  have hqL : L < L + u * (R - L) := by
    nlinarith [mul_pos hu.1 hD]
  have hqR : L + u * (R - L) < R := by
    nlinarith [hu.2]
  -- Compare levels on each side of the clipping thresholds, so that neither continuity nor
  -- strict increase of the source cdf is needed.
  have hlevel (x : ℝ) :
      u ≤ cdf (ProbabilityTheory.cond μ (B \ A)) x ↔
        L + u * (R - L) ≤ cdf μ x := by
    rw [cdf_cond_sdiff μ hA hB hLR]
    by_cases hxL : cdf μ x ≤ L
    · rw [max_eq_left hxL, min_eq_right hLR.le, sub_self, zero_div]
      constructor <;> intro h <;> linarith [hu.1, hqL]
    · have hLx : L ≤ cdf μ x := (not_le.mp hxL).le
      by_cases hRx : R ≤ cdf μ x
      · rw [max_eq_right hLx, min_eq_left hRx, div_self hD.ne']
        constructor
        · intro _
          exact hqR.le.trans hRx
        · intro _
          exact hu.2.le
      · have hxR : cdf μ x ≤ R := (not_le.mp hRx).le
        rw [max_eq_right hLx, min_eq_right hxR, le_div_iff₀ hD]
        constructor <;> intro h <;> linarith
  exact quantile_eq_of_le_cdf_iff _ _ hlevel

/-- The cdf conditioned on `(l, r]` excludes the lower atom and retains the upper atom. -/
theorem cdf_cond_Ioc {l r : ℝ} (hLR : cdf μ l < cdf μ r) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ (Ioc l r)) x =
      (min (cdf μ r) (max (cdf μ l) (cdf μ x)) - cdf μ l) /
        (cdf μ r - cdf μ l) := by
  simpa only [Iic_sdiff_Iic, ← cdf_eq_real] using
    cdf_cond_sdiff μ (IsLowerSet.Iic l) (IsLowerSet.Iic r)
      (by simpa only [← cdf_eq_real] using hLR) x

/-- For `0 < u < 1`, the `u`-quantile conditioned on `(l, r]` is the source quantile at the
rescaled level `cdf μ l + u * (cdf μ r - cdf μ l)`. -/
theorem quantile_cond_Ioc {l r u : ℝ} (hLR : cdf μ l < cdf μ r)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (ProbabilityTheory.cond μ (Ioc l r)).quantile u =
      μ.quantile (cdf μ l + u * (cdf μ r - cdf μ l)) := by
  simpa only [Iic_sdiff_Iic, ← cdf_eq_real] using
    quantile_cond_sdiff μ (IsLowerSet.Iic l) (IsLowerSet.Iic r)
      (by simpa only [← cdf_eq_real] using hLR) hu

/-- The cdf conditioned on `[l, r]` includes both endpoint atoms. The lower cut is the mass
strictly below `l`, allowing even `l = r` when the endpoint has positive mass. -/
theorem cdf_cond_Icc {l r : ℝ} (hLR : μ.real (Iio l) < cdf μ r) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ (Icc l r)) x =
      (min (cdf μ r) (max (μ.real (Iio l)) (cdf μ x)) - μ.real (Iio l)) /
        (cdf μ r - μ.real (Iio l)) := by
  simpa only [Iic_sdiff_Iio, ← cdf_eq_real] using
    cdf_cond_sdiff μ (IsLowerSet.Iio l) (IsLowerSet.Iic r)
      (by simpa only [← cdf_eq_real] using hLR) x

/-- The interior quantile conditioned on `[l, r]`, retaining both endpoint atoms. -/
theorem quantile_cond_Icc {l r u : ℝ} (hLR : μ.real (Iio l) < cdf μ r)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (ProbabilityTheory.cond μ (Icc l r)).quantile u =
      μ.quantile (μ.real (Iio l) + u * (cdf μ r - μ.real (Iio l))) := by
  simpa only [Iic_sdiff_Iio, ← cdf_eq_real] using
    quantile_cond_sdiff μ (IsLowerSet.Iio l) (IsLowerSet.Iic r)
      (by simpa only [← cdf_eq_real] using hLR) hu

/-- The cdf conditioned on `(l, r)` excludes both endpoint atoms. The upper cut is the mass
strictly below `r`. -/
theorem cdf_cond_Ioo {l r : ℝ} (hLR : cdf μ l < μ.real (Iio r)) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ (Ioo l r)) x =
      (min (μ.real (Iio r)) (max (cdf μ l) (cdf μ x)) - cdf μ l) /
        (μ.real (Iio r) - cdf μ l) := by
  simpa only [Iio_sdiff_Iic, ← cdf_eq_real] using
    cdf_cond_sdiff μ (IsLowerSet.Iic l) (IsLowerSet.Iio r)
      (by simpa only [← cdf_eq_real] using hLR) x

/-- The interior quantile conditioned on `(l, r)`, excluding both endpoint atoms. -/
theorem quantile_cond_Ioo {l r u : ℝ} (hLR : cdf μ l < μ.real (Iio r))
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (ProbabilityTheory.cond μ (Ioo l r)).quantile u =
      μ.quantile (cdf μ l + u * (μ.real (Iio r) - cdf μ l)) := by
  simpa only [Iio_sdiff_Iic, ← cdf_eq_real] using
    quantile_cond_sdiff μ (IsLowerSet.Iic l) (IsLowerSet.Iio r)
      (by simpa only [← cdf_eq_real] using hLR) hu

/-- The cdf conditioned on `[l, r)` retains the lower atom and excludes the upper atom. -/
theorem cdf_cond_Ico {l r : ℝ} (hLR : μ.real (Iio l) < μ.real (Iio r)) (x : ℝ) :
    cdf (ProbabilityTheory.cond μ (Ico l r)) x =
      (min (μ.real (Iio r)) (max (μ.real (Iio l)) (cdf μ x)) - μ.real (Iio l)) /
        (μ.real (Iio r) - μ.real (Iio l)) := by
  simpa only [Iio_sdiff_Iio] using
    cdf_cond_sdiff μ (IsLowerSet.Iio l) (IsLowerSet.Iio r) hLR x

/-- The interior quantile conditioned on `[l, r)`, retaining the lower atom and excluding the
upper atom. -/
theorem quantile_cond_Ico {l r u : ℝ} (hLR : μ.real (Iio l) < μ.real (Iio r))
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (ProbabilityTheory.cond μ (Ico l r)).quantile u =
      μ.quantile (μ.real (Iio l) + u * (μ.real (Iio r) - μ.real (Iio l))) := by
  simpa only [Iio_sdiff_Iio] using
    quantile_cond_sdiff μ (IsLowerSet.Iio l) (IsLowerSet.Iio r) hLR hu

end MeasureTheory.Measure

/-! ### Affine transport -/

namespace MeasureTheory.Measure

variable (μ : Measure ℝ)

/-- Real affine pushforward commutes with conditioning on the preimage of an arbitrary event,
without requiring the event to be measurable, including at zero slope and for zero-mass or
infinite-mass events. -/
theorem map_affine_cond_preimage (a b : ℝ) (s : Set ℝ) :
    (ProbabilityTheory.cond μ ((fun x ↦ a + b * x) ⁻¹' s)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) s := by
  by_cases hb : b = 0
  · classical
    subst hb
    simp only [zero_mul, add_zero, Measure.map_const]
    by_cases ha : a ∈ s
    · rw [preimage_const_of_mem ha, ProbabilityTheory.cond, Measure.restrict_univ,
        ProbabilityTheory.cond, Measure.restrict_smul, restrict_dirac]
      simp [ha, smul_smul]
    · rw [preimage_const_of_notMem ha, ProbabilityTheory.cond_empty, ProbabilityTheory.cond,
        Measure.restrict_smul, restrict_dirac]
      simp [ha]
  · simpa only [Function.comp_def] using
      ((measurableEmbedding_addLeft a).comp (measurableEmbedding_mulLeft₀ hb)).map_cond_preimage μ s

/-- An invertible real affine pushforward commutes with truncation by transforming both the
underlying measure and the conditioning event, without requiring the event to be measurable or to
have positive or finite mass. -/
theorem map_affine_cond (a : ℝ) {b : ℝ} (hb : b ≠ 0) (s : Set ℝ) :
    (ProbabilityTheory.cond μ s).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) ((fun x ↦ a + b * x) '' s) := by
  simpa only [Function.comp_def] using
    ((measurableEmbedding_addLeft a).comp (measurableEmbedding_mulLeft₀ hb)).map_cond μ s

/-- Positive affine transport preserves truncation to a closed interval `[l, r]`. -/
theorem map_affine_cond_Icc_pos (a : ℝ) {b : ℝ} (hb : 0 < b) (l r : ℝ) :
    (ProbabilityTheory.cond μ (Icc l r)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Icc (a + b * l) (a + b * r)) := by
  rw [μ.map_affine_cond a hb.ne', ← image_image (a + ·) (b * ·), image_mul_left_Icc' hb,
    image_const_add_Icc]

/-- Positive affine transport preserves truncation to an open interval `(l, r)`. -/
theorem map_affine_cond_Ioo_pos (a : ℝ) {b : ℝ} (hb : 0 < b) (l r : ℝ) :
    (ProbabilityTheory.cond μ (Ioo l r)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Ioo (a + b * l) (a + b * r)) := by
  rw [μ.map_affine_cond a hb.ne', ← image_image (a + ·) (b * ·), image_mul_left_Ioo hb,
    image_const_add_Ioo]

/-- Positive affine transport preserves truncation to a half-open interval `[l, r)`. -/
theorem map_affine_cond_Ico_pos (a : ℝ) {b : ℝ} (hb : 0 < b) (l r : ℝ) :
    (ProbabilityTheory.cond μ (Ico l r)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Ico (a + b * l) (a + b * r)) := by
  rw [μ.map_affine_cond a hb.ne', ← image_image (a + ·) (b * ·), image_mul_left_Ico hb,
    image_const_add_Ico]

/-- Positive affine transport preserves truncation to a half-open interval `(l, r]`. -/
theorem map_affine_cond_Ioc_pos (a : ℝ) {b : ℝ} (hb : 0 < b) (l r : ℝ) :
    (ProbabilityTheory.cond μ (Ioc l r)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Ioc (a + b * l) (a + b * r)) := by
  rw [μ.map_affine_cond a hb.ne', ← image_image (a + ·) (b * ·), image_mul_left_Ioc hb,
    image_const_add_Ioc]

/-- Positive affine transport preserves truncation to a closed upper ray `[l, ∞)`. -/
theorem map_affine_cond_Ici_pos (a : ℝ) {b : ℝ} (hb : 0 < b) (l : ℝ) :
    (ProbabilityTheory.cond μ (Ici l)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Ici (a + b * l)) := by
  rw [μ.map_affine_cond a hb.ne', ← image_image (a + ·) (b * ·), image_mul_left_Ici hb,
    image_const_add_Ici]

/-- Positive affine transport preserves truncation to an open upper ray `(l, ∞)`. -/
theorem map_affine_cond_Ioi_pos (a : ℝ) {b : ℝ} (hb : 0 < b) (l : ℝ) :
    (ProbabilityTheory.cond μ (Ioi l)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Ioi (a + b * l)) := by
  rw [μ.map_affine_cond a hb.ne', ← image_image (a + ·) (b * ·), image_mul_left_Ioi hb,
    image_const_add_Ioi]

/-- Positive affine transport preserves truncation to a closed lower ray `(-∞, r]`. -/
theorem map_affine_cond_Iic_pos (a : ℝ) {b : ℝ} (hb : 0 < b) (r : ℝ) :
    (ProbabilityTheory.cond μ (Iic r)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Iic (a + b * r)) := by
  rw [μ.map_affine_cond a hb.ne', ← image_image (a + ·) (b * ·), image_mul_left_Iic hb,
    image_const_add_Iic]

/-- Positive affine transport preserves truncation to an open lower ray `(-∞, r)`. -/
theorem map_affine_cond_Iio_pos (a : ℝ) {b : ℝ} (hb : 0 < b) (r : ℝ) :
    (ProbabilityTheory.cond μ (Iio r)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Iio (a + b * r)) := by
  rw [μ.map_affine_cond a hb.ne', ← image_image (a + ·) (b * ·), image_mul_left_Iio hb,
    image_const_add_Iio]

/-- Negative affine transport reverses the endpoints of a closed truncation interval. -/
theorem map_affine_cond_Icc_neg (a : ℝ) {b : ℝ} (hb : b < 0) (l r : ℝ) :
    (ProbabilityTheory.cond μ (Icc l r)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Icc (a + b * r) (a + b * l)) := by
  rw [← μ.map_affine_cond_preimage a b, ← Function.comp_def (a + ·) (b * ·), preimage_comp]
  simp [hb, hb.ne]

/-- Negative affine transport reverses the endpoints of an open truncation interval. -/
theorem map_affine_cond_Ioo_neg (a : ℝ) {b : ℝ} (hb : b < 0) (l r : ℝ) :
    (ProbabilityTheory.cond μ (Ioo l r)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Ioo (a + b * r) (a + b * l)) := by
  rw [← μ.map_affine_cond_preimage a b, ← Function.comp_def (a + ·) (b * ·), preimage_comp]
  simp [hb, hb.ne]

/-- Negative affine transport exchanges a closed lower and open upper truncation endpoint. -/
theorem map_affine_cond_Ico_neg (a : ℝ) {b : ℝ} (hb : b < 0) (l r : ℝ) :
    (ProbabilityTheory.cond μ (Ico l r)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Ioc (a + b * r) (a + b * l)) := by
  rw [← μ.map_affine_cond_preimage a b, ← Function.comp_def (a + ·) (b * ·), preimage_comp]
  simp [hb, hb.ne]

/-- Negative affine transport exchanges an open lower and closed upper truncation endpoint. -/
theorem map_affine_cond_Ioc_neg (a : ℝ) {b : ℝ} (hb : b < 0) (l r : ℝ) :
    (ProbabilityTheory.cond μ (Ioc l r)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Ico (a + b * r) (a + b * l)) := by
  rw [← μ.map_affine_cond_preimage a b, ← Function.comp_def (a + ·) (b * ·), preimage_comp]
  simp [hb, hb.ne]

/-- Negative affine transport sends truncation on a closed upper ray `[l, ∞)` to the closed lower
ray `(-∞, a + b * l]`. -/
theorem map_affine_cond_Ici_neg (a : ℝ) {b : ℝ} (hb : b < 0) (l : ℝ) :
    (ProbabilityTheory.cond μ (Ici l)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Iic (a + b * l)) := by
  rw [← μ.map_affine_cond_preimage a b, ← Function.comp_def (a + ·) (b * ·), preimage_comp]
  simp [hb, hb.ne]

/-- Negative affine transport sends truncation on an open upper ray `(l, ∞)` to the open lower
ray `(-∞, a + b * l)`. -/
theorem map_affine_cond_Ioi_neg (a : ℝ) {b : ℝ} (hb : b < 0) (l : ℝ) :
    (ProbabilityTheory.cond μ (Ioi l)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Iio (a + b * l)) := by
  rw [← μ.map_affine_cond_preimage a b, ← Function.comp_def (a + ·) (b * ·), preimage_comp]
  simp [hb, hb.ne]

/-- Negative affine transport sends truncation on a closed lower ray `(-∞, r]` to the closed upper
ray `[a + b * r, ∞)`. -/
theorem map_affine_cond_Iic_neg (a : ℝ) {b : ℝ} (hb : b < 0) (r : ℝ) :
    (ProbabilityTheory.cond μ (Iic r)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Ici (a + b * r)) := by
  rw [← μ.map_affine_cond_preimage a b, ← Function.comp_def (a + ·) (b * ·), preimage_comp]
  simp [hb, hb.ne]

/-- Negative affine transport sends truncation on an open lower ray `(-∞, r)` to the open upper
ray `(a + b * r, ∞)`. -/
theorem map_affine_cond_Iio_neg (a : ℝ) {b : ℝ} (hb : b < 0) (r : ℝ) :
    (ProbabilityTheory.cond μ (Iio r)).map (fun x ↦ a + b * x) =
      ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) (Ioi (a + b * r)) := by
  rw [← μ.map_affine_cond_preimage a b, ← Function.comp_def (a + ·) (b * ·), preimage_comp]
  simp [hb, hb.ne]

end MeasureTheory.Measure

namespace ProbabilityTheory.HasLaw

open MeasureTheory

/-- An invertible real affine function of a variable with a conditional law has the pushed-forward
underlying law conditioned on the affine image of the event, without requiring the event to be
measurable. -/
theorem affine_cond {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {μ : Measure ℝ} {s : Set ℝ}
    (hX : HasLaw X (ProbabilityTheory.cond μ s) P) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    HasLaw (fun ω ↦ a + b * X ω)
      (ProbabilityTheory.cond (μ.map (fun x ↦ a + b * x)) ((fun x ↦ a + b * x) '' s)) P := by
  have hf : HasLaw (fun x : ℝ ↦ a + b * x)
      ((ProbabilityTheory.cond μ s).map (fun x ↦ a + b * x)) (ProbabilityTheory.cond μ s) :=
    hasLaw_map (by fun_prop)
  rw [← μ.map_affine_cond a hb s]
  exact hf.comp hX

end ProbabilityTheory.HasLaw
