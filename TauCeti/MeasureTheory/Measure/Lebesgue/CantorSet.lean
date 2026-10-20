/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.Instances.CantorSet

/-!
# Lebesgue measure of the Cantor set

The `n`-th pre-Cantor set `preCantorSet n` is a union of `2ⁿ` closed intervals of length `3⁻ⁿ`,
so its Lebesgue measure is `(2 / 3)ⁿ`. Letting `n → ∞` shows that the ternary Cantor set
`cantorSet` is Lebesgue-null. This is the input for the Cantor function being differentiable
with derivative zero almost everywhere.

## Main results

* `TauCeti.volume_preCantorSet`: `volume (preCantorSet n) = (2 / 3) ^ n`.
* `TauCeti.volume_cantorSet`: `volume cantorSet = 0`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace TauCeti

/-- Each of the two affine maps `x ↦ x / 3` and `x ↦ (2 + x) / 3` building the pre-Cantor sets
scales Lebesgue measure by `1 / 3`. -/
private lemma volume_image_add_div_three (c : ℝ) (s : Set ℝ) :
    volume ((fun x ↦ (c + x) / 3) '' s) = 3⁻¹ * volume s := by
  have h : (fun x : ℝ ↦ (c + x) / 3) = AffineMap.homothety (c / 2) (3⁻¹ : ℝ) := by
    ext x
    simp only [AffineMap.homothety_apply, vsub_eq_sub, smul_eq_mul, vadd_eq_add]
    ring
  rw [h, Measure.addHaar_image_homothety]
  norm_num [ENNReal.ofReal_div_of_pos, one_div]

/-- The `n`-th pre-Cantor set has Lebesgue measure `(2 / 3) ^ n`. -/
theorem volume_preCantorSet (n : ℕ) : volume (preCantorSet n) = (2 / 3 : ℝ≥0∞) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hleft : (· / 3) '' preCantorSet n = (fun x ↦ (0 + x) / 3) '' preCantorSet n := by
      simp
    have hdisj : Disjoint ((· / 3) '' preCantorSet n)
        ((fun x ↦ (2 + x) / 3) '' preCantorSet n) := by
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
      have hx1 := (preCantorSet_subset_unitInterval hx).2
      have hy0 := (preCantorSet_subset_unitInterval hy).1
      linarith
    have hmeas : MeasurableSet ((fun x ↦ (2 + x) / 3) '' preCantorSet n) :=
      ((isCompact_Icc.of_isClosed_subset (isClosed_preCantorSet n)
        preCantorSet_subset_unitInterval).image (by fun_prop)).isClosed.measurableSet
    rw [preCantorSet_succ, measure_union hdisj hmeas, hleft, volume_image_add_div_three,
      volume_image_add_div_three, ih, pow_succ, ← add_mul, ENNReal.div_eq_inv_mul]
    ring

/-- The ternary Cantor set is Lebesgue-null. -/
@[simp]
theorem volume_cantorSet : volume cantorSet = 0 := by
  refine nonpos_iff_eq_zero.mp (ge_of_tendsto'
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := 2 / 3) ?_) fun n ↦ ?_)
  · exact ENNReal.div_lt_of_lt_mul' (by norm_num)
  · rw [← volume_preCantorSet n]
    exact measure_mono (iInter_subset _ n)

end TauCeti
