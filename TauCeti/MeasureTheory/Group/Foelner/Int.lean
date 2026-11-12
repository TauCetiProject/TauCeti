/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Group.FoelnerFilter
public import Mathlib.MeasureTheory.Measure.Count
public import TauCeti.Data.Int.Interval

/-!
# A Følner sequence of integer intervals

The intervals `{0, …, n}` have cardinality `n + 1` and translation boundary at most `2 * |k|`.
Their relative boundaries tend to zero. We give the real cardinality limit and the
counting-measure statement `TauCeti.isAddFoelner_int_Icc`, using Mathlib's additive action API.

## References

* A. Garrido, *An introduction to amenable groups*, Example 3.5.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Example G.5.4.
-/

public section

open Filter Finset MeasureTheory Topology
open scoped Pointwise symmDiff

namespace Int

/-- Integer intervals have vanishing relative translation boundary. -/
theorem tendsto_card_image_add_left_Icc_symmDiff_div_card (k : ℤ) :
    Tendsto (fun n : ℕ =>
      (#(((Icc 0 (n : ℤ)).image (k + ·)) ∆ Icc 0 (n : ℤ)) : ℝ) /
        #(Icc 0 (n : ℤ))) atTop (𝓝 0) := by
  have hcard (n : ℕ) : #(Icc 0 (n : ℤ)) = n + 1 := by
    simp [Int.card_Icc]
  refine squeeze_zero (fun n => by positivity)
    (fun n => div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (card_image_add_left_Icc_symmDiff_le k 0 n)) (by positivity)) ?_
  simp_rw [hcard, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
  simpa [div_eq_mul_inv] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * (k.natAbs : ℝ))

end Int

namespace TauCeti

/-- The integer intervals `{0, …, n}` form an additive Følner sequence for counting measure. -/
theorem isAddFoelner_int_Icc :
    IsAddFoelner ℤ Measure.count atTop (fun n : ℕ => (Icc 0 (n : ℤ) : Set ℤ)) where
  eventually_measurableSet := .of_forall fun n => (Icc 0 (n : ℤ)).measurableSet
  eventually_meas_ne_zero := .of_forall fun n => by
    rw [Measure.count_apply_finset]
    simp [Int.card_Icc]
  eventually_meas_ne_top := .of_forall fun n => by
    rw [Measure.count_apply_finset]
    exact ENNReal.natCast_ne_top _
  tendsto_meas_vadd_symmDiff k := by
    have h := ENNReal.tendsto_ofReal (Int.tendsto_card_image_add_left_Icc_symmDiff_div_card k)
    have heq (n : ℕ) :
        ENNReal.ofReal ((#(((Icc 0 (n : ℤ)).image (k + ·)) ∆ Icc 0 (n : ℤ)) : ℝ) /
          #(Icc 0 (n : ℤ))) =
        Measure.count ((k +ᵥ (Icc 0 (n : ℤ) : Set ℤ)) ∆ Icc 0 (n : ℤ)) /
          Measure.count (Icc 0 (n : ℤ) : Set ℤ) := by
      rw [← coe_vadd_finset, ← coe_symmDiff, Measure.count_apply_finset,
        Measure.count_apply_finset, vadd_finset_def]
      simp only [vadd_eq_add]
      rw [ENNReal.ofReal_div_of_pos (by
        exact_mod_cast (nonempty_Icc.mpr (Int.natCast_nonneg n)).card_pos), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]
    simpa only [heq, ENNReal.ofReal_zero] using h

end TauCeti
