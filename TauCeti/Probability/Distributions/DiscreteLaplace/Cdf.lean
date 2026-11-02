/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.DiscreteLaplace.Basic
public import TauCeti.Probability.Cdf
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Cumulative probabilities of discrete Laplace laws

The cumulative mass of a discrete Laplace law is a geometric tail below its integer center,
and one minus a geometric tail at or above the center. The real-cast cdf uses integer floor,
including at negative arguments. These formulas retain the atom at each cutoff and include
the point-mass boundary `q = 0`.

## References

* S. Inusah and T. J. Kozubowski, *A discrete analogue of the Laplace distribution*, Journal of
  Statistical Planning and Inference 136 (2006), 1090–1102.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

/-- At or below the center, the cumulative discrete Laplace mass is a geometric tail.
The exponent is a natural number because `k ≤ m`. -/
theorem discreteLaplaceMeasure_real_Iic_of_le (m : ℤ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) {k : ℤ} (hk : k ≤ m) :
    (discreteLaplaceMeasure m q).real (Iic k) = q ^ (m - k).toNat / (1 + q) := by
  have := isProbabilityMeasure_discreteLaplaceMeasure m hq0 hq1
  have hcover : Iic k = ⋃ n : ℕ, {k - (n : ℤ)} := by
    ext j
    simp only [mem_Iic, mem_iUnion, mem_singleton_iff]
    constructor
    · intro hj
      exact ⟨(k - j).toNat, by omega⟩
    · rintro ⟨n, rfl⟩
      omega
  have hmass : discreteLaplaceMeasure m q (Iic k) =
      ∑' n : ℕ, discreteLaplaceMeasure m q {k - (n : ℤ)} := by
    rw [hcover]
    apply measure_iUnion
    · intro i j hij
      simp only [Function.onFun, disjoint_singleton]
      omega
    · intro n
      exact measurableSet_singleton _
  have hsum := (ENNReal.summable.hasSum_iff.mpr hmass.symm).toReal (measure_ne_top _ _)
  have hterm (n : ℕ) :
      (discreteLaplaceMeasure m q {k - (n : ℤ)}).toReal =
        ((1 - q) * q ^ (m - k).toNat / (1 + q)) * q ^ n := by
    rw [← measureReal_def, discreteLaplaceMeasure_real_singleton m hq0 hq1,
      discreteLaplaceWeightReal_def]
    have habs : (k - (n : ℤ) - m).natAbs = (m - k).toNat + n := by omega
    rw [habs, pow_add]
    ring
  simp_rw [hterm] at hsum
  have hgeom := (hasSum_geometric_of_lt_one hq0 hq1).mul_left
    ((1 - q) * q ^ (m - k).toNat / (1 + q))
  have hq : 1 - q ≠ 0 := by linarith
  have heq := hsum.unique hgeom
  rw [← measureReal_def] at heq
  rw [heq]
  field_simp

/-- The cumulative discrete Laplace mass, including the point-mass parameter `q = 0`.
Natural conversion is applied only to the nonnegative distance from the center. -/
theorem discreteLaplaceMeasure_real_Iic (m : ℤ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (k : ℤ) :
    (discreteLaplaceMeasure m q).real (Iic k) =
      if k < m then q ^ (m - k).toNat / (1 + q)
      else 1 - q ^ ((k - m).toNat + 1) / (1 + q) := by
  have := isProbabilityMeasure_discreteLaplaceMeasure m hq0 hq1
  split_ifs with hk
  · exact discreteLaplaceMeasure_real_Iic_of_le m hq0 hq1 hk.le
  · have hpre : (Neg.neg : ℤ → ℤ) ⁻¹' Iic (-k - 1) = (Iic k)ᶜ := by
      ext j
      simp only [mem_preimage, mem_Iic, mem_compl_iff, not_le]
      omega
    have hreflect : (discreteLaplaceMeasure (-m) q).real (Iic (-k - 1)) =
        1 - (discreteLaplaceMeasure m q).real (Iic k) := by
      rw [← map_neg_discreteLaplaceMeasure, map_measureReal_apply (by fun_prop)
        measurableSet_Iic, hpre, measureReal_compl measurableSet_Iic, probReal_univ]
    rw [discreteLaplaceMeasure_real_Iic_of_le (-m) hq0 hq1 (by omega)] at hreflect
    have hexp : (-m - (-k - 1)).toNat = (k - m).toNat + 1 := by omega
    rw [hexp] at hreflect
    linarith

/-- The cdf of the real-cast discrete Laplace law uses the integer floor of the cutoff.
This formula applies at every real cutoff, including negative ones. -/
theorem cdf_map_intCast_discreteLaplaceMeasure (m : ℤ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (x : ℝ) :
    cdf ((discreteLaplaceMeasure m q).map (Int.cast : ℤ → ℝ)) x =
      if ⌊x⌋ < m then q ^ (m - ⌊x⌋).toNat / (1 + q)
      else 1 - q ^ ((⌊x⌋ - m).toNat + 1) / (1 + q) := by
  have := isProbabilityMeasure_discreteLaplaceMeasure m hq0 hq1
  rw [Measure.cdf_map_intCast, discreteLaplaceMeasure_real_Iic m hq0 hq1]

end TauCeti.Probability
