/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
public import TauCeti.Probability.Distributions.Beta.Cdf

/-!
# The cumulative distribution function of Fisher's F law

For positive degrees of freedom `m` and `n`, the cumulative distribution function of
`fisherSnedecorMeasure m n` is `0` on the nonpositive half-line and, at `x > 0`, the regularized
incomplete beta function `I_{m / 2, n / 2}` at `m * x / (n + m * x)`, the inverse of the beta-to-F
map. This is the beta distribution function read through that inverse, in the
regularized-incomplete-beta convention of the beta API.

## Main results

* `cdf_fisherSnedecorMeasure_eq` — the closed-form cumulative distribution function.

## References

* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 27.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {m n : ℝ}

/-- On the beta law, the preimage of `Iic x` under the beta-to-F map agrees a.e. with
`Iic (fisherSnedecorMapInv m n x)` for positive `x`. -/
private theorem fisherSnedecorMap_preimage_Iic_ae (hm : 0 < m) (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    fisherSnedecorMap m n ⁻¹' Iic x =ᵐ[betaMeasure (m / 2) (n / 2)]
      Iic (fisherSnedecorMapInv m n x) := by
  filter_upwards [ae_mem_Ioo_betaMeasure (m / 2) (n / 2)] with u hu
  simp only [mem_preimage, mem_Iic]
  apply propext
  have hden : 0 < n + m * x := add_pos hn (mul_pos hm hx)
  have h_inv := fisherSnedecorMap_mapInv (x := x) (ne_of_gt hm) (ne_of_gt hn)
    (ne_of_gt hden)
  have key := (fisherSnedecorMap_strictMonoOn hm hn).le_iff_le hu.2
    (fisherSnedecorMapInv_mem_Ioo hm hn hx).2
  rw [h_inv] at key
  exact key

/-- For positive degrees of freedom, the cdf is `0` when `x ≤ 0` and is the regularized
incomplete beta function at `m * x / (n + m * x)` when `0 < x`. -/
theorem cdf_fisherSnedecorMeasure_eq (hm : 0 < m) (hn : 0 < n) (x : ℝ) :
  cdf (fisherSnedecorMeasure m n) x =
      if x ≤ 0 then 0 else
      regularizedIncompleteBeta (m / 2) (n / 2) (m * x / (n + m * x)) := by
  let _ : IsProbabilityMeasure (fisherSnedecorMeasure m n) :=
    isProbabilityMeasure_fisherSnedecorMeasure hm hn
  let _ : IsProbabilityMeasure (betaMeasure (m / 2) (n / 2)) :=
    isProbabilityMeasureBeta (by linarith) (by linarith)
  by_cases hx : x ≤ 0
  · rw [ite_eq_left hx]
    rw [cdf_eq_real]
    have hpre : (Iic x : Set ℝ) =ᵐ[fisherSnedecorMeasure m n] ∅ := by
      filter_upwards [ae_mem_Ioi_fisherSnedecorMeasure m n] with y hy
      apply propext
      constructor
      · intro hyx
        exact (not_lt_of_ge (hyx.trans hx)) hy
      · intro hyempty
        simp at hyempty
    rw [measureReal_congr hpre, measureReal_empty]
  · have hx' : 0 < x := lt_of_not_ge hx
    rw [ite_eq_right hx]
    rw [cdf_eq_real, fisherSnedecorMeasure_eq_map hm hn,
      map_measureReal_apply (measurable_fisherSnedecorMap m n) measurableSet_Iic,
      measureReal_congr (fisherSnedecorMap_preimage_Iic_ae hm hn hx')]
    rw [← cdf_eq_real]
    simpa only [fisherSnedecorMapInv_def] using
      cdf_betaMeasure_eq (by linarith) (by linarith) _

end Probability

end TauCeti
