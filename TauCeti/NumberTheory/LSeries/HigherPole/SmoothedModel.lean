/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.HigherPole.DelangeWeight
public import TauCeti.NumberTheory.LSeries.HigherPole.SquaredSinc
import TauCeti.Analysis.Convolution.AtInfinity

/-!
# Squared-sinc smoothing of Delange's model

`TauCeti.HigherPoleTauberian.tendsto_integral_delangeWeight_mul_pow_mul_squaredSinc`
evaluates the limit of the squared-sinc smoothing of the normalised Delange weight on the
positive half-line. This is the profile of the weighted model for a pole of order `k + 1`
after removing its exponential and leading constant. Its limit follows from
`tendsto_delangeWeight_mul_pow_atTop`, `squaredSinc_mass` and
`MeasureTheory.tendsto_convolution_lsmul_atTop`, which uses Mathlib's convolution API.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) 71 (1954),
  213–242, §3.3.5.
-/

public section

open Filter MeasureTheory Set
open scoped Convolution Topology

namespace TauCeti.HigherPoleTauberian

/-- The squared-sinc smoothing of the normalised model tends to one for each positive
bandwidth (Delange, 1954, §3.3.5). -/
theorem tendsto_integral_delangeWeight_mul_pow_mul_squaredSinc (k : ℕ) {ell : ℝ}
    (hell : 0 < ell) :
    Tendsto (fun T : ℝ ↦ ∫ t in Ioi 0, delangeWeight k t * t ^ k * squaredSinc ell (t - T))
      atTop (𝓝 1) := by
  let f : ℝ → ℝ := (Ioi 0).indicator (fun t ↦ delangeWeight k t * t ^ k)
  have hf : AEStronglyMeasurable f volume :=
    ((continuous_delangeWeight k).mul (continuous_id.pow k)).aestronglyMeasurable.indicator
      measurableSet_Ioi
  have hbound : ∀ᵐ t ∂volume, ‖f t‖ ≤ 1 := .of_forall fun t ↦ by
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp only [f, indicator_of_mem ht, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (delangeWeight_nonneg ht.le) (pow_nonneg ht.le _))]
      exact (delangeWeight_mul_pow_lt_one ht.le).le
    · simp only [f, indicator_of_notMem ht, norm_zero, zero_le_one]
  have hlim : Tendsto f atTop (𝓝 1) := (tendsto_delangeWeight_mul_pow_atTop k).congr' <| by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have ht' : t ∈ Ioi (0 : ℝ) := ht
    exact (indicator_of_mem ht' (fun u ↦ delangeWeight k u * u ^ k)).symm
  have h := tendsto_convolution_lsmul_atTop (integrable_squaredSinc ell) hf hbound hlim
  rw [squaredSinc_mass hell, one_smul] at h
  refine h.congr fun T ↦ ?_
  rw [convolution_lsmul_swap, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  dsimp only [f]
  rw [← indicator_smul_apply (Ioi 0) (fun u ↦ squaredSinc ell (T - u))]
  apply congrArg (fun g : ℝ → ℝ ↦ (Ioi 0).indicator g t)
  funext u
  rw [smul_eq_mul, ← squaredSinc_neg_right ell (T - u), neg_sub, mul_comm]

end TauCeti.HigherPoleTauberian
