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
gives the limit of the squared-sinc smoothing of the normalised profile `w_k(t) t^k`
on the positive half-line. There the profile is the regularised lower incomplete Gamma
function `P(k + 1, t)` by `delangeWeight_mul_pow_eq_regularizedGamma`.
The kernel has mass one for positive bandwidth (`squaredSinc_mass`), so the limit is one,
a special case of `MeasureTheory.tendsto_convolution_lsmul_atTop`. Restoring the leading
factor `A/k!` gives the model term in the smoothed Delange–Ikehara limit.

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
  have hsymm : squaredSinc ell (T - t) = squaredSinc ell (t - T) := by
    simpa only [neg_sub] using squaredSinc_neg_right ell (t - T)
  simp only [f, hsymm, indicator_apply, smul_eq_mul, ite_mul, zero_mul,
    mul_comm (squaredSinc ell (t - T))]

end TauCeti.HigherPoleTauberian
