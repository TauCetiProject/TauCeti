/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm
import TauCeti.RingTheory.PowerSeries.CoeffProd

/-!
# Estimates for the Gauss norm of restricted series

Elementary bounds on the Gauss norm of power series over a (semi)normed ring: the ultrametric
bound for a difference, the coefficientwise bound for a product with a linear factor `X - a`, and
the bound on the Gauss norm of a truncation of a restricted series.

## Main results

* `TauCeti.PowerSeries.gaussNorm_sub_le_of_le`: the Gauss norm of a difference is bounded by a
  common bound on the two Gauss norms, over an ultrametric ring.
* `PowerSeries.norm_coeff_X_sub_C_mul_mul_pow_le`: over an ultrametric ring, every weighted
  coefficient of `(X - a) * q` is at most `c` times the Gauss norm of `q` when `‖a‖ ≤ c`.
* `TauCeti.PowerSeries.gaussNorm_trunc_le`: a truncation of a series with Gauss norm has Gauss norm
  at most that of the series.
-/

public section

namespace TauCeti.PowerSeries

variable {c : ℝ}

section Ultrametric

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R]

/-- The Gauss norm of a difference of series with Gauss norm is bounded when both Gauss norms
are. -/
theorem gaussNorm_sub_le_of_le (hc : 0 ≤ c) {a b : PowerSeries R} (ha : a.HasGaussNorm norm c)
    (hb : b.HasGaussNorm norm c) {C : ℝ} (ha' : a.gaussNorm norm c ≤ C)
    (hb' : b.gaussNorm norm c ≤ C) :
    (a - b).gaussNorm norm c ≤ C := by
  rw [sub_eq_add_neg]
  have hbneg : (-b).HasGaussNorm norm c := by
    simpa only [PowerSeries.HasGaussNorm, map_neg, norm_neg] using hb
  refine le_trans (PowerSeries.gaussNorm_add_le_max norm c a (-b) hc norm_nonneg
    IsUltrametricDist.isNonarchimedean_norm ha hbneg) (max_le ha' ?_)
  exact (MvPowerSeries.gaussNorm_neg norm (fun _ ↦ c) (fun x ↦ norm_neg x) b).trans_le hb'

/-- Multiplying a series with Gauss norm by `X - a`, for `a` in the closed disc of radius
`c ≥ 0`, gives weighted coefficients at most `c` times the Gauss norm of the series. -/
theorem _root_.PowerSeries.norm_coeff_X_sub_C_mul_mul_pow_le (hc : 0 ≤ c) {a : R} (ha : ‖a‖ ≤ c)
    {q : PowerSeries R} (hq : q.HasGaussNorm norm c) (m : ℕ) :
    ‖((PowerSeries.X - PowerSeries.C a) * q).coeff m‖ * c ^ m ≤ c * q.gaussNorm norm c := by
  have hqle (m : ℕ) : ‖q.coeff m‖ * c ^ m ≤ q.gaussNorm norm c :=
    PowerSeries.le_gaussNorm norm c q hq m
  have hcross (m : ℕ) : ‖a * q.coeff m‖ * c ^ m ≤ c * q.gaussNorm norm c :=
    calc ‖a * q.coeff m‖ * c ^ m ≤ c * ‖q.coeff m‖ * c ^ m :=
          mul_le_mul_of_nonneg_right (norm_mul_le_of_le ha le_rfl) (pow_nonneg hc m)
      _ ≤ c * q.gaussNorm norm c := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hqle m) hc
  rcases m with _ | m
  · rw [PowerSeries.coeff_zero_X_sub_C_mul, norm_neg]
    exact hcross 0
  · rw [PowerSeries.coeff_succ_X_sub_C_mul, sub_eq_add_neg]
    refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _)
      (pow_nonneg hc _)).trans ?_
    rw [max_mul_of_nonneg _ _ (pow_nonneg hc _), norm_neg]
    refine max_le ?_ (hcross (m + 1))
    calc ‖q.coeff m‖ * c ^ (m + 1) = c * (‖q.coeff m‖ * c ^ m) := by ring
      _ ≤ c * q.gaussNorm norm c := mul_le_mul_of_nonneg_left (hqle m) hc

end Ultrametric

section Trunc

variable {R : Type*} [SeminormedRing R] {f : PowerSeries R}

/-- Every truncation of a series `f` with Gauss norm has Gauss norm at most that of `f`. -/
theorem gaussNorm_trunc_le (hf : f.HasGaussNorm norm c) (N : ℕ) :
    ((f.trunc N : Polynomial R) : PowerSeries R).gaussNorm norm c ≤ f.gaussNorm norm c := by
  rw [PowerSeries.gaussNorm_eq]
  refine ciSup_le fun m ↦ ?_
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs
  · exact PowerSeries.le_gaussNorm norm c f hf m
  · simpa using PowerSeries.gaussNorm_nonneg norm c f norm_nonneg

end Trunc

end TauCeti.PowerSeries
