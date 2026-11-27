/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.RingTheory.PowerSeries.CoeffProd

/-!
# Estimates for the Gauss norm of restricted series

Elementary bounds on the Gauss norm and weighted coefficients of power series over a (semi)normed
ring: the ultrametric bound for a difference, the coefficientwise bound for a product with a linear
factor `X - a`, the bound on the Gauss norm of a truncation of a restricted series, and
single-degree weighted bounds on truncations and truncated scaled geometric series.

## Main results

* `TauCeti.PowerSeries.gaussNorm_sub_le_of_le`: the Gauss norm of a difference is bounded by a
  common bound on the two Gauss norms, over an ultrametric ring.
* `PowerSeries.norm_coeff_X_sub_C_mul_mul_pow_le`: over an ultrametric ring, every weighted
  coefficient of `(X - a) * q` is at most `c` times the Gauss norm of `q` when `‖a‖ ≤ c`.
* `TauCeti.PowerSeries.gaussNorm_trunc_le`: a truncation of a series with Gauss norm has Gauss norm
  at most that of the series.
* `PowerSeries.norm_coeff_trunc_mul_pow_le`: truncating a power series below degree `N` preserves a
  nonnegative single-degree weighted bound below `N`.
* `PowerSeries.norm_coeff_trunc_C_mul_mk_pow_mul_pow_le`: if `0 ≤ c` and `‖b‖ * c ≤ 1`, every
  `c`-weighted coefficient of `trunc N (C a * ∑ k, b ^ k * X ^ k)` is bounded by `‖a‖`.
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

namespace PowerSeries

section WeightedCoeff

variable {R : Type*} [SeminormedRing R]

/-- Truncating a power series below degree `N` bounds its `n`-th weighted coefficient by any
`B ≥ 0` that bounds `‖coeff n φ‖ * c ^ n` when `n < N`. -/
theorem norm_coeff_trunc_mul_pow_le {φ : PowerSeries R} {c B : ℝ} (hB : 0 ≤ B) {N n : ℕ}
    (hφ : n < N → ‖coeff n φ‖ * c ^ n ≤ B) :
    ‖(trunc N φ).coeff n‖ * c ^ n ≤ B := by
  rw [coeff_trunc]
  split_ifs with hn
  · exact hφ hn
  · simpa using hB

/-- If `0 ≤ c` and `‖b‖ * c ≤ 1`, every `c`-weighted coefficient of a truncated scaled geometric
series `trunc N (C a * ∑ k, b ^ k * X ^ k)` is bounded by `‖a‖`. -/
theorem norm_coeff_trunc_C_mul_mk_pow_mul_pow_le (a : R) {b : R} {c : ℝ} (hc : 0 ≤ c)
    (hb : ‖b‖ * c ≤ 1) (N n : ℕ) :
    ‖(trunc N (C a * mk fun k ↦ b ^ k)).coeff n‖ * c ^ n ≤ ‖a‖ := by
  refine norm_coeff_trunc_mul_pow_le (norm_nonneg a) fun _ ↦ ?_
  rw [coeff_C_mul, coeff_mk]
  calc ‖a * b ^ n‖ * c ^ n
      ≤ ‖a‖ * ‖b‖ ^ n * c ^ n :=
        mul_le_mul_of_nonneg_right (TauCeti.norm_mul_pow_le a b n) (pow_nonneg hc n)
    _ = ‖a‖ * (‖b‖ * c) ^ n := by rw [mul_assoc, ← mul_pow]
    _ ≤ ‖a‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (mul_nonneg (norm_nonneg b) hc) hb) (norm_nonneg a)
    _ = ‖a‖ := mul_one _

end WeightedCoeff

end PowerSeries
