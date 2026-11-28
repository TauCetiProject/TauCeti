/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Analysis.Submultiplicative
public import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.Distribution.Amice.Norm

/-!
# Derivative norm bounds from prime-power coefficients

For a formal parameter `T`, a unit coefficient of `T(ϖ X) / ϖ` in each degree `p ^ (f * j)`
forces a lower bound on the derivative norms at those degrees. The factorial in the derivative
contributes the radius `p ^ (-1 / (p - 1))`. A submultiplicative sequence dominating these norms
then satisfies the resulting exponential lower bound in every degree. Such lower bounds on norms
are used to show sharpness of divisibility estimates for derivatives on formal groups.

This is the prime-power step and the passage to arbitrary degrees in
`New.CMLattice.katz_divisibility_limit` of [lsernau/grh-lean][one-curve], using the mathematical
input of `New.CMLattice.pow_le_maxDerivNorm_of_eq_primeNorm_pow` in the same file.

[one-curve]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Derivatives/Sharpness/OneCurve.lean
-/

public section

open Filter TauCeti

namespace Submultiplicative

/-- For a parameter whose rescaling divided by `ϖ` has coefficient norm at least one in the
Frobenius degrees `p ^ (f * j)`, a submultiplicative sequence dominating its
factorial-weighted coefficient norms at these degrees is bounded below by
`(p ^ (-1 / (p - 1)) / ‖ϖ‖) ^ n` in every degree `n`. -/
theorem pow_le_of_padic_rescale_coeff {u : ℕ → ℝ} (hu : Submultiplicative u)
    (p : ℕ) [Fact p.Prime] {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[p] K] (T : PowerSeries K) {ϖ : K} (hϖ : ϖ ≠ 0) {f : ℕ} (hf : 0 < f)
    (hcoeff : ∀ j : ℕ, ‖ϖ‖ ≤ ‖(T.rescale ϖ).coeff (p ^ (f * j))‖)
    (hderiv : ∀ j : ℕ, ‖((p ^ (f * j)).factorial : K) * T.coeff (p ^ (f * j))‖ ≤ u (p ^ (f * j)))
    (n : ℕ) : ((p : ℝ) ^ (-1 / ((p : ℝ) - 1)) / ‖ϖ‖) ^ n ≤ u n := by
  have hϖ₀ : 0 < ‖ϖ‖ := norm_pos_iff.mpr hϖ
  have hp : p.Prime := Fact.out
  have hR : amiceRadius p 0 = (p : ℝ) ^ (-1 / ((p : ℝ) - 1)) := by
    simp [amiceRadius_def, neg_div, one_div]
  let C := (p : ℝ) ^ (1 / ((p : ℝ) - 1))
  have hC : 0 < C := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.pos) _
  have hu₁ : 0 ≤ u 1 := (norm_nonneg _).trans (by simpa using hderiv 0)
  rw [← hR]
  apply hu.pow_le_of_frequently_ge_mul_pow hu₁ (mul_pos hC hϖ₀)
    (div_pos (amiceRadius_pos 0) hϖ₀) _ n
  have hindex : 1 < p ^ f := one_lt_pow₀ hp.one_lt hf.ne'
  refine frequently_atTop.mpr fun a ↦ ⟨p ^ (f * a), ?_, ?_⟩
  · rw [pow_mul]
    exact (Nat.lt_pow_self hindex).le
  · let N := p ^ (f * a)
    have hfac : ‖(N.factorial : K)‖ = C * amiceRadius p 0 ^ N := by
      rw [norm_natCast_eq_norm_padic (p := p)]
      simpa only [N, C, zero_add] using norm_factorial_pow_eq_mul_amiceRadius_pow (p := p) 0 (f * a)
    have hs : ‖ϖ‖ / ‖ϖ‖ ^ N ≤ ‖T.coeff N‖ := by
      apply (div_le_iff₀' (pow_pos hϖ₀ N)).mpr
      simpa [PowerSeries.coeff_rescale, norm_mul, N] using hcoeff a
    calc
      (C * ‖ϖ‖) * (amiceRadius p 0 / ‖ϖ‖) ^ N =
          (C * amiceRadius p 0 ^ N) * (‖ϖ‖ / ‖ϖ‖ ^ N) := by rw [div_pow]; ring
      _ ≤ ‖(N.factorial : K) * T.coeff N‖ := by
        rw [norm_mul, hfac]
        exact mul_le_mul_of_nonneg_left hs (mul_nonneg hC.le (pow_nonneg (amiceRadius_pos 0).le _))
      _ ≤ u N := hderiv a

end Submultiplicative
