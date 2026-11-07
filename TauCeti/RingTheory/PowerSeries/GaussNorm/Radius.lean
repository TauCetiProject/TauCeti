/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Radius contraction for series with vanishing initial coefficients

If the coefficients below degree `N` vanish, shrinking the radius from `r` to `s`
contracts the Gauss norm by at least `(s / r) ^ N`. Bounded weighted coefficients
suffice; neither restrictedness nor a nonarchimedean coefficient norm is required.
In particular, series with constant coefficient one approach one on a fixed
smaller disc as their radii of control grow, provided the Gauss norms of their
differences from one at those radii are uniformly bounded, as for normalised disc
cofactors. This estimate is useful for the convergence of normalised Weierstrass
polynomials.
-/

public section

namespace TauCeti.PowerSeries

open _root_.PowerSeries

variable {R : Type*} [SeminormedRing R] {f : PowerSeries R} {r s : ℝ}

/-- Vanishing below degree `N` improves radius monotonicity by the factor `(s / r) ^ N`. -/
theorem gaussNorm_le_mul_pow_div_of_coeff_eq_zero (hr : 0 < r) (hs : 0 ≤ s)
    (hsr : s ≤ r) (hf : f.HasGaussNorm norm r) {N : ℕ}
    (hzero : ∀ n < N, coeff n f = 0) :
    f.gaussNorm norm s ≤ f.gaussNorm norm r * (s / r) ^ N := by
  rw [PowerSeries.gaussNorm_eq]
  refine ciSup_le fun n ↦ ?_
  by_cases hn : n < N
  · simp only [hzero n hn, norm_zero, zero_mul]
    exact mul_nonneg (PowerSeries.gaussNorm_nonneg _ _ _ norm_nonneg) (by positivity)
  · calc
      ‖coeff n f‖ * s ^ n = (‖coeff n f‖ * r ^ n) * (s / r) ^ n := by
        rw [div_pow]
        field_simp
      _ ≤ f.gaussNorm norm r * (s / r) ^ N :=
        mul_le_mul (PowerSeries.le_gaussNorm norm r f hf n)
          (pow_le_pow_of_le_one (by positivity) ((div_le_one hr).mpr hsr) (by omega))
          (by positivity) (PowerSeries.gaussNorm_nonneg _ _ _ norm_nonneg)

/-- With constant coefficient one, the Gauss distance to one contracts by `s / r`
when the radius shrinks. -/
theorem gaussNorm_sub_one_le_mul_div (hr : 0 < r) (hs : 0 ≤ s) (hsr : s ≤ r)
    (hf : (f - 1).HasGaussNorm norm r) (h0 : constantCoeff f = 1) :
    (f - 1).gaussNorm norm s ≤ (f - 1).gaussNorm norm r * (s / r) := by
  simpa using gaussNorm_le_mul_pow_div_of_coeff_eq_zero hr hs hsr hf (N := 1)
    (fun n hn ↦ by
      have : n = 0 := by omega
      subst n
      simp [coeff_zero_eq_constantCoeff_apply, h0])

end TauCeti.PowerSeries
