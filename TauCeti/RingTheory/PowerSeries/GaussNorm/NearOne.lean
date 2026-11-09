/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Restricted series close to `1`

A restricted series `U` at a radius `r` is *close to `1`* when `‖U - 1‖_r < 1`. Over a
nonarchimedean coefficient ring with `‖1‖ = 1`, such a series has a constant coefficient of norm
one and Gauss norm `1`. When its constant coefficient is `1` and `r > 0`, closeness to `1` says
exactly that `U` is distinguished of degree `0` at `r`.

## Main results

* `TauCeti.PowerSeries.norm_coeff_mul_pow_le_gaussNorm_sub_one`: the weighted coefficients of `U`
  in positive degrees are bounded by `‖U - 1‖_r`.
* `TauCeti.PowerSeries.norm_constantCoeff_eq_one_of_gaussNorm_sub_one_lt` and
  `TauCeti.PowerSeries.gaussNorm_eq_one_of_gaussNorm_sub_one_lt`: a restricted series close to
  `1` has constant coefficient of norm one and Gauss norm `1`.
* `TauCeti.PowerSeries.gaussNorm_sub_one_lt_one_iff`: a restricted series with constant
  coefficient `1` is close to `1` exactly when it is distinguished of degree `0`.
-/

public section

namespace TauCeti.PowerSeries

open _root_.PowerSeries

variable {R : Type*} [NormedRing R] {r : ℝ} {U : PowerSeries R}

/-- The weighted coefficients of `U` in positive degrees are those of `U - 1`, so they are bounded
by `‖U - 1‖_r`. -/
theorem norm_coeff_mul_pow_le_gaussNorm_sub_one (hU : U.IsRestricted r) {m : ℕ}
    (hm : m ≠ 0) : ‖U.coeff m‖ * r ^ m ≤ (U - 1).gaussNorm norm r := by
  have h := PowerSeries.le_gaussNorm norm r (U - 1)
    (hasGaussNorm_of_isRestricted (hU.sub (PowerSeries.isRestricted_one r))) m
  simpa [coeff_one, hm] using h

variable [NormOneClass R] [IsUltrametricDist R]

/-- If `‖U - 1‖_r < 1` for a restricted series `U`, its constant coefficient has norm one. -/
theorem norm_constantCoeff_eq_one_of_gaussNorm_sub_one_lt (hU : U.IsRestricted r)
    (h : (U - 1).gaussNorm norm r < 1) : ‖constantCoeff U‖ = 1 := by
  have h0 : ‖constantCoeff U - 1‖ < ‖(1 : R)‖ := by
    have := PowerSeries.le_gaussNorm norm r (U - 1)
      (hasGaussNorm_of_isRestricted (hU.sub (PowerSeries.isRestricted_one r))) 0
    simp only [map_sub, coeff_zero_eq_constantCoeff_apply, map_one, pow_zero, mul_one] at this
    simpa using this.trans_lt h
  rw [← sub_add_cancel (constantCoeff U) 1,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h0.ne, max_eq_right h0.le, norm_one]

/-- A restricted series `U` with `‖U - 1‖_r < 1` has Gauss norm `1` at `r`. -/
theorem gaussNorm_eq_one_of_gaussNorm_sub_one_lt (hU : U.IsRestricted r)
    (h : (U - 1).gaussNorm norm r < 1) : U.gaussNorm norm r = 1 := by
  have h0 := norm_constantCoeff_eq_one_of_gaussNorm_sub_one_lt hU h
  rw [gaussNorm_eq_of_forall_le (s := 0)]
  · simpa using h0
  · intro m
    rcases eq_or_ne m 0 with rfl | hm
    · rfl
    · simpa [h0] using ((norm_coeff_mul_pow_le_gaussNorm_sub_one hU hm).trans h.le)

/-- **Restricted series close to `1`.** At a positive radius `r`, a restricted series `U` with
constant coefficient `1` satisfies `‖U - 1‖_r < 1` exactly when it is distinguished of degree `0`
at `r`. -/
theorem gaussNorm_sub_one_lt_one_iff (hr : 0 < r) (hU : U.IsRestricted r)
    (h0 : constantCoeff U = 1) :
    (U - 1).gaussNorm norm r < 1 ↔ IsDistinguished r 0 U := by
  refine ⟨fun h ↦ ⟨?_, fun m hm ↦ ?_⟩, fun hd ↦ ?_⟩
  · simp [gaussNorm_eq_one_of_gaussNorm_sub_one_lt hU h, h0]
  · rw [gaussNorm_eq_one_of_gaussNorm_sub_one_lt hU h]
    exact (norm_coeff_mul_pow_le_gaussNorm_sub_one hU hm.ne').trans_lt h
  · have hU1 : U.gaussNorm norm r = 1 := by
      simpa [h0] using hd.norm_coeff_mul_pow_eq.symm
    -- Truncating `U` past degree `0` leaves its constant term `1`.
    simpa [trunc_one_left, coeff_zero_eq_constantCoeff_apply, h0, hU1] using
      hd.gaussNorm_sub_trunc_lt hr hU

end TauCeti.PowerSeries
