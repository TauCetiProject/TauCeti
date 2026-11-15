/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Exponential.Basic
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Norm bounds for integral formal exponentials

If the coefficients of a formal group are mapped into the closed unit ball of a normed
field, its factorial-scaled exponential coefficients also lie in that ball. This estimate
controls the denominators in analytic uses of the formal exponential.
-/

public section

namespace FormalGroup

variable {R K : Type*} [CommRing R] [NormedField K] [Algebra ℚ K]
  (F : FormalGroup R) (f : R →+* K) (hf : ∀ a, ‖f a‖ ≤ 1)

include hf

/-- The factorial-scaled exponential coefficients of an integral formal group have norm at
most one. Here integrality means that the coefficient map takes values in the closed unit
ball. -/
theorem norm_factorial_mul_coeff_exp_le_one (n : ℕ) :
    ‖(n.factorial : K) * PowerSeries.coeff n (F.map f).exp‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := F.factorial_mul_coeff_exp_mem_range f n
  rw [← ha]
  exact hf a

/-- The coefficients of an integral formal exponential are bounded by the inverses of
factorial norms. -/
theorem norm_coeff_exp_le_inv_norm_factorial (n : ℕ) :
    ‖PowerSeries.coeff n (F.map f).exp‖ ≤ ‖(n.factorial : K)‖⁻¹ := by
  have hn : (n.factorial : K) ≠ 0 := by
    simpa only [map_natCast] using
      (map_ne_zero_iff (algebraMap ℚ K) (algebraMap ℚ K).injective).mpr
        (Nat.cast_ne_zero.mpr n.factorial_ne_zero : (n.factorial : ℚ) ≠ 0)
  have h := F.norm_factorial_mul_coeff_exp_le_one f hf n
  rw [norm_mul, mul_comm] at h
  rw [inv_eq_one_div]
  exact (le_div_iff₀ (norm_pos_iff.mpr hn)).mpr h

end FormalGroup
