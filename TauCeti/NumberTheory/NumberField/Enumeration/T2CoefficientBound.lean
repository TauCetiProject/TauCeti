/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.NumberField.Enumeration.T2
import Mathlib.RingTheory.Polynomial.Vieta
import TauCeti.Analysis.Normed.Ring.ElementarySymmetric

/-!
# Coefficient bounds from the `T₂` root norm

Vieta's formula and the root-mean-square bound on elementary symmetric functions give a
binomial coefficient bound on each coefficient of a monic polynomial in terms of `T₂`.
-/

public section

namespace Polynomial

/-- For a monic complex polynomial of degree `n`, the norm of the coefficient of `X^(n-k)`
is at most `n.choose k * (T₂ / n)^(k/2)` for `k ≤ n`. The monic constant case is included. -/
theorem norm_coeff_le_of_complexT2 {p : ℂ[X]} (hp : p.Monic) {k : ℕ} (hk : k ≤ p.natDegree) :
    ‖p.coeff (p.natDegree - k)‖ ≤
      (p.natDegree.choose k : ℝ) * (p.complexT2 / p.natDegree) ^ ((k : ℝ) / 2) := by
  have hcard := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hv := coeff_eq_esymm_roots_of_card hcard (Nat.sub_le p.natDegree k)
  rw [Nat.sub_sub_self hk, hp.leadingCoeff, one_mul] at hv
  rw [hv, Real.rpow_div_two_eq_sqrt _ (div_nonneg p.complexT2_nonneg (Nat.cast_nonneg _)),
    Real.rpow_natCast, complexT2_def, ← hcard]
  simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using
    p.roots.norm_esymm_le_choose_mul_sqrt_mean_sq_pow k

/-- The coefficient bound in terms of `T₂` for monic integer polynomials. -/
theorem abs_coeff_le_of_t2 {p : ℤ[X]} (hp : p.Monic) {k : ℕ} (hk : k ≤ p.natDegree) :
    |(p.coeff (p.natDegree - k) : ℝ)| ≤
      (p.natDegree.choose k : ℝ) * (p.t2 / p.natDegree) ^ ((k : ℝ) / 2) := by
  have hdeg := hp.natDegree_map (Int.castRingHom ℂ)
  have hbound := norm_coeff_le_of_complexT2 (hp.map (Int.castRingHom ℂ))
    (k := k) (hdeg.symm ▸ hk)
  simpa only [complexT2_map_intCast, hdeg, coeff_map, Int.coe_castRingHom, Complex.norm_intCast]
    using hbound

-- The root norm uses absolute values: the power sum of the squared roots here would be `-2`.
example : (X ^ 2 + 1 : ℤ[X]).t2 = 2 := by
  have hsq : (C Complex.I : ℂ[X]) ^ 2 = -1 := by rw [← map_pow, Complex.I_sq, map_neg, C_1]
  have hfactor : (X ^ 2 + 1 : ℂ[X]) = (X - C Complex.I) * (X - C (-Complex.I)) := by
    rw [C_neg, sub_neg_eq_add, mul_comm, ← sq_sub_sq, hsq, sub_neg_eq_add]
  rw [← complexT2_map_intCast, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_one,
    hfactor, complexT2_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)]
  simp only [complexT2_X_sub_C, norm_neg, Complex.norm_I, one_pow]
  norm_num

end Polynomial
