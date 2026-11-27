/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Isocrystal
import Mathlib.RingTheory.WittVector.DiscreteValuationRing

/-!
# Frobenius on the fraction field of the Witt vectors

Let `k` be a perfect domain of characteristic `p`, and let `K(p, k)` be the fraction field of the
Witt vectors `W(k)` (which is `W(k)[1/p]` when `k` is a field), with the Frobenius `φ(p, k)`
extended from `W(k)`. The Frobenius preserves the `p`-adic valuation, so the equation
`φ(a) p ^ n = a` with `n ≥ 1` has no solution `a ≠ 0`. This is the input needed to show that a
monodromy operator `N` with `N Φ = p Φ N` on a finite-dimensional isocrystal is nilpotent.

## Main results

* `WittVector.FractionRing.eq_zero_of_frobenius_mul_p_pow_eq`: in `K(p, k)`,
  `φ(a) p ^ n = a` with `n ≥ 1` forces `a = 0`.
-/

public section

open scoped Isocrystal

namespace WittVector.FractionRing

variable (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [IsDomain k] [CharP k p]
  [PerfectRing k p]

/-- In the fraction field `K(p, k)` of the Witt vectors `W(k)` of a perfect domain `k` of
characteristic `p` (which is `W(k)[1/p]` when `k` is a field), the equation `φ(a) p ^ n = a` with
`n ≥ 1` only has the solution `a = 0`. -/
theorem eq_zero_of_frobenius_mul_p_pow_eq {a : K(p, k)} {n : ℕ} (hn : n ≠ 0)
    (ha : φ(p, k) a * (p : K(p, k)) ^ n = a) : a = 0 := by
  by_contra ha0
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := WittVector p k) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at ha0
  have hinj := IsFractionRing.injective (WittVector p k) K(p, k)
  have hσ (z : WittVector p k) : φ(p, k) (algebraMap (WittVector p k) K(p, k) z) =
      algebraMap (WittVector p k) K(p, k) (WittVector.frobenius z) := by
    -- `φ(p, k)` is the ring map underlying the extension of `frobeniusEquiv p k` to `K(p, k)`.
    simp [FractionRing.frobeniusRingHom, FractionRing.frobenius]
  have hAy : algebraMap (WittVector p k) K(p, k) y ≠ 0 := by simpa using hinj.ne hy0
  have hAFy : algebraMap (WittVector p k) K(p, k) (WittVector.frobenius y) ≠ 0 := by
    have : WittVector.frobenius y ≠ 0 := by simpa using (frobenius_bijective p k).injective.ne hy0
    simpa using hinj.ne this
  -- Clear denominators: `F(x) p ^ n y = x F(y)` in `W(k)`.
  have hW :
      WittVector.frobenius x * (p : WittVector p k) ^ n * y = x * WittVector.frobenius y := by
    apply hinj
    rw [map_div₀, hσ, hσ] at ha
    simp only [map_mul, map_pow, map_natCast]
    field_simp at ha
    linear_combination ha
  -- Write `x = p ^ m u` and `y = p ^ l w` with `u, w` of nonzero constant coefficient; after
  -- cancelling `p ^ (m + l)`, the constant coefficients give `0 = u₀ w₀ ^ p`.
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_p_mul x hx0
  obtain ⟨l, w, hw, rfl⟩ := exists_eq_pow_p_mul y hy0
  simp only [map_mul, map_pow, map_natCast] at hW
  have hcancel :
      WittVector.frobenius u * (p : WittVector p k) ^ n * w = u * WittVector.frobenius w := by
    apply mul_left_cancel₀ (pow_ne_zero (m + l) (WittVector.p_ne_zero p k))
    linear_combination hW
  have h0 := congrArg WittVector.constantCoeff hcancel
  simp only [map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_pow hn, mul_zero, zero_mul,
    WittVector.constantCoeff_apply, coeff_frobenius_charP] at h0
  exact mul_ne_zero hu (pow_ne_zero _ hw) h0.symm

end WittVector.FractionRing
