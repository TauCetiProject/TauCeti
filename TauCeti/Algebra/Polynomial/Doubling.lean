/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Polynomials that commute with doubling

Substituting `2 X` for `X` multiplies the coefficient of `X ^ n` by `2 ^ n`
(`Polynomial.comp_C_mul_X_coeff`). For `n ≠ 1` the integer `2 ^ n - 2` is nonzero, so over a ring
without additive torsion (`HasUniqueDiv`), for instance a `ℚ`-algebra or `ℤ`, a polynomial `p`
with `p (2 X) = 2 p (X)` has no coefficient outside degree one: it is `c X` with `c` its linear
coefficient.

This is the eigenvalue computation behind the linearity of additive maps in characteristic
zero: a polynomial map `t ↦ p t` that is additive satisfies `p (2 t) = 2 p (t)`, and so is
linear over a `ℚ`-algebra.

The torsion-freeness hypothesis cannot be dropped: over `ZMod p` with `p` prime, `X ^ p` satisfies
`(2 X) ^ p = 2 X ^ p`, since `2 ^ p = 2` there.

## Main results

* `Polynomial.comp_C_two_mul_X_eq_C_two_mul_iff`: over a ring without additive torsion,
  `p (2 X) = 2 p (X)` exactly when `p = c X` for `c` the linear coefficient of `p`.
-/

public section

namespace Polynomial

variable {A : Type*} [Ring A] [HasUniqueDiv A]

/-- Over a ring without additive torsion, for instance a `ℚ`-algebra or `ℤ`, a polynomial commutes
with doubling, `p (2 X) = 2 p (X)`, exactly when it is linear, `p = c X` for its linear
coefficient `c`. -/
theorem comp_C_two_mul_X_eq_C_two_mul_iff {p : A[X]} :
    p.comp (C 2 * X) = C 2 * p ↔ p = C (p.coeff 1) * X := by
  constructor
  · intro h
    ext n
    rw [coeff_C_mul_X]
    split_ifs with hn
    · rw [hn]
    -- Comparing coefficients of `X ^ n` gives `(2 ^ n - 2) • p.coeff n = 0`.
    have hcoeff : p.coeff n * 2 ^ n = 2 * p.coeff n := by
      simpa only [comp_C_mul_X_coeff, coeff_C_mul] using congrArg (fun q => q.coeff n) h
    have hzero : ((2 : ℤ) ^ n - 2) • p.coeff n = 0 := by
      rw [zsmul_eq_mul, Int.cast_sub, Int.cast_pow, Int.cast_ofNat, sub_mul,
        ((Commute.ofNat_left 2 _).pow_left n).eq, hcoeff, sub_self]
    -- The integer `2 ^ n - 2` is nonzero, so it cancels in the torsion-free group `A`.
    have hq : (2 : ℤ) ^ n - 2 ≠ 0 := by
      intro h0
      have hn' : (2 : ℕ) ^ n = 2 ^ 1 := by exact_mod_cast sub_eq_zero.mp h0
      exact hn (Nat.pow_right_injective le_rfl hn')
    exact (IsAddTorsionFree.zsmul_eq_zero_iff_right hq).mp hzero
  · intro h
    rw [h, C_mul_comp, X_comp, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul,
      (Commute.ofNat_right _ 2).eq]

end Polynomial
