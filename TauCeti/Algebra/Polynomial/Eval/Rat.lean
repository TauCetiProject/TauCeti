/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.DenomsClearable
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Rat.Cast.Order

/-!
# Lower bounds for cross evaluations at rational points

For integer polynomials `P, Q` of degree at most `N`, a nonzero value
`P(x) - y Q(x)` at rational points cannot be smaller than
`(den(x)^N den(y))⁻¹`. This is the arithmetic lower bound used when auxiliary
polynomials give a small rational linear form in two approximants.

The proof applies Mathlib's `one_le_pow_mul_abs_eval_div` to
`den(y) P - num(y) Q`; it does not require either polynomial to be nonzero.
-/

public section

namespace TauCeti

open Polynomial

/-- For a nonzero cross evaluation of integer polynomials of degree at most `N`,
`1 ≤ den(x)^N den(y) |P(x) - y Q(x)|`. -/
theorem one_le_den_pow_mul_abs_aeval_sub_mul {P Q : ℤ[X]} {N : ℕ}
    (hP : P.natDegree ≤ N) (hQ : Q.natDegree ≤ N) {x y : ℚ}
    (hne : aeval x P - y * aeval x Q ≠ 0) :
    (1 : ℚ) ≤ (x.den : ℚ) ^ N * y.den * |aeval x P - y * aeval x Q| := by
  let F : ℤ[X] := C (y.den : ℤ) * P - C y.num * Q
  have hF : F.natDegree ≤ N :=
    (natDegree_sub_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans hP) ((natDegree_C_mul_le _ _).trans hQ))
  have heval : aeval x F = (y.den : ℚ) * (aeval x P - y * aeval x Q) := by
    simp [F, mul_sub, ← mul_assoc, Rat.den_mul_eq_num]
  have heval' : (F.map (algebraMap ℤ ℚ)).eval ((x.num : ℚ) / (x.den : ℤ)) =
      (y.den : ℚ) * (aeval x P - y * aeval x Q) := by
    simpa only [Int.cast_natCast, Rat.num_div_den, eval_map_algebraMap] using heval
  have h := one_le_pow_mul_abs_eval_div (K := ℚ) (f := F)
    (a := x.num) (b := x.den) (by exact_mod_cast x.den_pos)
    (by rw [heval']; exact mul_ne_zero (by positivity) hne)
  rw [heval', Int.cast_natCast, abs_mul, abs_of_pos (Nat.cast_pos.2 y.den_pos)] at h
  calc
    (1 : ℚ) ≤ (x.den : ℚ) ^ F.natDegree *
        ((y.den : ℚ) * |aeval x P - y * aeval x Q|) := h
    _ ≤ (x.den : ℚ) ^ N * y.den * |aeval x P - y * aeval x Q| := by
      rw [mul_assoc]
      gcongr
      exact_mod_cast x.den_pos

end TauCeti
