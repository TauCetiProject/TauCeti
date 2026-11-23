/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.SignRight

/-! # Additional lemmas for `Polynomial.signRight`

Over any strictly ordered commutative ring, `Polynomial.signRight` commutes with powers.
-/

public section

namespace Polynomial

/-- Powers raise the right-hand sign to the same power, with the convention `0^0 = 1`. -/
@[simp]
theorem signRight_pow {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (a : R) (p : R[X]) (n : ℕ) :
    signRight a (p ^ n) = signRight a p ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ← C_1, signRight_C, sign_one]
  | succ n ih => simp [pow_succ, signRight_mul, ih]

end Polynomial
