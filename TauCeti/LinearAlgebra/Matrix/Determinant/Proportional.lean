/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinants with two proportional columns

Mathlib's `Matrix.det_zero_of_column_eq` says that a matrix with two equal columns has zero
determinant. Over a commutative ring with zero divisors, two columns that are multiples
`x • v` and `y • v` of a common vector need not be scalar multiples of each other, so that
lemma does not apply directly. Multilinearity still gives a vanishing determinant: this is
`Matrix.det_eq_zero_of_column_eq_smul`. A typical instance is a pair of columns that both
vanish outside a single row.
-/

public section

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- A square matrix whose columns `a ≠ b` are multiples `x • v` and `y • v` of a common vector
has zero determinant. No cancellation in `R` is needed. -/
theorem det_eq_zero_of_column_eq_smul {A : Matrix n n R} {a b : n} (hab : a ≠ b)
    {v : n → R} {x y : R} (ha : ∀ i, A i a = x * v i) (hb : ∀ i, A i b = y * v i) :
    A.det = 0 := by
  have hA : A = (A.updateCol a (x • v)).updateCol b (y • v) := by
    ext i k
    by_cases hkb : k = b
    · subst hkb
      simp [hb]
    · by_cases hka : k = a
      · subst hka
        simp [hkb, ha]
      · simp [hkb, hka]
  rw [hA, det_updateCol_smul, updateCol_comm _ hab, det_updateCol_smul,
    det_zero_of_column_eq hab (by simp [hab.symm]), mul_zero, mul_zero]

end Matrix
