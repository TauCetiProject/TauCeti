/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Analysis.Real.Sqrt

/-!
# Infinite-place values of norm-one elements and square roots

Multiplication by an element of relative norm one in a CM field preserves absolute values
at infinity. A square root of `-d` for `d : ℕ` contributes a factor `√d`. This gives the
placewise size formula for the normalized different generator in
`New.Parameters.infinitePlace_apply_deltaE` in lsernau/grh-lean
(`grh/src/New/Derivatives/Field/PrimeDecomposition.lean`, revision `72fead1`).
-/

public section

open NumberField.IsCMField

namespace NumberField.InfinitePlace

/-- An element whose square is `-d`, for `d : ℕ`, has absolute value `√d` at every infinite
place. -/
theorem apply_eq_sqrt_of_sq_eq_neg_natCast {E : Type*} [Field E] (v : InfinitePlace E)
    {b : E} {d : ℕ} (hb : b ^ 2 = -(d : E)) : v b = √(d : ℝ) := by
  have hs : v b ^ 2 = (d : ℝ) := by
    rw [← map_pow, hb, ← norm_embedding_eq]
    simp
  rw [← hs, Real.sqrt_sq (apply_nonneg v b)]

/-- A norm-one element of a CM field has absolute value one at every infinite place. -/
theorem apply_eq_one_of_mul_complexConj_eq_one {E : Type*} [Field E] [CharZero E]
    [IsCMField E] [Algebra.IsIntegral ℚ E] (v : InfinitePlace E) {c : E}
    (hc : c * complexConj E c = 1) : v c = 1 := by
  have hc' : v c * v c = 1 := by simpa using congrArg v hc
  exact (sq_eq_sq₀ (apply_nonneg v c) zero_le_one).mp (by simpa [sq] using hc')

/-- A norm-one correction does not change the infinite-place value of `a`, and multiplying
by a square root of `-d` scales it by `√d`. -/
theorem apply_mul_mul_eq_mul_sqrt_of_mul_complexConj_eq_one {E : Type*} [Field E] [CharZero E]
    [IsCMField E] [Algebra.IsIntegral ℚ E] (v : InfinitePlace E) {a b c : E} {d : ℕ}
    (hc : c * complexConj E c = 1) (hb : b ^ 2 = -(d : E)) :
    v (c * a * b) = v a * √(d : ℝ) := by
  simp only [map_mul, v.apply_eq_one_of_mul_complexConj_eq_one hc,
    v.apply_eq_sqrt_of_sq_eq_neg_natCast hb, one_mul]

end NumberField.InfinitePlace
