/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul

/-!
# Matrix products: positivity of powers and nonvanishing of factors

Over a strictly ordered semiring, once some power `A ^ k` with `k > 0` of an entrywise nonnegative
square matrix `A` is strictly positive, every later power is strictly positive too: each row of `A`
has a positive entry, so multiplying a strictly positive matrix by `A` on the left keeps it
strictly positive. This is the form in which positivity propagates along the powers of a primitive
matrix.

If a product of matrices is nonzero, then the inner index type is nonempty and neither factor is
zero.

## Main results

* `Matrix.pow_apply_pos_of_le`: if `A` is entrywise nonnegative and `A ^ k` is strictly positive
  for some `k > 0`, then so is `A ^ m` for every `m ≥ k`.
* `Matrix.nonempty_of_mul_ne_zero`, `Matrix.left_ne_zero_of_mul_ne_zero`,
  `Matrix.right_ne_zero_of_mul_ne_zero`: if a matrix product is nonzero, then the inner index type
  is nonempty and neither factor is zero.
-/

public section

open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section StrictOrderedSemiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {A : Matrix n n R}

/-- If `A` is entrywise nonnegative and its power `A ^ k`, for some `k > 0`, is strictly positive,
then every power `A ^ m` with `m ≥ k` is strictly positive. -/
theorem pow_apply_pos_of_le (hA : ∀ i j, 0 ≤ A i j) {k : ℕ} (hk : 0 < k)
    (hAk : ∀ i j, 0 < (A ^ k) i j) {m : ℕ} (hkm : k ≤ m) : ∀ i j, 0 < (A ^ m) i j := by
  -- Every row of `A` has a positive entry, since `A ^ k = A * A ^ (k - 1)` does.
  have hrow : ∀ i, ∃ l, 0 < A i l := fun i => by
    have h := hAk i i
    rw [← Nat.sub_add_cancel hk, pow_succ', Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
    exact ⟨l, (hA i l).lt_of_ne' (left_ne_zero_of_mul hl)⟩
  induction m, hkm using Nat.le_induction with
  | base => exact hAk
  | succ m _ ih =>
    intro i j
    obtain ⟨l, hl⟩ := hrow i
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_pos' (fun l _ => mul_nonneg (hA i l) (ih l j).le)
      ⟨l, Finset.mem_univ l, mul_pos hl (ih l j)⟩

end StrictOrderedSemiring

section NonUnitalNonAssocSemiring

variable {K : Type*} [NonUnitalNonAssocSemiring K] {m n p : Type*} [Fintype n]

/-- If a matrix product is nonzero, then the inner index type is nonempty. -/
theorem nonempty_of_mul_ne_zero {A : Matrix m n K} {B : Matrix n p K} (h : A * B ≠ 0) :
    Nonempty n := by
  by_contra hn
  have := not_nonempty_iff.mp hn
  exact h (Matrix.ext fun i j ↦ by simp [Matrix.mul_apply])

/-- If a matrix product is nonzero, then its left factor is nonzero. -/
theorem left_ne_zero_of_mul_ne_zero {A : Matrix m n K} {B : Matrix n p K} (h : A * B ≠ 0) :
    A ≠ 0 := fun hA ↦ h (by simp [hA])

/-- If a matrix product is nonzero, then its right factor is nonzero. -/
theorem right_ne_zero_of_mul_ne_zero {A : Matrix m n K} {B : Matrix n p K} (h : A * B ≠ 0) :
    B ≠ 0 := fun hB ↦ h (by simp [hB])

end NonUnitalNonAssocSemiring

end Matrix
