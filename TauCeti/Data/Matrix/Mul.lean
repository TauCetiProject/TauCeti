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

If the entries of a product of matrices are not all zero, then the inner index type is nonempty and
the entries of neither factor are all zero.

## Main results

* `Matrix.pow_apply_pos_of_le`: if `A` is entrywise nonnegative and `A ^ k` is strictly positive
  for some `k > 0`, then so is `A ^ m` for every `m ≥ k`.
* `Matrix.nonempty_and_entries_ne_zero_of_mul`: if the entries of a product are not all zero, the
  inner index is nonempty and the entries of neither factor are all zero.
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

/-- If the entries of a matrix product are not all zero, then the inner index type is nonempty and
the entries of neither factor are all zero. -/
theorem nonempty_and_entries_ne_zero_of_mul (A : Matrix m n K) (B : Matrix n p K)
    (hc : (fun q : m × p ↦ (A * B) q.1 q.2) ≠ 0) :
    Nonempty n ∧ (fun q : m × n ↦ A q.1 q.2) ≠ 0 ∧ (fun q : n × p ↦ B q.1 q.2) ≠ 0 := by
  refine ⟨?_, fun ha ↦ hc ?_, fun hb ↦ hc ?_⟩
  · by_contra hn
    have := not_nonempty_iff.mp hn
    exact hc (funext fun q ↦ by simp [Matrix.mul_apply])
  · have hA : A = 0 := Matrix.ext fun i j ↦ congrFun ha (i, j)
    exact funext fun q ↦ by simp [hA]
  · have hB : B = 0 := Matrix.ext fun i j ↦ congrFun hb (i, j)
    exact funext fun q ↦ by simp [hB]

end NonUnitalNonAssocSemiring

end Matrix
