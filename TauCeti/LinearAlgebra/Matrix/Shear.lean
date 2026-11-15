/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul

/-!
# Square-zero matrices supported on pivot rows

Given a family `B` of rows indexed by a type `α` and an embedding `e : α ↪ ι`,
`Matrix.exists_mul_self_eq_zero_extension` produces a matrix `N` on `ι` with square zero,
supported on the rows `e a` and the columns outside `range e`, and agreeing with `B` there. Over
a ring, `1 - N` and `1 + N` are then mutually inverse changes of coordinates.

## Main results

* `Matrix.exists_mul_self_eq_zero_extension`: the existence of such a matrix `N`.
-/

public section

open Set

namespace Matrix

variable {α ι K : Type*} [Fintype ι] [NonUnitalNonAssocSemiring K]

/-- Given `B : Matrix α ι K` and an embedding `e : α ↪ ι`, there is a matrix `N` on `ι` with
`N * N = 0` that vanishes outside the rows `e a` and on the columns in `range e`, and satisfies
`N (e a) j = B a j` for `j ∉ range e`. -/
theorem exists_mul_self_eq_zero_extension (B : Matrix α ι K) (e : α ↪ ι) :
    ∃ N : Matrix ι ι K, N * N = 0 ∧
      (∀ i, ∀ j ∈ range e, N i j = 0) ∧ (∀ i ∉ range e, ∀ j, N i j = 0) ∧
      ∀ a j, j ∉ range e → N (e a) j = B a j := by
  classical
  let N : Matrix ι ι K := Matrix.of
    (Function.extend e (fun a j ↦ if j ∈ range e then 0 else B a j) 0)
  have hrow (a : α) (j : ι) : N (e a) j = if j ∈ range e then 0 else B a j := by
    simp [N, e.injective.extend_apply]
  have hout {i : ι} (hi : i ∉ range e) (j : ι) : N i j = 0 := by
    simp [N, Function.extend_apply' _ _ _ hi]
  have hcol (i : ι) {j : ι} (hj : j ∈ range e) : N i j = 0 := by
    by_cases hi : i ∈ range e
    · obtain ⟨a, rfl⟩ := hi
      simp [hrow, hj]
    · exact hout hi j
  refine ⟨N, ?_, hcol, fun i hi j ↦ hout hi j, fun a j hj ↦ by simp [hrow, hj]⟩
  ext i j
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hk : k ∈ range e
  · simp [hcol i hk]
  · simp [hout hk j]

end Matrix
