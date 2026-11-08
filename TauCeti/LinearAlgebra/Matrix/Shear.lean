/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic

/-!
# Bounded square-zero matrices

Given a family `B` of rows indexed by a type `α`, with entries in the unit ball of an absolute value
outside the pivot columns, and an embedding `e : α ↪ ι`,
`AbsoluteValue.exists_square_zero_extension` produces a matrix `N` on `ι` with
square zero and entries in the unit ball, supported on the rows `e a` and the columns outside
`range e`, and agreeing with `B` there. Over a ring, `1 - N` and `1 + N` are then mutually inverse
changes of coordinates.

## Main results

* `AbsoluteValue.exists_square_zero_extension`: the existence of such a matrix `N`.
-/

public section

open Set

namespace AbsoluteValue

variable {α ι K : Type*} [Fintype ι] [Semiring K]

/-- A matrix supported on the pivot rows and the non-pivot columns, with entries in the unit ball
whenever those of a given family `B` are on the non-pivot columns, and agreeing with `B` there,
has square zero. -/
theorem exists_square_zero_extension (v : AbsoluteValue K ℝ) (e : α ↪ ι)
    (B : Matrix α ι K)
    (hb : ∀ a j, j ∉ range e → v (B a j) ≤ 1) :
    ∃ N : Matrix ι ι K, N * N = 0 ∧ (∀ i j, v (N i j) ≤ 1) ∧
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
  refine ⟨N, ?_, fun i j ↦ ?_, hcol, fun i hi j ↦ hout hi j, fun a j hj ↦ by simp [hrow, hj]⟩
  · ext i j
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    by_cases hk : k ∈ range e
    · simp [hcol i hk]
    · simp [hout hk j]
  · by_cases hi : i ∈ range e
    · obtain ⟨a, rfl⟩ := hi
      rw [hrow]
      split_ifs with hj
      · simp
      · exact hb a j hj
    · simp [hout hi j]

end AbsoluteValue
