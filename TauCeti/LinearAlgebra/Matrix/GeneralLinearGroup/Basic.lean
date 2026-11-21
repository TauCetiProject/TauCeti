/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Basic properties of the general linear group

General facts about invertible matrices in `GL n R` (`Matrix.GeneralLinearGroup n R`) that require
only a semiring and do not depend on diagonal, triangular, or elementary subgroup structure.

## Main results

* `Matrix.GeneralLinearGroup.exists_apply_ne_zero_col`: every invertible matrix over a nontrivial
  semiring has at least one nonzero entry in each column.
-/

public section

namespace Matrix.GeneralLinearGroup

/-- Every invertible matrix over a nontrivial semiring has at least one nonzero entry in each
column. -/
theorem exists_apply_ne_zero_col {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]
    [Nontrivial R] (g : GL n R) (j : n) : ∃ i : n, g i j ≠ 0 := by
  by_contra h
  have hzero : ∀ i, g i j = 0 := fun i ↦ Classical.not_not.1 fun hi ↦ h ⟨i, hi⟩
  have h1 := congrFun (congrFun g.inv_mul j) j
  simp [Matrix.mul_apply, hzero] at h1

end Matrix.GeneralLinearGroup
