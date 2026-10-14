/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Scalar orthogonal matrices

A scalar matrix `c • 1` over a nonempty index type lies in the orthogonal group of the standard
symmetric form only when `c ^ 2 = 1`. For an empty index type every scalar qualifies.

## Main declarations

* `TauCeti.sq_eq_one_of_smul_one_mem_orthogonalGroup`: a scalar orthogonal matrix over a nonempty
  index type has scalar a square root of one.
-/

public section

namespace TauCeti

/-- A scalar matrix preserving the standard symmetric form has scalar a square root of one,
provided the index type is nonempty: the orthogonality relation reads `c ^ 2 • 1 = 1`. -/
theorem sq_eq_one_of_smul_one_mem_orthogonalGroup {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {R : Type*} [CommRing R] {c : R}
    (h : c • (1 : Matrix n n R) ∈ Matrix.orthogonalGroup n R) : c ^ 2 = 1 := by
  rw [Matrix.mem_orthogonalGroup_iff] at h
  have hentry := congrFun (congrFun h (Classical.arbitrary n)) (Classical.arbitrary n)
  simpa [sq] using hentry

end TauCeti
