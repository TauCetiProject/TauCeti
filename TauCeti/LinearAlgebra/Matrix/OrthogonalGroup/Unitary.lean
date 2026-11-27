/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OfReal

/-!
# The real orthogonal group in the complex unitary group

A real orthogonal matrix `g ∈ O(n)` is unitary as a complex matrix
(`Matrix.map_ofReal_mem_unitaryGroup`), and the entrywise coercion is multiplicative, so `O(n)`
is a subgroup of `U(n)`.

## Main definitions

* `TauCeti.orthogonalComplexMatrix`: the complex unitary matrix of `g ∈ O(n)`, as a monoid
  morphism `O(n) →* U(n)`.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The complex matrix of an element of `O(n)`, a unitary matrix. -/
def orthogonalComplexMatrix : orthogonalGroup n ℝ →* unitaryGroup n ℂ where
  toFun g := ⟨(g : Matrix n n ℝ).map (↑), map_ofReal_mem_unitaryGroup g.property⟩
  map_one' := Subtype.ext map_ofReal_one
  map_mul' g h := Subtype.ext (by simp)

/-- The entries of the complex matrix of `g ∈ O(n)`. -/
@[simp]
theorem orthogonalComplexMatrix_apply (g : orthogonalGroup n ℝ) (i j : n) :
    (orthogonalComplexMatrix g : Matrix n n ℂ) i j = ((g : Matrix n n ℝ) i j : ℂ) := by
  simp [orthogonalComplexMatrix]

end TauCeti
