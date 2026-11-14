/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi

/-!
# Linear independence of matrix rows from linear combinations

If the linear combinations `i ↦ ∑ j, C i j • x j` formed from a matrix `C : Matrix ι κ R` and a
finite family `x : κ → M` are `R`-linearly independent, then the rows `C.row` of `C` are
`R`-linearly independent (`LinearIndependent.row_of_sum_smul`).

## Main results

* `LinearIndependent.row_of_sum_smul`: linear independence of `i ↦ ∑ j, C i j • x j` implies
  `LinearIndependent R C.row`.
-/

public section

namespace LinearIndependent

/-- If the linear combinations `i ↦ ∑ j, C i j • x j` in an `R`-module `M` are `R`-linearly
independent, then the rows of `C` are `R`-linearly independent. -/
theorem row_of_sum_smul {ι κ R M : Type*} [Fintype κ] [Semiring R] [AddCommMonoid M] [Module R M]
    {C : Matrix ι κ R} {x : κ → M}
    (hy : LinearIndependent R fun i ↦ ∑ j, C i j • x j) :
    LinearIndependent R C.row := by
  let L : (κ → R) →ₗ[R] M := ∑ j : κ, (LinearMap.proj j).smulRight (x j)
  have hL : (fun i ↦ ∑ j, C i j • x j) = L ∘ C.row := by
    funext i
    simp [L, Matrix.row_apply]
  exact LinearIndependent.of_comp L (hL ▸ hy)

end LinearIndependent
