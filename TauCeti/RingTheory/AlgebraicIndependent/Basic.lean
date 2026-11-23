/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import TauCeti.LinearAlgebra.LinearIndependent.Matrix

/-!
# Linear combinations of algebraically independent families

If the linear combinations `i ↦ ∑ j, C i j • x j` formed from a matrix `C : Matrix ι κ R` in an
`R`-algebra `A` are algebraically independent over `R`, then the rows of `C` are `R`-linearly
independent (`AlgebraicIndependent.linearIndependent_row`).

## Main results

* `AlgebraicIndependent.linearIndependent_row`: algebraic independence of `i ↦ ∑ j, C i j • x j`
  implies `LinearIndependent R C.row`.
-/

public section

namespace AlgebraicIndependent

/-- If the linear combinations `i ↦ ∑ j, C i j • x j` in an `R`-algebra `A` are algebraically
independent over `R`, then the rows of `C` are `R`-linearly independent. -/
theorem linearIndependent_row {ι κ R A : Type*} [Fintype κ] [CommRing R] [CommRing A]
    [Algebra R A] {C : Matrix ι κ R} {x : κ → A}
    (hy : AlgebraicIndependent R fun i ↦ ∑ j, C i j • x j) :
    LinearIndependent R C.row :=
  hy.linearIndependent.row_of_sum_smul

end AlgebraicIndependent
