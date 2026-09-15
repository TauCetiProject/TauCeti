/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The standard dot-product bilinear form

This file records symmetry and nondegeneracy of `dotProductBilin` on a finite coordinate space.
These properties make orthogonal complements for the dot product into an exact duality on
finite-dimensional subspaces.
-/

public section

namespace TauCeti

open Matrix
open LinearMap (BilinForm)

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The standard dot-product bilinear form is symmetric. -/
theorem isSymm_dotProductBilin :
    (dotProductBilin R R : BilinForm R (ι → R)).IsSymm :=
  ⟨dotProduct_comm⟩

/-- The standard dot-product bilinear form on a finite coordinate space is nondegenerate. -/
theorem nondegenerate_dotProductBilin :
    (dotProductBilin R R : BilinForm R (ι → R)).Nondegenerate := by
  constructor
  · intro x hx
    exact dotProduct_eq_zero x hx
  · intro y hy
    apply dotProduct_eq_zero y
    intro x
    rw [dotProduct_comm]
    exact hy x

end TauCeti
