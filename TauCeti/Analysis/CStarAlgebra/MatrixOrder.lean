/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.Matrix.Order

/-!
# Spectral order and positive semidefiniteness of complex matrices

The spectral order on `CStarMatrix n n ℂ` agrees with the positive-semidefinite order
on ordinary complex matrices. The algebraic star equivalence between the two carriers
preserves and reflects order, independently of their different norm instances.
-/

public section

open scoped MatrixOrder ComplexOrder

namespace CStarMatrix

/-- Positivity in the matrix C⋆-algebra is ordinary positive semidefiniteness. -/
theorem nonneg_iff_posSemidef {n : Type*} [Fintype n]
    {M : CStarMatrix n n ℂ} : 0 ≤ M ↔ (ofMatrix.symm M).PosSemidef := by
  classical
  rw [← Matrix.nonneg_iff_posSemidef]
  simpa only [map_zero, ← ofMatrix_eq_ofMatrixStarAlgEquiv, Equiv.apply_symm_apply] using
    (map_le_map_iff (ofMatrixStarAlgEquiv (n := n) (A := ℂ))
      (a := 0) (b := ofMatrix.symm M))

end CStarMatrix
