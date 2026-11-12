/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Smoothness of determinants and of basis coordinates

The determinant of a square matrix is a polynomial in its entries, so a matrix-valued map whose
entries are `C^n` has a `C^n` determinant. This is the `C^n` counterpart of Mathlib's
`Continuous.matrix_det`, and holds at every regularity, including analytic regularity.

In the other direction, the coordinates of a `C^n` map into a finite-dimensional space in any basis
are `C^n` (`Module.Basis.contDiffOn_repr_apply`); in particular so are the entries of the matrix of
a `C^n` operator-valued map.
-/

public section

variable {𝕜 E 𝔸 ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Fintype ι] [DecidableEq ι] {n : WithTop ℕ∞}

/-- A matrix-valued map with `C^n` entries has a `C^n` determinant. -/
theorem ContDiff.matrix_det {M : E → Matrix ι ι 𝔸} (hM : ∀ i j, ContDiff 𝕜 n fun x ↦ M x i j) :
    ContDiff 𝕜 n fun x ↦ (M x).det := by
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum fun σ _ ↦ contDiff_const.mul (contDiff_prod fun i _ ↦ hM _ _)

namespace Module.Basis

variable [CompleteSpace 𝕜] {U : Set E} {κ : Type*} {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] {f : E → F}

/-- The coordinates in a basis of a `C^n` map into a finite-dimensional space are `C^n`. -/
theorem contDiffOn_repr_apply (b : Basis κ 𝕜 F) (hf : ContDiffOn 𝕜 n f U) (m : κ) :
    ContDiffOn 𝕜 n (fun x ↦ b.repr (f x) m) U :=
  (b.coord m).toContinuousLinearMap.contDiff.comp_contDiffOn hf

end Module.Basis
