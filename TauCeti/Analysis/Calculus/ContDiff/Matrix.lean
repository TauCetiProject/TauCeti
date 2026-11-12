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
# Smoothness of determinants and matrix entries

The determinant of a square matrix is a polynomial in its entries, so a matrix-valued map whose
entries are `C^n` has a `C^n` determinant. This is the `C^n` counterpart of Mathlib's
`Continuous.matrix_det`, and holds at every regularity, including analytic regularity.

In the other direction, the entries of the matrix of a `C^n` operator-valued map in bases of the
source and a finite-dimensional target space are `C^n` (`Module.Basis.contDiffOn_repr_apply`).
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

variable [CompleteSpace 𝕜] {U : Set E} {ι κ : Type*} {F F' : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {g : E → F →L[𝕜] F'}

/-- The entries of the matrix of a `C^n` operator-valued function in bases of the source and
finite-dimensional target spaces are `C^n`. -/
theorem contDiffOn_repr_apply (b : Basis ι 𝕜 F) (b' : Basis κ 𝕜 F') [FiniteDimensional 𝕜 F']
    (hg : ContDiffOn 𝕜 n g U) (m : κ) (l : ι) :
    ContDiffOn 𝕜 n (fun x ↦ b'.repr (g x (b l)) m) U :=
  ((b'.coord m).toContinuousLinearMap.contDiff.comp_contDiffOn
    (hg.clm_apply (contDiffOn_const (c := b l)))).congr fun _ _ ↦ by simp

end Module.Basis
