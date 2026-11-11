/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic

import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.Analysis.Matrix.LDL

/-!
# The `QR` factorization of an invertible matrix

Every invertible matrix `g` over `ℝ` or `ℂ` is `g = U b` with `U` unitary and `b` upper
triangular. This is the `QR` factorization, or the Gram-Schmidt process applied to the columns of
`g`. It is read off the positive-definite Gram matrix `gᴴ g`: an upper triangular `P` with
`Pᴴ (gᴴ g) P = 1` (`Matrix.PosDef.exists_isUpperTriangular_conjTranspose_mul_mul_eq_one`, from the
`LDL` decomposition) makes `U = g P` unitary, and `b = U⁻¹ g = P⁻¹` is upper triangular.

## Main results

* `Matrix.GeneralLinearGroup.exists_mem_upperTriangularGroup_toUnits_mul_eq`: every invertible
  matrix over `ℝ` or `ℂ` is a unitary matrix times an upper triangular one.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 2.1 (the `QR` factorization).
-/

public section

open Matrix TauCeti

open scoped ComplexOrder

namespace Matrix.GeneralLinearGroup

variable {ι 𝕜 : Type*} [Fintype ι] [LinearOrder ι] [RCLike 𝕜]

/-- **Every invertible matrix over `ℝ` or `ℂ` is a unitary matrix times an upper triangular
one**: the `QR` factorization `g = U b`. -/
theorem exists_mem_upperTriangularGroup_toUnits_mul_eq (g : GL ι 𝕜) :
    ∃ U : unitaryGroup ι 𝕜, ∃ b ∈ upperTriangularGroup ι 𝕜, Unitary.toUnits U * b = g := by
  -- an upper triangular `P` normalizing the Gram matrix: `Pᴴ (gᴴ g) P = 1`
  obtain ⟨P, hPB, hP⟩ :=
    (PosDef.conjTranspose_mul_self _ (mulVec_injective_of_isUnit g.isUnit) :
      ((g : Matrix ι ι 𝕜)ᴴ * g).PosDef).exists_isUpperTriangular_conjTranspose_mul_mul_eq_one
  have hU : (g : Matrix ι ι 𝕜) * P ∈ unitaryGroup ι 𝕜 := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_mul]
    simpa only [Matrix.mul_assoc] using hP
  set U : unitaryGroup ι 𝕜 := ⟨_, hU⟩
  -- `(U⁻¹ g)⁻¹ = g⁻¹ U = P` is upper triangular
  have hinv : ((((Unitary.toUnits U)⁻¹ * g)⁻¹ : GL ι 𝕜) : Matrix ι ι 𝕜) = P := by
    have hval : ((Unitary.toUnits U : GL ι 𝕜) : Matrix ι ι 𝕜) = g * P :=
      Unitary.val_toUnits_apply U
    simp [hval, ← Matrix.mul_assoc]
  have hB : (Unitary.toUnits U)⁻¹ * g ∈ upperTriangularGroup ι 𝕜 := by
    rw [← inv_mem_iff, UpperTriangularGroup.mem_iff, hinv]
    exact hPB
  exact ⟨U, _, hB, mul_inv_cancel_left _ _⟩

end Matrix.GeneralLinearGroup
