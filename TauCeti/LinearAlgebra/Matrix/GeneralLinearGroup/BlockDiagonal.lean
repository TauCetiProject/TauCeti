/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Matrix.Block

/-!
# The block-diagonal embedding of a product of general linear groups

A tuple `(gᵢ)` of invertible `n × n` matrices indexed by a finite type `ι` gives the invertible
block-diagonal matrix `Matrix.blockDiagonal g` indexed by `n × ι`. This is a group homomorphism
`(ι → GL n R) →* GL (n × ι) R`, whose image is the Levi subgroup `GL n R × ⋯ × GL n R` of the
standard parabolic subgroups with equal blocks. Conjugating by it multiplies the block `X_(i,j)`
of a matrix on the left by `gᵢ` and on the right by `gⱼ⁻¹`.

## Main declarations

* `TauCeti.blockDiagonalGL`: the block-diagonal embedding `(ι → GL n R) →* GL (n × ι) R`.
* `TauCeti.submatrix_blockDiagonalGL_mul_mul_inv`: the blocks of a conjugate by a block-diagonal
  element.
-/

public section

open Matrix

namespace TauCeti

variable (n ι R : Type*) [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] [Semiring R]

/-- The block-diagonal embedding `∏ᵢ GL n R → GL (n × ι) R` of the Levi subgroup. -/
def blockDiagonalGL : (ι → GL n R) →* GL (n × ι) R :=
  (Units.map
      (blockDiagonalRingHom n ι R : (ι → Matrix n n R) →* Matrix (n × ι) (n × ι) R)).comp
    MulEquiv.piUnits.symm.toMonoidHom

variable {n ι R}

@[simp]
theorem coe_blockDiagonalGL (g : ι → GL n R) :
    (blockDiagonalGL n ι R g : Matrix (n × ι) (n × ι) R) =
      blockDiagonal fun i => (g i : Matrix n n R) :=
  (rfl)

/-- The inverse of a Levi element is block diagonal with the inverse blocks. The high `simp`
priority makes this fire before `Matrix.coe_units_inv` turns the left side into the inverse of a
block-diagonal matrix. -/
@[simp high]
theorem coe_blockDiagonalGL_inv (g : ι → GL n R) :
    ((blockDiagonalGL n ι R g)⁻¹ : GL (n × ι) R) =
      (blockDiagonal fun i => ((g i)⁻¹ : GL n R) : Matrix (n × ι) (n × ι) R) := by
  rw [← map_inv, coe_blockDiagonalGL, Pi.inv_def]

/-- The blocks of a conjugate by a Levi element. -/
theorem submatrix_blockDiagonalGL_mul_mul_inv (g : ι → GL n R) (X : Matrix (n × ι) (n × ι) R)
    (i j : ι) :
    ((blockDiagonalGL n ι R g : Matrix (n × ι) (n × ι) R) * X *
        ((blockDiagonalGL n ι R g)⁻¹ : GL (n × ι) R)).submatrix (·, i) (·, j) =
      (g i : Matrix n n R) * X.submatrix (·, i) (·, j) * ((g j)⁻¹ : GL n R) := by
  rw [coe_blockDiagonalGL, coe_blockDiagonalGL_inv, submatrix_blockDiagonal_mul_mul_blockDiagonal]

end TauCeti
