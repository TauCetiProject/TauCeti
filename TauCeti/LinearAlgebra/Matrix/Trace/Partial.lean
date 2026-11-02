/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The partial trace of a matrix on a product index

For a square matrix `Y` with rows and columns indexed by `m × n`, the *partial trace over the
second factor* is the `m × m` matrix `Matrix.partialTraceRight Y` with entries
`∑ k, Y (i, k) (j, k)`, the sum of the diagonal blocks `Matrix.blockDiag Y k`. When the index
`m × n` labels the monomial basis of a tensor product of two finite-dimensional spaces, this is
the partial trace `Tr₂` of quantum mechanics, which forgets the second subsystem.

The partial trace preserves the trace, `Matrix.trace_partialTraceRight`, sends a Kronecker product
`A ⊗ₖ B` to `Tr B • A`, `Matrix.partialTraceRight_kronecker`, sends `1` to `card n • 1`,
`Matrix.partialTraceRight_one`, and is a bimodule map over the first factor:
`Tr₂ ((A ⊗ₖ 1) * Y * (B ⊗ₖ 1)) = A * Tr₂ Y * B`
(`Matrix.partialTraceRight_kronecker_one_mul`, `Matrix.partialTraceRight_mul_kronecker_one`). It
commutes with conjugate transposition and preserves positive semidefiniteness, since each
diagonal block is a compression of `Y`.
-/

public section

open scoped Kronecker

namespace Matrix

variable {R m n : Type*} [Fintype n]

section AddCommMonoid

variable [AddCommMonoid R]

/-- The **partial trace** over the second factor of a square matrix indexed by `m × n`: the
`m × m` matrix with entries `∑ k, Y (i, k) (j, k)`, the sum of the diagonal blocks of `Y`. -/
def partialTraceRight (Y : Matrix (m × n) (m × n) R) : Matrix m m R :=
  ∑ k, blockDiag Y k

@[simp]
theorem partialTraceRight_apply (Y : Matrix (m × n) (m × n) R) (i j : m) :
    partialTraceRight Y i j = ∑ k, Y (i, k) (j, k) := by
  simp [partialTraceRight, sum_apply, blockDiag_apply]

@[simp]
theorem partialTraceRight_zero : partialTraceRight (0 : Matrix (m × n) (m × n) R) = 0 := by
  ext
  simp

@[simp]
theorem partialTraceRight_add (Y Z : Matrix (m × n) (m × n) R) :
    partialTraceRight (Y + Z) = partialTraceRight Y + partialTraceRight Z := by
  ext
  simp [Finset.sum_add_distrib]

@[simp]
theorem partialTraceRight_smul {α : Type*} [DistribSMul α R] (c : α)
    (Y : Matrix (m × n) (m × n) R) :
    partialTraceRight (c • Y) = c • partialTraceRight Y := by
  ext
  simp [Finset.smul_sum]

/-- The partial trace preserves the trace. -/
@[simp]
theorem trace_partialTraceRight [Fintype m] (Y : Matrix (m × n) (m × n) R) :
    trace (partialTraceRight Y) = trace Y := by
  simp [trace, Fintype.sum_prod_type]

/-- The partial trace commutes with conjugate transposition. -/
@[simp]
theorem partialTraceRight_conjTranspose [StarAddMonoid R] (Y : Matrix (m × n) (m × n) R) :
    partialTraceRight Yᴴ = (partialTraceRight Y)ᴴ := by
  ext
  simp [star_sum]

end AddCommMonoid

section Semiring

/-- The partial trace of a Kronecker product `A ⊗ₖ B` is `Tr B • A`. -/
@[simp]
theorem partialTraceRight_kronecker [CommSemiring R] (A : Matrix m m R) (B : Matrix n n R) :
    partialTraceRight (A ⊗ₖ B) = trace B • A := by
  ext
  simp [trace, Finset.sum_mul, mul_comm (A _ _)]

/-- The partial trace of the identity is `card n • 1`. -/
@[simp]
theorem partialTraceRight_one [NonAssocSemiring R] [DecidableEq m] [DecidableEq n] :
    partialTraceRight (1 : Matrix (m × n) (m × n) R) = (Fintype.card n : R) • 1 := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

variable [Semiring R] [Fintype m] [DecidableEq n]

/-- The partial trace is left linear over the first factor:
`Tr₂ ((A ⊗ₖ 1) * Y) = A * Tr₂ Y`. -/
theorem partialTraceRight_kronecker_one_mul (A : Matrix m m R) (Y : Matrix (m × n) (m × n) R) :
    partialTraceRight ((A ⊗ₖ (1 : Matrix n n R)) * Y) = A * partialTraceRight Y := by
  ext i j
  simp only [partialTraceRight_apply, mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [one_apply, Finset.mul_sum]

/-- The partial trace is right linear over the first factor:
`Tr₂ (Y * (B ⊗ₖ 1)) = Tr₂ Y * B`. -/
theorem partialTraceRight_mul_kronecker_one (Y : Matrix (m × n) (m × n) R) (B : Matrix m m R) :
    partialTraceRight (Y * (B ⊗ₖ (1 : Matrix n n R))) = partialTraceRight Y * B := by
  ext i j
  simp only [partialTraceRight_apply, mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [one_apply, Finset.sum_mul]

end Semiring

/-- The partial trace of a positive semidefinite matrix is positive semidefinite: it is the sum of
the compressions of `Y` to the diagonal blocks. -/
theorem PosSemidef.partialTraceRight [Ring R] [PartialOrder R] [StarRing R]
    [AddLeftMono R] {Y : Matrix (m × n) (m × n) R} (hY : Y.PosSemidef) :
    Y.partialTraceRight.PosSemidef := by
  have hblock (k : n) : blockDiag Y k = Y.submatrix (·, k) (·, k) := by
    ext
    simp [blockDiag_apply]
  exact posSemidef_sum _ fun k _ => hblock k ▸ hY.submatrix _

end Matrix
