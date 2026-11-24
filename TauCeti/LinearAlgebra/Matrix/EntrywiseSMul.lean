/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Entrywise scaling of matrices by real weights

Scaling the entry `(i, j)` of a matrix `Y` with entries in a real vector space `E` by `r i j` is a
real linear endomorphism of `Matrix m n E`, multiplicative and additive in the weights `r`.

## Main definitions

* `Matrix.entrywiseSMulAlgHom`: entrywise scaling by a matrix of real weights, as an algebra
  homomorphism into the real endomorphisms of `Matrix m n E`.
-/

public section

namespace Matrix

variable {m n : Type*}

/-- Entrywise scaling by a real matrix of weights, as a real algebra homomorphism from the weights
to the real linear endomorphisms of `Matrix m n E`. -/
def entrywiseSMulAlgHom (E : Type*) [AddCommGroup E] [Module ℝ E] :
    (m → n → ℝ) →ₐ[ℝ] Module.End ℝ (Matrix m n E) where
  toFun r :=
    { toFun Y := of fun i j ↦ r i j • Y i j
      map_add' Y Z := by ext i j; simp [smul_add]
      map_smul' c Y := by ext i j; simp [smul_comm (r i j) c] }
  map_one' := by ext Y i j; simp
  map_mul' r s := by ext Y i j; simp [mul_smul]
  map_zero' := by ext Y i j; simp
  map_add' r s := by ext Y i j; simp [add_smul]
  commutes' c := by ext Y i j; simp

/-- `entrywiseSMulAlgHom E r Y` is the matrix with entries `r i j • Y i j`. -/
theorem entrywiseSMulAlgHom_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : m → n → ℝ) (Y : Matrix m n E) :
    entrywiseSMulAlgHom E r Y = of fun i j ↦ r i j • Y i j :=
  (rfl)

/-- The entry `(i, j)` of `entrywiseSMulAlgHom E r Y` is `r i j • Y i j`. -/
@[simp]
theorem entrywiseSMulAlgHom_apply_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    (r : m → n → ℝ) (Y : Matrix m n E) (i : m) (j : n) :
    entrywiseSMulAlgHom E r Y i j = r i j • Y i j :=
  (rfl)

end Matrix
