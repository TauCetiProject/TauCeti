/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Data.Matrix.Block

/-!
# Matrices acting on vectors with entries in a topological module

A matrix `A : Matrix κ ι R` acts on vectors `x : ι → M` with entries in an `R`-module `M` by
`k ↦ ∑ i, A k i • x i`. When `M` is a topological additive monoid on which each scalar acts
continuously, this is the continuous additive map `Matrix.smulVecHom A M : (ι → M) →ₜ+ (κ → M)`,
and it is functorial in the matrix (`Matrix.smulVecHom_one`, `Matrix.smulVecHom_mul`). For `M = R`
it is `Matrix.mulVec` (`Matrix.smulVecHom_self_apply`).

The upper-right block projection and the matching insertion are continuous linear maps over
any semiring and topological module, with arbitrary row and column index types. Their application
lemmas are `Matrix.toBlocks₁₂CLM_apply` and `Matrix.fromBlocks₁₂CLM_apply`.

## Main definitions

* `Matrix.smulVecHom`: the continuous additive action of a matrix on module-valued vectors.
* `Matrix.toBlocks₁₂CLM`: projection onto the upper-right block as a continuous linear map.
* `Matrix.fromBlocks₁₂CLM`: insertion into the upper-right block as a continuous linear map.

The motivating case is `R = ℤ` and `M = AddCircle p`, where an integer matrix induces a map of
tori `(ι → AddCircle p) → (κ → AddCircle p)`.
-/

public section

namespace Matrix

variable {ι κ μ R : Type*} [Fintype ι] [Semiring R] (A : Matrix κ ι R)
  (M : Type*) [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul R M]

/-- The continuous additive map `(ι → M) →ₜ+ (κ → M)` induced by a matrix `A` with entries in `R`,
sending `x` to `k ↦ ∑ i, A k i • x i`. -/
def smulVecHom : (ι → M) →ₜ+ (κ → M) where
  toFun x k := ∑ i, A k i • x i
  map_zero' := by ext k; simp
  map_add' x y := by ext k; simp [smul_add, Finset.sum_add_distrib]
  continuous_toFun := by fun_prop

@[simp]
theorem smulVecHom_apply (x : ι → M) (k : κ) : A.smulVecHom M x k = ∑ i, A k i • x i :=
  (rfl)

/-- For `M = R`, the induced map is `Matrix.mulVec`. -/
@[simp]
theorem smulVecHom_self_apply [TopologicalSpace R] [ContinuousAdd R] [ContinuousConstSMul R R]
    (x : ι → R) : A.smulVecHom R x = A *ᵥ x := by
  ext k
  simp [mulVec, dotProduct]

/-- The identity matrix induces the identity map. -/
@[simp]
theorem smulVecHom_one [DecidableEq ι] :
    (1 : Matrix ι ι R).smulVecHom M = ContinuousAddMonoidHom.id _ := by
  ext x i
  simp [Matrix.one_apply, ite_smul]

/-- The map induced by a product of matrices is the composite of the maps they induce. -/
theorem smulVecHom_mul [Fintype κ] (B : Matrix μ κ R) :
    (B * A).smulVecHom M = (B.smulVecHom M).comp (A.smulVecHom M) := by
  ext x m
  simp only [smulVecHom_apply, ContinuousAddMonoidHom.comp_toFun, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

noncomputable section Blocks

variable {𝕜 R m n l o : Type*} [Semiring 𝕜]
  [AddCommMonoid R] [Module 𝕜 R] [TopologicalSpace R]
variable (𝕜)

/-- Projection onto the upper-right block as a continuous linear map. -/
def toBlocks₁₂CLM :
    Matrix (m ⊕ n) (l ⊕ o) R →L[𝕜] Matrix m o R where
  toLinearMap :=
    { toFun := toBlocks₁₂
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  cont := continuous_matrix fun i j ↦ continuous_id.matrix_elem (Sum.inl i) (Sum.inr j)
/-- The block projection acts by taking the upper-right block. -/
@[simp] theorem toBlocks₁₂CLM_apply (A : Matrix (m ⊕ n) (l ⊕ o) R) :
    toBlocks₁₂CLM 𝕜 A = A.toBlocks₁₂ := by rfl

/-- Insertion into the upper-right block, with all other blocks zero, as a continuous linear map. -/
def fromBlocks₁₂CLM :
    Matrix m o R →L[𝕜] Matrix (m ⊕ n) (l ⊕ o) R where
  toLinearMap :=
    { toFun := fun X ↦ fromBlocks 0 X 0 0
      map_add' := fun X Y ↦ by simp only [fromBlocks_add, zero_add]
      map_smul' := fun c X ↦ by simp only [fromBlocks_smul, smul_zero, RingHom.id_apply] }
  cont := continuous_matrix fun i j ↦ by
    cases i <;> cases j
    · exact continuous_const
    · exact continuous_id.matrix_elem _ _
    · exact continuous_const
    · exact continuous_const
/-- The block insertion puts its argument in the upper-right block and zero elsewhere. -/
@[simp] theorem fromBlocks₁₂CLM_apply (A : Matrix m o R) :
    fromBlocks₁₂CLM 𝕜 (n := n) (l := l) A = fromBlocks 0 A 0 0 := by rfl

end Blocks

end Matrix
