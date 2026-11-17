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
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Continuous matrix actions, trace, and block maps over a topological module

A matrix `A : Matrix κ ι R` acts on vectors `x : ι → M` with entries in an additive monoid `M` on
which `R` acts additively by `k ↦ ∑ i, A k i • x i`. When `M` is a topological additive monoid on
which each scalar acts continuously, this is the continuous additive map
`Matrix.smulVecHom A M : (ι → M) →ₜ+ (κ → M)`. When `M` is an `R`-module it is functorial in the
matrix (`Matrix.smulVecHom_one`, `Matrix.smulVecHom_mul`). For `M = R` it is `Matrix.mulVec`
(`Matrix.smulVecHom_self_apply`).

The motivating case is `R = ℤ` and `M = AddCircle p`, where an integer matrix induces a map of
tori `(ι → AddCircle p) → (κ → AddCircle p)`.

Over a nontrivially normed field `𝕜`, matrix-vector multiplication `(M, v) ↦ M *ᵥ v` is bundled as
the continuous bilinear map `Matrix.mulVecCLM m n 𝕜 R : Matrix m n R →L[𝕜] (n → R) →L[𝕜] (m → R)`,
requiring only a topological ring `R` with continuous multiplication and continuous scalar action by
`𝕜` (no finiteness on `m`, completeness, or choice of matrix norm). Its application lemma is
`Matrix.mulVecCLM_apply`.

The matrix trace (`Matrix.traceCLM`), the upper-right block projection, and the matching insertion
are continuous linear maps over any semiring and topological module. Their application lemmas are
`Matrix.traceCLM_apply`, `Matrix.toBlocks₁₂CLM_apply`, and `Matrix.fromBlocks₁₂CLM_apply`.

## Main definitions

* `Matrix.smulVecHom`: the continuous additive action of a matrix on vectors in an additive monoid
  with a distributive scalar action.
* `Matrix.mulVecCLM`: matrix-vector multiplication as a continuous bilinear map.
* `Matrix.traceCLM`: matrix trace as a continuous linear map.
* `Matrix.toBlocks₁₂CLM`: projection onto the upper-right block as a continuous linear map.
* `Matrix.fromBlocks₁₂CLM`: insertion into the upper-right block as a continuous linear map.
-/

public section

namespace Matrix

variable {ι κ μ R : Type*} [Fintype ι]

section DistribSMul

variable (A : Matrix κ ι R) (M : Type*) [AddCommMonoid M] [DistribSMul R M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul R M]

/-- The continuous additive map `(ι → M) →ₜ+ (κ → M)` induced by a matrix `A` with entries in `R`,
sending `x` to `k ↦ ∑ i, A k i • x i`. -/
def smulVecHom : (ι → M) →ₜ+ (κ → M) where
  toFun x k := ∑ i, A k i • x i
  map_zero' := by ext k; simp
  map_add' x y := by ext k; simp [Finset.sum_add_distrib]
  continuous_toFun := by fun_prop

@[simp]
theorem smulVecHom_apply (x : ι → M) (k : κ) : A.smulVecHom M x k = ∑ i, A k i • x i :=
  (rfl)

end DistribSMul

/-- For `M = R`, the induced map is `Matrix.mulVec`. -/
@[simp]
theorem smulVecHom_self_apply [NonUnitalNonAssocSemiring R] [TopologicalSpace R] [ContinuousAdd R]
    [ContinuousConstSMul R R] (A : Matrix κ ι R) (x : ι → R) : A.smulVecHom R x = A *ᵥ x := by
  ext k
  simp [mulVec, dotProduct]

section Module

variable [Semiring R] (A : Matrix κ ι R) (M : Type*) [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]

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

end Module

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

section Trace

/-- `Matrix.trace` as a continuous linear map. -/
def traceCLM (n α R : Type*) [Fintype n] [AddCommMonoid R] [TopologicalSpace R] [ContinuousAdd R]
    [Semiring α] [Module α R] : Matrix n n R →L[α] R where
  toLinearMap := Matrix.traceLinearMap n α R
  cont := continuous_id.matrix_trace

/-- Applying `Matrix.traceCLM` evaluates `Matrix.trace`. -/
@[simp]
theorem traceCLM_apply {n α R : Type*} [Fintype n] [AddCommMonoid R] [TopologicalSpace R]
    [ContinuousAdd R] [Semiring α] [Module α R] (M : Matrix n n R) :
    traceCLM n α R M = M.trace :=
  (rfl)

/-- Coercing `Matrix.traceCLM` to a function yields `Matrix.trace`. -/
@[simp]
theorem coe_traceCLM (n α R : Type*) [Fintype n] [AddCommMonoid R] [TopologicalSpace R]
    [ContinuousAdd R] [Semiring α] [Module α R] :
    ⇑(traceCLM n α R) = (Matrix.trace : Matrix n n R → R) :=
  (rfl)

/-- Forgetting continuity of `Matrix.traceCLM` recovers `Matrix.traceLinearMap`. -/
@[simp]
theorem toLinearMap_traceCLM (n α R : Type*) [Fintype n] [AddCommMonoid R] [TopologicalSpace R]
    [ContinuousAdd R] [Semiring α] [Module α R] :
    (traceCLM n α R).toLinearMap = Matrix.traceLinearMap n α R :=
  (rfl)

end Trace

section MulVec

/-- `Matrix.mulVec` as a continuous bilinear map `Matrix m n R →L[𝕜] (n → R) →L[𝕜] (m → R)`. -/
def mulVecCLM (m n 𝕜 R : Type*) [Fintype n] [NontriviallyNormedField 𝕜]
    [NonUnitalNonAssocRing R] [Module 𝕜 R] [SMulCommClass 𝕜 R R] [IsScalarTower 𝕜 R R]
    [TopologicalSpace R] [IsTopologicalAddGroup R] [ContinuousMul R] [ContinuousConstSMul 𝕜 R] :
    Matrix m n R →L[𝕜] (n → R) →L[𝕜] (m → R) :=
  let L : Matrix m n R →ₗ[𝕜] (n → R) →L[𝕜] (m → R) :=
    { toFun M :=
        { toLinearMap :=
            { toFun v := M *ᵥ v
              map_add' := mulVec_add M
              map_smul' c v := mulVec_smul M c v }
          cont := continuous_const.matrix_mulVec continuous_id }
      map_add' M N := ContinuousLinearMap.ext fun v ↦ add_mulVec M N v
      map_smul' c M := ContinuousLinearMap.ext fun v ↦ smul_mulVec c M v }
  ⟨L, ContinuousLinearMap.continuous_of_continuous_uncurry L
    (continuous_fst.matrix_mulVec continuous_snd)⟩

/-- Applying `Matrix.mulVecCLM` evaluates `Matrix.mulVec`. -/
@[simp]
theorem mulVecCLM_apply {m n 𝕜 R : Type*} [Fintype n] [NontriviallyNormedField 𝕜]
    [NonUnitalNonAssocRing R] [Module 𝕜 R] [SMulCommClass 𝕜 R R] [IsScalarTower 𝕜 R R]
    [TopologicalSpace R] [IsTopologicalAddGroup R] [ContinuousMul R] [ContinuousConstSMul 𝕜 R]
    (M : Matrix m n R) (v : n → R) :
    mulVecCLM m n 𝕜 R M v = M *ᵥ v :=
  (rfl)

end MulVec

end Matrix
