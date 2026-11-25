/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Data.Matrix.Block
public import TauCeti.LinearAlgebra.Matrix.Module

/-!
# Continuous matrix actions and block maps over a topological module

A matrix `A : Matrix κ ι R` acts on vectors `x : ι → M` with entries in an additive monoid `M` on
which `R` acts additively by `k ↦ ∑ i, A k i • x i`. When `M` is a topological additive monoid on
which each scalar acts continuously, this is the continuous additive map
`Matrix.smulVecHom A M : (ι → M) →ₜ+ (κ → M)`. When `M` is an `R`-module it is functorial in the
matrix (`Matrix.smulVecHom_one`, `Matrix.smulVecHom_mul`). For `M = R` it is `Matrix.mulVec`
(`Matrix.smulVecHom_self_apply`); over a topological commutative semiring, bundling linearity as
well gives `Matrix.mulVecCLM : (ι → R) →L[R] (κ → R)`, which varies continuously with the matrix
entries over any normed field (`Matrix.continuous_mulVecCLM`, `Matrix.continuousOn_mulVecCLM`).

The motivating case for `Matrix.smulVecHom` is `R = ℤ` and `M = AddCircle p`, where an integer
matrix induces a map of tori `(ι → AddCircle p) → (κ → AddCircle p)`.

The upper-right block projection and the matching insertion are continuous linear maps over
any semiring and topological module, with arbitrary row and column index types. Their application
lemmas are `Matrix.toBlocks₁₂CLM_apply` and `Matrix.fromBlocks₁₂CLM_apply`.

## Main definitions

* `Matrix.smulVecHom`: the continuous additive action of a matrix on vectors in an additive monoid
  with a distributive scalar action.
* `Matrix.mulVecCLM`: `Matrix.mulVec` as a continuous linear map `(ι → R) →L[R] (κ → R)`, with
  continuity in families over a normed field (`Matrix.continuous_mulVecCLM`,
  `Matrix.continuousOn_mulVecCLM`).
* `TauCeti.dotProductCLM`: the covector `v ↦ c ⬝ᵥ v` as a continuous linear functional on `ι → R`.
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
  simp only [smulVecHom_apply, ContinuousAddMonoidHom.comp_toFun, Matrix.sum_mul_apply_smul]

end Module

/-- The map induced by a difference of matrices is the difference of the maps they induce. -/
theorem smulVecHom_sub_apply [Ring R] (A B : Matrix κ ι R) (M : Type*) [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] (x : ι → M) :
    (A - B).smulVecHom M x = A.smulVecHom M x - B.smulVecHom M x := by
  ext k
  simp [sub_smul, Finset.sum_sub_distrib]

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

section MulVecCLM

section TopologicalSemiring

variable [CommSemiring R] [TopologicalSpace R] [ContinuousAdd R] [ContinuousMul R]

/-- `Matrix.mulVec A` as a continuous `R`-linear map `(ι → R) →L[R] (κ → R)`. -/
def mulVecCLM (A : Matrix κ ι R) : (ι → R) →L[R] (κ → R) where
  toLinearMap := A.mulVecLin
  cont := continuous_const.matrix_mulVec continuous_id

/-- Applying `A.mulVecCLM` computes the matrix-vector product `A *ᵥ v`. -/
@[simp]
theorem mulVecCLM_apply (A : Matrix κ ι R) (v : ι → R) : A.mulVecCLM v = A *ᵥ v := (rfl)

/-- Coercing `A.mulVecCLM` to a linear map gives `A.mulVecLin`. -/
@[simp]
theorem toLinearMap_mulVecCLM (A : Matrix κ ι R) :
    (A.mulVecCLM : (ι → R) →ₗ[R] (κ → R)) = A.mulVecLin := (rfl)

/-- The zero matrix induces the zero continuous linear map. -/
@[simp]
theorem mulVecCLM_zero : (0 : Matrix κ ι R).mulVecCLM = 0 := by
  ext; simp

/-- Matrix addition corresponds to addition of continuous linear maps. -/
@[simp]
theorem mulVecCLM_add (A B : Matrix κ ι R) :
    (A + B).mulVecCLM = A.mulVecCLM + B.mulVecCLM := by
  ext; simp [add_mulVec]

/-- Scalar multiplication of a matrix scales the induced continuous linear map. -/
@[simp]
theorem mulVecCLM_smul (c : R) (A : Matrix κ ι R) :
    (c • A).mulVecCLM = c • A.mulVecCLM := by
  ext; simp [smul_mulVec]

/-- The identity matrix induces the identity continuous linear map. -/
@[simp]
theorem mulVecCLM_one [DecidableEq ι] :
    (1 : Matrix ι ι R).mulVecCLM = ContinuousLinearMap.id R (ι → R) := by
  ext; simp

/-- Matrix multiplication corresponds to composition of continuous linear maps. -/
@[simp]
theorem mulVecCLM_mul [Fintype κ] (A : Matrix μ κ R) (B : Matrix κ ι R) :
    (A * B).mulVecCLM = A.mulVecCLM.comp B.mulVecCLM := by
  ext; simp [mulVec_mulVec]

/-- Decomposition of `A.mulVecCLM` as a finite linear combination of rank-one coordinate maps. -/
theorem mulVecCLM_eq_sum [Fintype κ] [DecidableEq κ] (A : Matrix κ ι R) :
    A.mulVecCLM = ∑ i : κ, ∑ j : ι, A i j •
      (ContinuousLinearMap.single R (fun _ : κ ↦ R) i ∘L
        ContinuousLinearMap.proj (R := R) (φ := fun _ : ι ↦ R) j) := by
  ext v k
  simp [mulVec, dotProduct, Pi.single_apply]

end TopologicalSemiring

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜] [Finite κ]

/-- Over a normed field, `Matrix.mulVecCLM` depends continuously on the matrix. -/
@[fun_prop]
theorem continuous_mulVecCLM :
    Continuous (Matrix.mulVecCLM : Matrix κ ι 𝕜 → (ι → 𝕜) →L[𝕜] (κ → 𝕜)) := by
  classical
  cases nonempty_fintype κ
  have hEq : (Matrix.mulVecCLM : Matrix κ ι 𝕜 → (ι → 𝕜) →L[𝕜] (κ → 𝕜)) =
      fun A ↦ ∑ i : κ, ∑ j : ι, A i j •
        (ContinuousLinearMap.single 𝕜 (fun _ : κ ↦ 𝕜) i ∘L
          ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) j) :=
    funext mulVecCLM_eq_sum
  rw [hEq]
  fun_prop

/-- A matrix family whose entries are continuous on `s` induces a continuous-on-`s` family of
continuous linear maps via `Matrix.mulVecCLM`. -/
theorem continuousOn_mulVecCLM {X : Type*} [TopologicalSpace X] {s : Set X}
    {M : X → Matrix κ ι 𝕜} (hM : ∀ i j, ContinuousOn (fun x ↦ M x i j) s) :
    ContinuousOn (fun x ↦ (M x).mulVecCLM) s :=
  continuous_mulVecCLM.comp_continuousOn
    (continuousOn_pi.mpr fun i ↦ continuousOn_pi.mpr fun j ↦ hM i j)

end NormedField

end MulVecCLM

end Matrix

namespace TauCeti

section DotProductCLM

variable {ι R : Type*} [Fintype ι] [CommSemiring R] [TopologicalSpace R] [ContinuousAdd R]
  [ContinuousMul R]

/-- The covector `v ↦ c ⬝ᵥ v` on `ι → R` as a continuous `R`-linear map: Mathlib's
`dotProductBilin R R c` together with its continuity. -/
def dotProductCLM (c : ι → R) : (ι → R) →L[R] R where
  toLinearMap := dotProductBilin R R c
  cont := continuous_const.dotProduct continuous_id

/-- Applying `dotProductCLM c` computes the dot product with `c`. -/
@[simp]
theorem dotProductCLM_apply (c v : ι → R) : dotProductCLM c v = c ⬝ᵥ v :=
  dotProductBilin_apply_apply R R c v

/-- Coercing `dotProductCLM c` to a linear map gives `dotProductBilin R R c`. -/
@[simp]
theorem toLinearMap_dotProductCLM (c : ι → R) :
    (dotProductCLM c : (ι → R) →ₗ[R] R) = dotProductBilin R R c := (rfl)

end DotProductCLM

end TauCeti
