/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair
public import TauCeti.Analysis.CStarAlgebra.Module.Gram
public import TauCeti.Analysis.CStarAlgebra.Module.Self

import Mathlib.Topology.Instances.Matrix

/-!
# Column-vector action of `CStarMatrix` on finite right Hilbert C⋆-modules

For a (possibly non-unital) normed complex algebra `A` (with `IsScalarTower ℂ A A` and
`SMulCommClass ℂ A A`), `CStarMatrix m n A` acts (when `n` is finite) on column vectors in
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)` by left matrix-vector multiplication `(M *ᵥ v) i = ∑ j, M i j * v j`. Unlike
Mathlib's `CStarMatrix.toCLM`, which acts on the left module `C⋆ᵐᵒᵈ(A, m → A)` by `Matrix.vecMul`
on the right, this column-vector action commutes with the right `A`-action
(`MulOpposite.op a • v`). When `A` is a (possibly non-unital) C⋆-algebra and both `m` and `n` are
finite, `mulVecCLM M` and `mulVecCLM M.conjTranspose` form a C⋆-module adjoint pair. Over a unital
ring `A` and for finite `n`, `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)` is a finite free right `A`-module and
`mulVecLinearMap M` represents a right `A`-linear operator.

## Main declarations

* `CStarMatrix.mulVecCLM`: for finite `n` over a (possibly non-unital) normed complex
  algebra `A`, left matrix-vector multiplication bundled complex-linearly in the matrix as
  `CStarMatrix m n A →ₗ[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A) →L[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A)`.
* `CStarMatrix.isAdjointPair_mulVecCLM_conjTranspose`,
  `CStarMatrix.isAdjointPair_mulVecCLM_star`:
  over a (possibly non-unital) C⋆-algebra `A` for finite `m` and `n` (resp. finite `n`),
  `mulVecCLM M` and `mulVecCLM M.conjTranspose` form a C⋆-module adjoint pair.
* `CStarMatrix.mulVecLinearMap`: over a unital ring `A` and finite `n`, left matrix-vector
  multiplication bundled additively in the matrix as
  `CStarMatrix m n A →ₗ[ℤ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A) →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A)`.
* `CStarMatrix.gram_mulVecCLM_single_one`: over a unital C⋆-algebra `A` and for finite `m`
  and `n`, the Gram matrix of the columns `j ↦ mulVecCLM M (e j)` of `M` is `M.conjTranspose * M`.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1 and 4.
-/

public section

open MulOpposite Matrix CStarModule
open scoped WithCStarModule

namespace CStarMatrix

section NonUnital

section Normed

variable {l m n A : Type*} [Fintype n] [NonUnitalNormedRing A] [NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

/-- Left multiplication by a `CStarMatrix m n A` on column vectors in `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)`, bundled
complex-linearly in the matrix as a continuous complex-linear map. Unlike `CStarMatrix.toCLM`,
which acts by `Matrix.vecMul` on the left module `C⋆ᵐᵒᵈ(A, m → A)`, this acts by `Matrix.mulVec`
and commutes with the right `A`-action (`CStarMatrix.mulVecCLM_op_smul`). -/
noncomputable def mulVecCLM :
    CStarMatrix m n A →ₗ[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A) →L[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A) where
  toFun M :=
    { toLinearMap :=
        ((WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := m → A)).symm :
            (m → A) →ₗ[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A)) ∘ₗ
          Matrix.mulVecBilin ℂ ℂ (ofMatrix.symm M) ∘ₗ
          ((WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := n → A)) :
            C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A) →ₗ[ℂ] (n → A))
      cont :=
        (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := m → A)).symm.continuous.comp <|
          (continuous_const.matrix_mulVec continuous_id).comp
            (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := n → A)).continuous }
  map_add' M N := ContinuousLinearMap.ext fun _ ↦ (congrArg
    (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := m → A)).symm <| by
      rw [ofMatrix_symm_add, map_add, LinearMap.add_comp, LinearMap.add_apply]).trans
    (map_add _ _ _)
  map_smul' c M := ContinuousLinearMap.ext fun _ ↦ (congrArg
    (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := m → A)).symm <| by
      rw [ofMatrix_symm_smul, map_smul, LinearMap.smul_comp, LinearMap.smul_apply]).trans
    (map_smul _ _ _)

theorem mulVecCLM_apply (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecCLM M v = (WithCStarModule.equiv Aᵐᵒᵖ (m → A)).symm
      (ofMatrix.symm M *ᵥ WithCStarModule.equiv Aᵐᵒᵖ (n → A) v) := by
  simp [mulVecCLM]

@[simp] theorem mulVecCLM_apply_apply (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A))
    (i : m) : mulVecCLM M v i = ∑ j, M i j * v j := by
  simp [mulVecCLM_apply, Matrix.mulVec, dotProduct]

/-- `mulVecCLM M` commutes with the right `A`-action on column vectors. -/
theorem mulVecCLM_op_smul (M : CStarMatrix m n A) (a : A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecCLM M (op a • v) = op a • mulVecCLM M v := by
  let : DistribSMul Aᵐᵒᵖ A :=
    { smul_zero := fun _ ↦ zero_mul _, smul_add := fun _ _ _ ↦ add_mul _ _ _ }
  rw [mulVecCLM_apply, mulVecCLM_apply, WithCStarModule.equiv_smul, Matrix.mulVec_smul,
    WithCStarModule.equiv_symm_smul]

@[simp] theorem mulVecCLM_comp_mulVecCLM [Fintype m] (M : CStarMatrix l m A)
    (N : CStarMatrix m n A) : (mulVecCLM M).comp (mulVecCLM N) = mulVecCLM (M * N) := by
  ext1 v
  simp only [ContinuousLinearMap.comp_apply, mulVecCLM_apply, Equiv.apply_symm_apply,
    Matrix.mulVec_mulVec, ofMatrix_symm_mul]

@[simp] theorem mulVecCLM_mulVecCLM [Fintype m] (M : CStarMatrix l m A)
    (N : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecCLM M (mulVecCLM N v) = mulVecCLM (M * N) v :=
  congrFun (congrArg DFunLike.coe (mulVecCLM_comp_mulVecCLM M N)) v

theorem _root_.IsIdempotentElem.mulVecCLM {p : CStarMatrix n n A}
    (hp : IsIdempotentElem p) : IsIdempotentElem (mulVecCLM p) := by
  rw [IsIdempotentElem, ContinuousLinearMap.mul_def, mulVecCLM_comp_mulVecCLM, hp.eq]

end Normed

section CStar

variable {m n A : Type*} [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Column-vector multiplication by `M` and by `M.conjTranspose` form a module adjoint pair on the
standard right Hilbert `A`-modules (for finite `m` and `n`). -/
theorem isAdjointPair_mulVecCLM_conjTranspose [Fintype m] (M : CStarMatrix m n A) :
    LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A))).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A))).flip
      (mulVecCLM M) (mulVecCLM M.conjTranspose) := by
  rw [isAdjointPair_inner_iff]; intro v w; apply unop_injective
  simp only [WithCStarModule.pi_inner, Finset.unop_sum, unop_inner_mulOpposite,
    mulVecCLM_apply_apply, star_sum, star_mul, Finset.sum_mul, conjTranspose_apply]
  rw [Finset.sum_comm]; simp_rw [Finset.mul_sum, mul_assoc]

/-- Column-vector multiplication by a square matrix `M` and by `star M` form a module adjoint pair
on `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)`. -/
theorem isAdjointPair_mulVecCLM_star (M : CStarMatrix n n A) : LinearMap.IsAdjointPair
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A))).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A))).flip (mulVecCLM M) (mulVecCLM (star M)) :=
  isAdjointPair_mulVecCLM_conjTranspose M

end CStar

end NonUnital

section Unital

variable {l m n A : Type*} [Fintype n]

/-- Left multiplication by a `CStarMatrix m n A` on `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)`, bundled additively in the
matrix as a right `A`-linear (`Aᵐᵒᵖ`-linear) map. -/
def mulVecLinearMap [Ring A] :
    CStarMatrix m n A →ₗ[ℤ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A) →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A) where
  toFun M :=
    (WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ (m → A)).symm.toLinearMap ∘ₗ
      Matrix.mulVecBilin ℤ Aᵐᵒᵖ (ofMatrix.symm M) ∘ₗ
      (WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ (n → A)).toLinearMap
  map_add' M N := by
    ext1 v; simp [ofMatrix_symm_add]
  map_smul' c M := by
    ext1 v
    simp only [RingHom.id_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
      ofMatrix_symm_smul, map_zsmul]

@[simp] theorem mulVecLinearMap_one [DecidableEq n] [Ring A] :
    mulVecLinearMap (1 : CStarMatrix n n A) = LinearMap.id := by
  ext1 v; simp [mulVecLinearMap, ofMatrix_symm_one]

@[simp] theorem mulVecCLM_one [DecidableEq n] [NormedRing A] [NormedSpace ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] :
    mulVecCLM (1 : CStarMatrix n n A) = .id ℂ _ := by
  ext1 v; simp [mulVecCLM_apply, ofMatrix_symm_one]

theorem mulVecLinearMap_apply [Ring A] (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecLinearMap M v = (WithCStarModule.equiv Aᵐᵒᵖ (m → A)).symm
      (ofMatrix.symm M *ᵥ WithCStarModule.equiv Aᵐᵒᵖ (n → A) v) := by
  simp [mulVecLinearMap]

@[simp] theorem mulVecLinearMap_apply_apply [Ring A] (M : CStarMatrix m n A)
    (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) (i : m) : mulVecLinearMap M v i = ∑ j, M i j * v j := by
  simp [mulVecLinearMap_apply, Matrix.mulVec, dotProduct]

@[simp] theorem coe_mulVecLinearMap [NormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A]
    [SMulCommClass ℂ A A] (M : CStarMatrix m n A) : ⇑(mulVecLinearMap M) = ⇑(mulVecCLM M) :=
  funext fun v ↦ (mulVecLinearMap_apply M v).trans (mulVecCLM_apply M v).symm

@[simp] theorem mulVecLinearMap_comp_mulVecLinearMap [Fintype m] [Ring A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (mulVecLinearMap M).comp (mulVecLinearMap N) = mulVecLinearMap (M * N) := by
  ext1 v
  simp only [LinearMap.comp_apply, mulVecLinearMap_apply, Equiv.apply_symm_apply,
    Matrix.mulVec_mulVec, ofMatrix_symm_mul]

@[simp] theorem mulVecLinearMap_mulVecLinearMap [Fintype m] [Ring A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecLinearMap M (mulVecLinearMap N v) = mulVecLinearMap (M * N) v :=
  LinearMap.congr_fun (mulVecLinearMap_comp_mulVecLinearMap M N) v

theorem _root_.IsIdempotentElem.mulVecLinearMap [Ring A] {p : CStarMatrix n n A}
    (hp : IsIdempotentElem p) : IsIdempotentElem (mulVecLinearMap p) := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, mulVecLinearMap_comp_mulVecLinearMap, hp.eq]

/-- Over a unital C⋆-algebra, the Gram matrix of the columns `j ↦ mulVecCLM M (e j)` of a matrix
`M : CStarMatrix m n A` is `M.conjTranspose * M`. -/
theorem gram_mulVecCLM_single_one [Fintype m] [DecidableEq n] [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (M : CStarMatrix m n A) :
    gram A (fun j ↦ mulVecCLM M ((WithCStarModule.equiv Aᵐᵒᵖ (n → A)).symm (Pi.single j (1 : A)))) =
      M.conjTranspose * M := by
  ext i j
  simp [gram_apply, WithCStarModule.pi_inner, Finset.unop_sum, mulVecCLM_apply_apply, mul_apply,
    conjTranspose_apply, Pi.single_apply]

end Unital

end CStarMatrix
