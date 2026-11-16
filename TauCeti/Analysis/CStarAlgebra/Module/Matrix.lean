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

For a C⋆-algebra `A` (possibly non-unital) and finite index types, `CStarMatrix m n A` acts on
column vectors in the finite right Hilbert `A`-module `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)` by left matrix-vector
multiplication `(M *ᵥ v) i = ∑ j, M i j * v j`. Unlike Mathlib's `CStarMatrix.toCLM`, which acts on
the left module `C⋆ᵐᵒᵈ(A, m → A)` by `Matrix.vecMul` on the right, this column-vector action
commutes with the right `A`-action (`MulOpposite.op a • v`) and represents module operators between
finite free right Hilbert `A`-modules.

## Main declarations

* `CStarMatrix.mulVecCLM`: left matrix-vector multiplication bundled complex-linearly in the matrix
  as `CStarMatrix m n A →ₗ[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A) →L[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A)`.
* `CStarMatrix.isAdjointPair_mulVecCLM_conjTranspose`, `CStarMatrix.isAdjointPair_mulVecCLM_star`:
  `mulVecCLM M` and `mulVecCLM M.conjTranspose` form a C⋆-module adjoint pair.
* `CStarMatrix.mulVecLinearMap`: over a unital ring `A`, left matrix-vector multiplication bundled
  additively in the matrix as
  `CStarMatrix m n A →ₗ[ℤ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A) →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A)`.
* `CStarMatrix.gram_mulVecCLM_single_one`: the Gram matrix of the columns `j ↦ mulVecCLM M (e j)`
  of `M` is `M.conjTranspose * M`.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1 and 4.
-/

public section

open MulOpposite Matrix CStarModule
open scoped WithCStarModule

namespace CStarMatrix

section NonUnital

variable {l m n A : Type*} [Fintype n] [NonUnitalCStarAlgebra A]

private noncomputable def mulVecCLMAux (M : CStarMatrix m n A) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A) →L[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A) where
  toLinearMap :=
    (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ (m → A)).symm.toLinearMap ∘ₗ
      Matrix.mulVecBilin ℂ ℂ (ofMatrix.symm M) ∘ₗ
      (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ (n → A)).toLinearMap
  cont :=
    (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := m → A)).symm.continuous.comp <|
      (continuous_const.matrix_mulVec continuous_id).comp
        (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := n → A)).continuous

private theorem mulVecCLMAux_apply (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecCLMAux M v =
      (WithCStarModule.equiv Aᵐᵒᵖ (m → A)).symm
        (ofMatrix.symm M *ᵥ WithCStarModule.equiv Aᵐᵒᵖ (n → A) v) := rfl

/-- Left multiplication by a `CStarMatrix m n A` on column vectors in `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)`, bundled
complex-linearly in the matrix as a continuous complex-linear map. Unlike `CStarMatrix.toCLM`,
which acts by `Matrix.vecMul` on the left module `C⋆ᵐᵒᵈ(A, m → A)`, this acts by `Matrix.mulVec`
and commutes with the right `A`-action (`CStarMatrix.mulVecCLM_op_smul`). -/
noncomputable def mulVecCLM :
    CStarMatrix m n A →ₗ[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A) →L[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A) where
  toFun := mulVecCLMAux
  map_add' M N := by
    ext1 v
    have hadd : ofMatrix.symm (M + N) = ofMatrix.symm M + ofMatrix.symm N := rfl
    simp only [_root_.add_apply, mulVecCLMAux_apply, hadd, Matrix.add_mulVec,
      WithCStarModule.equiv_symm_add]
  map_smul' c M := by
    ext1 v
    have hsmul : ofMatrix.symm (c • M) = c • ofMatrix.symm M := rfl
    simp only [RingHom.id_apply, _root_.smul_apply, mulVecCLMAux_apply, hsmul,
      Matrix.smul_mulVec, WithCStarModule.equiv_symm_smul]

theorem mulVecCLM_apply (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecCLM M v =
      (WithCStarModule.equiv Aᵐᵒᵖ (m → A)).symm
        (ofMatrix.symm M *ᵥ WithCStarModule.equiv Aᵐᵒᵖ (n → A) v) := by
  simp [mulVecCLM, mulVecCLMAux_apply]

@[simp] theorem mulVecCLM_apply_apply (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) (i : m) :
    mulVecCLM M v i = ∑ j, M i j * v j := by
  simp [mulVecCLM_apply, Matrix.mulVec, dotProduct]

/-- `mulVecCLM M` commutes with the right `A`-action on column vectors. -/
theorem mulVecCLM_op_smul (M : CStarMatrix m n A) (a : A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecCLM M (op a • v) = op a • mulVecCLM M v := by
  let : DistribSMul Aᵐᵒᵖ A :=
    { smul_zero := fun _ ↦ zero_mul _
      smul_add := fun _ _ _ ↦ add_mul _ _ _ }
  rw [mulVecCLM_apply, mulVecCLM_apply, WithCStarModule.equiv_smul, Matrix.mulVec_smul,
    WithCStarModule.equiv_symm_smul]

@[simp] theorem mulVecCLM_comp_mulVecCLM [Fintype m] (M : CStarMatrix l m A)
    (N : CStarMatrix m n A) : (mulVecCLM M).comp (mulVecCLM N) = mulVecCLM (M * N) := by
  ext1 v
  have hmul : ofMatrix.symm (M * N) = ofMatrix.symm M * ofMatrix.symm N :=
    ofMatrix.symm_apply_apply _
  simp only [ContinuousLinearMap.comp_apply, mulVecCLM_apply, Equiv.apply_symm_apply,
    Matrix.mulVec_mulVec, hmul]

@[simp] theorem mulVecCLM_mulVecCLM [Fintype m] (M : CStarMatrix l m A) (N : CStarMatrix m n A)
    (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) : mulVecCLM M (mulVecCLM N v) = mulVecCLM (M * N) v :=
  congrFun (congrArg DFunLike.coe (mulVecCLM_comp_mulVecCLM M N)) v

theorem _root_.IsIdempotentElem.mulVecCLM {p : CStarMatrix n n A} (hp : IsIdempotentElem p) :
    IsIdempotentElem (mulVecCLM p) := by
  rw [IsIdempotentElem, ContinuousLinearMap.mul_def, mulVecCLM_comp_mulVecCLM, hp.eq]

/-- Column-vector multiplication by `M` and by `M.conjTranspose` form a module adjoint pair on the
finite free right Hilbert `A`-modules. -/
theorem isAdjointPair_mulVecCLM_conjTranspose [Fintype m] [PartialOrder A] [StarOrderedRing A]
    (M : CStarMatrix m n A) :
    LinearMap.IsAdjointPair
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A))).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A))).flip
      (mulVecCLM M) (mulVecCLM M.conjTranspose) := by
  rw [isAdjointPair_inner_iff]; intro v w; apply unop_injective
  simp only [WithCStarModule.pi_inner, Finset.unop_sum, unop_inner_mulOpposite,
    mulVecCLM_apply_apply, star_sum, star_mul, Finset.sum_mul, conjTranspose_apply]
  rw [Finset.sum_comm]; simp_rw [Finset.mul_sum, mul_assoc]

/-- Column-vector multiplication by a square matrix `M` and by `star M` form a module adjoint pair
on `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)`. -/
theorem isAdjointPair_mulVecCLM_star [PartialOrder A] [StarOrderedRing A] (M : CStarMatrix n n A) :
    LinearMap.IsAdjointPair
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A))).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A))).flip (mulVecCLM M) (mulVecCLM (star M)) :=
  isAdjointPair_mulVecCLM_conjTranspose M

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
    ext1 v
    have hadd : ofMatrix.symm (M + N) = ofMatrix.symm M + ofMatrix.symm N := rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply, hadd, map_add]
  map_smul' c M := by
    ext1 v
    have hsmul : ofMatrix.symm (c • M) = c • ofMatrix.symm M := rfl
    simp only [RingHom.id_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
      hsmul, map_zsmul]

theorem mulVecLinearMap_apply [Ring A] (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecLinearMap M v =
      (WithCStarModule.equiv Aᵐᵒᵖ (m → A)).symm
        (ofMatrix.symm M *ᵥ WithCStarModule.equiv Aᵐᵒᵖ (n → A) v) := by
  simp [mulVecLinearMap]

@[simp] theorem mulVecLinearMap_apply_apply [Ring A] (M : CStarMatrix m n A)
    (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) (i : m) : mulVecLinearMap M v i = ∑ j, M i j * v j := by
  simp [mulVecLinearMap_apply, Matrix.mulVec, dotProduct]

@[simp] theorem coe_mulVecLinearMap [CStarAlgebra A] (M : CStarMatrix m n A) :
    ⇑(mulVecLinearMap M) = ⇑(mulVecCLM M) := by
  funext v; rw [mulVecLinearMap_apply, mulVecCLM_apply]

@[simp] theorem mulVecLinearMap_comp_mulVecLinearMap [Fintype m] [Ring A] (M : CStarMatrix l m A)
    (N : CStarMatrix m n A) :
    (mulVecLinearMap M).comp (mulVecLinearMap N) = mulVecLinearMap (M * N) := by
  ext1 v
  have hmul : ofMatrix.symm (M * N) = ofMatrix.symm M * ofMatrix.symm N :=
    ofMatrix.symm_apply_apply _
  simp only [LinearMap.comp_apply, mulVecLinearMap_apply, Equiv.apply_symm_apply,
    Matrix.mulVec_mulVec, hmul]

@[simp] theorem mulVecLinearMap_mulVecLinearMap [Fintype m] [Ring A] (M : CStarMatrix l m A)
    (N : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecLinearMap M (mulVecLinearMap N v) = mulVecLinearMap (M * N) v :=
  LinearMap.congr_fun (mulVecLinearMap_comp_mulVecLinearMap M N) v

@[simp] theorem mulVecLinearMap_one [DecidableEq n] [Ring A] :
    mulVecLinearMap (1 : CStarMatrix n n A) = LinearMap.id := by
  ext1 v
  have hone : ofMatrix.symm (1 : CStarMatrix n n A) = 1 := rfl
  simp only [mulVecLinearMap_apply, LinearMap.id_apply, hone, Matrix.one_mulVec,
    Equiv.symm_apply_apply]

@[simp] theorem mulVecCLM_one [DecidableEq n] [CStarAlgebra A] :
    mulVecCLM (1 : CStarMatrix n n A) = .id ℂ _ := by
  ext v
  rw [ContinuousLinearMap.id_apply, ← coe_mulVecLinearMap, mulVecLinearMap_one, LinearMap.id_apply]

theorem _root_.IsIdempotentElem.mulVecLinearMap [Ring A] {p : CStarMatrix n n A}
    (hp : IsIdempotentElem p) : IsIdempotentElem (mulVecLinearMap p) := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, mulVecLinearMap_comp_mulVecLinearMap, hp.eq]

/-- Over a unital C⋆-algebra, the Gram matrix of the columns `j ↦ mulVecCLM M (e j)` of a matrix
`M : CStarMatrix m n A` is `M.conjTranspose * M`. -/
theorem gram_mulVecCLM_single_one [Fintype m] [DecidableEq n] [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (M : CStarMatrix m n A) :
    gram A (fun j ↦ mulVecCLM M
      ((WithCStarModule.equiv Aᵐᵒᵖ (n → A)).symm (Pi.single j (1 : A)))) =
      M.conjTranspose * M := by
  ext i j
  simp [gram_apply, WithCStarModule.pi_inner, Finset.unop_sum, mulVecCLM_apply_apply,
    mul_apply, conjTranspose_apply, Pi.single_apply]

end Unital

end CStarMatrix
