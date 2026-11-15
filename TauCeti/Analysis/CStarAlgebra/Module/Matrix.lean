/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair
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
* `CStarMatrix.algebraMap_le_iff_forall_sum_le`: quadratic-form criterion for scalar lower bounds
  `algebraMap ℝ (CStarMatrix n n A) r ≤ M`.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1 and 4.
-/

public section

open MulOpposite Matrix CStarModule
open scoped WithCStarModule

namespace CStarMatrix

section NonUnital

variable {l m n A : Type*} [Fintype n] [NonUnitalCStarAlgebra A]

/-- Left multiplication by a `CStarMatrix m n A` on column vectors in `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)`, bundled
complex-linearly in the matrix as a continuous complex-linear map. Unlike `CStarMatrix.toCLM`,
which acts by `Matrix.vecMul` on the left module `C⋆ᵐᵒᵈ(A, m → A)`, this acts by `Matrix.mulVec`
and commutes with the right `A`-action (`CStarMatrix.mulVecCLM_op_smul`). -/
noncomputable def mulVecCLM :
    CStarMatrix m n A →ₗ[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A) →L[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, m → A) where
  toFun M :=
    (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := m → A)).symm.toContinuousLinearMap.comp <|
      (ContinuousLinearMap.mk (Matrix.mulVecBilin ℂ ℂ (ofMatrix.symm M))
        (continuous_const.matrix_mulVec continuous_id)).comp
        (WithCStarModule.equivL ℂ (A := Aᵐᵒᵖ) (E := n → A)).toContinuousLinearMap
  map_add' M₁ M₂ :=
    ContinuousLinearMap.ext fun v ↦
      congrArg (WithCStarModule.equiv Aᵐᵒᵖ (m → A)).symm
        (Matrix.add_mulVec (ofMatrix.symm M₁) (ofMatrix.symm M₂) v)
  map_smul' c M :=
    ContinuousLinearMap.ext fun v ↦
      congrArg (WithCStarModule.equiv Aᵐᵒᵖ (m → A)).symm
        (Matrix.smul_mulVec c (ofMatrix.symm M) v)

theorem mulVecCLM_apply (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecCLM M v = (WithCStarModule.equiv Aᵐᵒᵖ (m → A)).symm (ofMatrix.symm M *ᵥ v) := (rfl)

@[simp] theorem mulVecCLM_apply_apply (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) (i : m) :
    mulVecCLM M v i = ∑ j, M i j * v j := (rfl)

/-- `mulVecCLM M` commutes with the right `A`-action on column vectors. -/
theorem mulVecCLM_op_smul (M : CStarMatrix m n A) (a : A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecCLM M (op a • v) = op a • mulVecCLM M v := by
  ext i; simp [MulOpposite.smul_eq_mul_unop, Finset.sum_mul, mul_assoc]

@[simp] theorem mulVecCLM_comp_mulVecCLM [Fintype m] (M : CStarMatrix l m A)
    (N : CStarMatrix m n A) : (mulVecCLM M).comp (mulVecCLM N) = mulVecCLM (M * N) :=
  ContinuousLinearMap.ext fun v ↦ congrArg (WithCStarModule.equiv Aᵐᵒᵖ (l → A)).symm
    (Matrix.mulVec_mulVec v (ofMatrix.symm M) (ofMatrix.symm N))

@[simp] theorem mulVecCLM_mulVecCLM [Fintype m] (M : CStarMatrix l m A) (N : CStarMatrix m n A)
    (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) : mulVecCLM M (mulVecCLM N v) = mulVecCLM (M * N) v :=
  congrFun (congrArg DFunLike.coe (mulVecCLM_comp_mulVecCLM M N)) v

theorem isIdempotentElem_mulVecCLM {p : CStarMatrix n n A} (hp : IsIdempotentElem p) :
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
  map_add' _ _ := by ext v i; simp [Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]
  map_smul' _ _ := by
    ext v i; simp [Matrix.mulVec, dotProduct, zsmul_eq_mul, mul_assoc, Finset.mul_sum]

@[simp] theorem coe_mulVecLinearMap [CStarAlgebra A] (M : CStarMatrix m n A) :
    ⇑(mulVecLinearMap M) = ⇑(mulVecCLM M) := (rfl)

theorem mulVecLinearMap_apply [Ring A] (M : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecLinearMap M v = (WithCStarModule.equiv Aᵐᵒᵖ (m → A)).symm (ofMatrix.symm M *ᵥ v) := (rfl)

@[simp] theorem mulVecLinearMap_apply_apply [Ring A] (M : CStarMatrix m n A)
    (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) (i : m) : mulVecLinearMap M v i = ∑ j, M i j * v j := (rfl)

@[simp] theorem mulVecLinearMap_comp_mulVecLinearMap [Fintype m] [Ring A] (M : CStarMatrix l m A)
    (N : CStarMatrix m n A) :
    (mulVecLinearMap M).comp (mulVecLinearMap N) = mulVecLinearMap (M * N) :=
  LinearMap.ext fun v ↦ congrArg (WithCStarModule.equiv Aᵐᵒᵖ (l → A)).symm
    (Matrix.mulVec_mulVec v (ofMatrix.symm M) (ofMatrix.symm N))

@[simp] theorem mulVecLinearMap_mulVecLinearMap [Fintype m] [Ring A] (M : CStarMatrix l m A)
    (N : CStarMatrix m n A) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, n → A)) :
    mulVecLinearMap M (mulVecLinearMap N v) = mulVecLinearMap (M * N) v :=
  LinearMap.congr_fun (mulVecLinearMap_comp_mulVecLinearMap M N) v

@[simp] theorem mulVecLinearMap_one [DecidableEq n] [Ring A] :
    mulVecLinearMap (1 : CStarMatrix n n A) = LinearMap.id :=
  LinearMap.ext fun v ↦ congrArg (WithCStarModule.equiv Aᵐᵒᵖ (n → A)).symm (Matrix.one_mulVec v)

@[simp] theorem mulVecCLM_one [DecidableEq n] [CStarAlgebra A] :
    mulVecCLM (1 : CStarMatrix n n A) = .id ℂ _ := by
  ext v
  rw [ContinuousLinearMap.id_apply, ← coe_mulVecLinearMap, mulVecLinearMap_one, LinearMap.id_apply]

theorem isIdempotentElem_mulVecLinearMap [Ring A] {p : CStarMatrix n n A}
    (hp : IsIdempotentElem p) : IsIdempotentElem (mulVecLinearMap p) := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, mulVecLinearMap_comp_mulVecLinearMap, hp.eq]

/-- Over a unital C⋆-algebra, a matrix `M : CStarMatrix n n A` satisfies
`algebraMap ℝ (CStarMatrix n n A) r ≤ M` if and only if every finite quadratic form
`∑ i, ∑ j, star (a i) * M i j * a j` dominates `r • ∑ i, star (a i) * a i`. -/
theorem algebraMap_le_iff_forall_sum_le [DecidableEq n] [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {r : ℝ} {M : CStarMatrix n n A} :
    algebraMap ℝ (CStarMatrix n n A) r ≤ M ↔
      ∀ a : n → A, r • ∑ i, star (a i) * a i ≤ ∑ i, ∑ j, star (a i) * M i j * a j := by
  rw [← sub_nonneg, Algebra.algebraMap_eq_smul_one, nonneg_iff_forall_sum_nonneg]
  refine forall_congr' fun a ↦ ?_
  have hone :
      ∑ i, ∑ j, star (a i) * (r • (1 : CStarMatrix n n A)) i j * a j =
        r • ∑ i, star (a i) * a i := by
    simp [one_apply, ite_mul, mul_ite, ← Finset.smul_sum]
  simp_rw [sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib, hone, sub_nonneg]

end Unital

end CStarMatrix
