/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.MinTensorNorm

/-!
# The minimal and maximal norms on `M_n ⊙ A`

For every, possibly non-unital, C*-algebra `A`, the map `M_n(ℂ) ⊗[ℂ] A → M_n(A)`,
`m ⊗ a ↦ [mᵢⱼ a]`, is a star algebra isomorphism (`TauCeti.cstarMatrixTensorEquiv`), with inverse
`x ↦ Σᵢⱼ Eᵢⱼ ⊗ xᵢⱼ`. Since `M_n(A)` is a C*-algebra, every injective star homomorphism from
`M_n(ℂ) ⊗[ℂ] A` into a C*-algebra induces the `CStarMatrix` norm
(`NonUnitalStarAlgHom.norm_apply_eq_of_bijective`). In particular the minimal and the maximal norm
on `M_n ⊙ A` coincide with the `CStarMatrix` norm
(`TauCeti.minTensorNorm_eq_norm_cstarMatrixTensorEquiv`,
`TauCeti.maxTensorNorm_eq_norm_cstarMatrixTensorEquiv`), and both norms of `Σ Eᵢⱼ ⊗ aᵢⱼ` are
`‖[aᵢⱼ]‖` (`TauCeti.minTensorNorm_cstarMatrixTensorEquiv_symm`,
`TauCeti.maxTensorNorm_cstarMatrixTensorEquiv_symm`).

That `M_n ⊙ A` carries exactly one C*-norm also needs that the completion of an arbitrary C*-norm
gives an injective star homomorphism into a C*-algebra; that step is not in this file.

## Main declarations

* `TauCeti.cstarMatrixTensorEquiv`: `M_n(ℂ) ⊗[ℂ] A ≃⋆ₐ[ℂ] M_n(A)`.
* `TauCeti.minTensorNorm_eq_norm_cstarMatrixTensorEquiv`,
  `TauCeti.maxTensorNorm_eq_norm_cstarMatrixTensorEquiv`: both norms on `M_n(ℂ) ⊗[ℂ] A` are the
  `CStarMatrix` norm, and `TauCeti.minTensorNorm_cstarMatrixTensorEquiv_symm`,
  `TauCeti.maxTensorNorm_cstarMatrixTensorEquiv_symm`: both norms of `Σ Eᵢⱼ ⊗ aᵢⱼ` are `‖[aᵢⱼ]‖`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, II.9.4.2.
-/

public section

noncomputable section

open TensorProduct
open scoped ComplexOrder

universe u

namespace TauCeti

variable (n : Type*) [Fintype n] [DecidableEq n] (A : Type u) [NonUnitalCStarAlgebra A]

/-- The bilinear map `(m, a) ↦ [mᵢⱼ a]` from `M_n(ℂ) × A` to `M_n(A)`. -/
private def cstarMatrixTensorBilin : CStarMatrix n n ℂ →ₗ[ℂ] A →ₗ[ℂ] CStarMatrix n n A :=
  LinearMap.mk₂ ℂ (fun m a ↦ CStarMatrix.ofMatrix fun i j ↦ m i j • a)
    (fun _ _ _ ↦ CStarMatrix.ext fun _ _ ↦ add_smul _ _ _)
    (fun _ _ _ ↦ CStarMatrix.ext fun _ _ ↦ mul_smul _ _ _)
    (fun _ _ _ ↦ CStarMatrix.ext fun _ _ ↦ smul_add _ _ _)
    (fun _ _ _ ↦ CStarMatrix.ext fun _ _ ↦ smul_comm _ _ _)

omit [Fintype n] [DecidableEq n] in
variable {n A} in
@[simp]
private theorem cstarMatrixTensorBilin_apply (m : CStarMatrix n n ℂ) (a : A) (i j : n) :
    cstarMatrixTensorBilin n A m a i j = m i j • a :=
  (rfl)

/-- The star algebra isomorphism `M_n(ℂ) ⊗[ℂ] A ≃ M_n(A)`, `m ⊗ a ↦ [mᵢⱼ a]`, with inverse
`x ↦ Σᵢⱼ Eᵢⱼ ⊗ xᵢⱼ` (Blackadar II.9.4.2). -/
def cstarMatrixTensorEquiv : CStarMatrix n n ℂ ⊗[ℂ] A ≃⋆ₐ[ℂ] CStarMatrix n n A where
  toFun := TensorProduct.lift (cstarMatrixTensorBilin n A)
  invFun x := ∑ i, ∑ j, CStarMatrix.matrixUnit i j ⊗ₜ x i j
  left_inv x := by
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ =>
      simp only [map_add, CStarMatrix.add_apply, TensorProduct.tmul_add, Finset.sum_add_distrib]
        at h₁ h₂ ⊢
      rw [h₁, h₂]
    | tmul m a =>
      conv_rhs => rw [CStarMatrix.eq_sum_smul_ofMatrix_single_one m]
      simp only [TensorProduct.lift.tmul, cstarMatrixTensorBilin_apply, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', TensorProduct.sum_tmul, ← CStarMatrix.ofMatrix_symm_matrixUnit,
        Equiv.apply_symm_apply]
  right_inv x := by
    refine CStarMatrix.ext fun k l ↦ ?_
    simp [map_sum, CStarMatrix.sum_apply, CStarMatrix.matrixUnit_apply, ite_smul, ite_and]
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' x y := by
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]
    | tmul m a =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
      | tmul m' a' =>
        refine CStarMatrix.ext fun i j ↦ ?_
        simp [CStarMatrix.mul_apply, Finset.sum_smul, smul_mul_smul_comm]
  map_star' x := by
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simp only [star_add, map_add, h₁, h₂]
    | tmul m a =>
      refine CStarMatrix.ext fun i j ↦ ?_
      simp [CStarMatrix.star_apply, star_smul]

variable {n A}

/-- `TauCeti.cstarMatrixTensorEquiv` sends `m ⊗ a` to `[mᵢⱼ a]`. -/
@[simp]
theorem cstarMatrixTensorEquiv_apply_tmul (m : CStarMatrix n n ℂ) (a : A) (i j : n) :
    cstarMatrixTensorEquiv n A (m ⊗ₜ a) i j = m i j • a :=
  (rfl)

/-- The inverse of `TauCeti.cstarMatrixTensorEquiv` is `x ↦ Σᵢⱼ Eᵢⱼ ⊗ xᵢⱼ`. -/
@[simp]
theorem cstarMatrixTensorEquiv_symm_apply (x : CStarMatrix n n A) :
    (cstarMatrixTensorEquiv n A).symm x = ∑ i, ∑ j, CStarMatrix.matrixUnit i j ⊗ₜ x i j :=
  (rfl)

variable [PartialOrder A] [StarOrderedRing A]

/-- **The minimal norm on `M_n ⊙ A`** is the `CStarMatrix` norm (Blackadar II.9.4.2). -/
theorem minTensorNorm_eq_norm_cstarMatrixTensorEquiv (x : CStarMatrix n n ℂ ⊗[ℂ] A) :
    minTensorNorm (CStarMatrix n n ℂ) A x = ‖cstarMatrixTensorEquiv n A x‖ :=
  minTensorNorm_eq_norm_of_bijective
    (Φ := NonUnitalStarAlgHom.ofClass (cstarMatrixTensorEquiv n A))
    (cstarMatrixTensorEquiv n A).bijective x

/-- **The maximal norm on `M_n ⊙ A`** is the `CStarMatrix` norm (Blackadar II.9.4.2). -/
theorem maxTensorNorm_eq_norm_cstarMatrixTensorEquiv (x : CStarMatrix n n ℂ ⊗[ℂ] A) :
    maxTensorNorm (CStarMatrix n n ℂ) A x = ‖cstarMatrixTensorEquiv n A x‖ :=
  maxTensorNorm_eq_norm_of_bijective
    (Φ := NonUnitalStarAlgHom.ofClass (cstarMatrixTensorEquiv n A))
    (cstarMatrixTensorEquiv n A).bijective x

/-- The minimal norm of `Σᵢⱼ Eᵢⱼ ⊗ aᵢⱼ` is the `CStarMatrix` norm of `[aᵢⱼ]`. -/
theorem minTensorNorm_cstarMatrixTensorEquiv_symm (x : CStarMatrix n n A) :
    minTensorNorm (CStarMatrix n n ℂ) A ((cstarMatrixTensorEquiv n A).symm x) = ‖x‖ := by
  rw [minTensorNorm_eq_norm_cstarMatrixTensorEquiv, StarAlgEquiv.apply_symm_apply]

/-- The maximal norm of `Σᵢⱼ Eᵢⱼ ⊗ aᵢⱼ` is the `CStarMatrix` norm of `[aᵢⱼ]`. -/
theorem maxTensorNorm_cstarMatrixTensorEquiv_symm (x : CStarMatrix n n A) :
    maxTensorNorm (CStarMatrix n n ℂ) A ((cstarMatrixTensorEquiv n A).symm x) = ‖x‖ := by
  rw [maxTensorNorm_eq_norm_cstarMatrixTensorEquiv, StarAlgEquiv.apply_symm_apply]

end TauCeti
