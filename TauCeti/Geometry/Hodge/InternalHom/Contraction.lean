/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.InternalHom.Basic

/-!
# Integral contraction and complexification

The contraction equivalence `V* ⊗ W ≃ Hom(V, W)` commutes with complexification of finite free
integral lattices. Its inverse identifies the internal-hom Hodge filtration with the filtration
on the tensor product of the dual and the target. This lets an integral form on the tensor
product be pulled back to the integral internal hom.

The contraction maps and equivalences are Mathlib's `dualTensorHom` and `dualTensorHomEquiv`.
The Hodge-filtration comparison follows Deligne, *Théorie de Hodge II*, §2.1, and
Peters–Steenbrink, *Mixed Hodge Structures*, §2.1.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

variable {V₁ V₂ W₁ W₂ : Type*} [AddCommGroup V₁] [AddCommGroup V₂]
variable [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
variable {ι₁ : V₁ →ₗ[ℤ] W₁} {ι₂ : V₂ →ₗ[ℤ] W₂}
variable [Module.Free ℤ V₁] [Module.Finite ℤ V₁]

/-- Complexifying integral contraction gives contraction of the complexified dual and target. -/
@[simp]
theorem integralMapToComplex_dualTensorHom (h₁ : IsBaseChange ℂ ι₁)
    (h₂ : IsBaseChange ℂ ι₂) :
    integralMapToComplex (isBaseChange_tensorLatticeMap (isBaseChange_dualLatticeMap h₁) h₂)
      (homLatticeMap h₁ ι₂) (dualTensorHom ℤ V₁ V₂).toAddMonoidHom.toIntLinearMap =
        dualTensorHom ℂ W₁ W₂ := by
  refine (isBaseChange_tensorLatticeMap (isBaseChange_dualLatticeMap h₁) h₂).algHom_ext _ _
    fun z ↦ ?_
  rw [integralMapToComplex_apply_ι, homLatticeMap_apply]
  induction z using TensorProduct.inductionOn with
  | tmul φ y =>
    refine h₁.algHom_ext _ _ fun x ↦ ?_
    simp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe,
      integralMapToComplex_apply_ι, dualTensorHom_apply, map_smul, tensorLatticeMap_tmul,
      dualLatticeMap_apply_ι]
    exact (Int.cast_smul_eq_zsmul ℂ (φ x) (ι₂ y)).symm
  | add z z' hz hz' =>
    simp only [map_add, integralMapToComplex_add]
    exact congrArg₂ (· + ·) hz hz'

/-- The inverse integral contraction equivalence complexifies to inverse complex contraction. -/
@[simp]
theorem integralMapToComplex_dualTensorHomEquiv_symm (h₁ : IsBaseChange ℂ ι₁)
    (h₂ : IsBaseChange ℂ ι₂) :
    letI : Module.Finite ℂ W₁ := h₁.finite
    integralMapToComplex (isBaseChange_homLatticeMap h₁ h₂)
      (tensorLatticeMap (dualLatticeMap h₁) ι₂)
      (dualTensorHomEquiv ℤ V₁ V₂).symm.toLinearMap.toAddMonoidHom.toIntLinearMap =
        (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  let _ : Module.Finite ℂ W₁ := h₁.finite
  have hcomp : dualTensorHom ℂ W₁ W₂ ∘ₗ
      integralMapToComplex (isBaseChange_homLatticeMap h₁ h₂)
        (tensorLatticeMap (dualLatticeMap h₁) ι₂)
        (dualTensorHomEquiv ℤ V₁ V₂).symm.toLinearMap.toAddMonoidHom.toIntLinearMap =
      LinearMap.id := by
    rw [← integralMapToComplex_dualTensorHom h₁ h₂, ← integralMapToComplex_comp]
    have hcancel : (dualTensorHom ℤ V₁ V₂).toAddMonoidHom.toIntLinearMap ∘ₗ
        (dualTensorHomEquiv ℤ V₁ V₂).symm.toLinearMap.toAddMonoidHom.toIntLinearMap =
        LinearMap.id := by
      ext φ x
      simp
    rw [hcancel, integralMapToComplex_id]
  ext φ
  apply (dualTensorHom_bijective (R := ℂ) (M := W₁) (N := W₂)).1
  simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
    dualTensorHom_dualTensorHomEquiv_symm] using LinearMap.congr_fun hcomp φ

namespace HodgeStructure

variable {h₁ : IsBaseChange ℂ ι₁} {h₂ : IsBaseChange ℂ ι₂} {n₁ n₂ : ℤ}

/-- Integral internal-hom filtrations are pulled back from `V* ⊗ W` along inverse contraction. -/
theorem internalHom_F_eq_comap (hs₁ : HodgeStructure h₁ n₁)
    (hs₂ : HodgeStructure h₂ n₂) (p : ℤ) :
    letI : Module.Finite ℂ W₁ := h₁.finite
    (hs₁.internalHom hs₂).F p = ((hs₁.dual.tensorProduct hs₂).F p).comap
      (dualTensorHomEquiv ℂ W₁ W₂).symm.toLinearMap := by
  let _ : Module.Finite ℂ W₁ := h₁.finite
  rw [internalHom_F, HodgeStructureOn.internalHom_F_eq_comap, tensorProduct_F]
  congr 1
  simp only [HodgeStructureOn.tensorProduct_F_eq_iSup_piece, dual_piece]

end HodgeStructure

end TauCeti.Hodge
