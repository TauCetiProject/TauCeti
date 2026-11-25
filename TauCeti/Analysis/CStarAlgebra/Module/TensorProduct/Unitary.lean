/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.TensorProduct.Completion
public import TauCeti.Analysis.CStarAlgebra.Module.Unitary

/-!
# Transport of Hilbert C⋆-module tensor products by isometric equivalences

`LinearIsometryEquiv.hilbertModuleTensorProductUnitary` tensors a complex linear
isometric equivalence with the identity on the coefficient algebra, giving a unitary
between the completed right Hilbert modules.
-/

public section

open TauCeti MulOpposite

namespace LinearIsometryEquiv

variable {H K A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A complex linear isometric equivalence induces a unitary on the completed tensor products
by acting on the Hilbert-space factor. -/
noncomputable def hilbertModuleTensorProductUnitary (f : H ≃ₗᵢ[ℂ] K) :
    CStarModuleUnitary Aᵐᵒᵖ (HilbertModuleTensorProduct H A) (HilbertModuleTensorProduct K A) := by
  let g := f.toLinearIsometry.toLinearMap.hilbertModuleTensorProductToCompletion (A := A)
  have h := f.toLinearIsometry.inner_hilbertModuleTensorProductToCompletion (A := A)
  have hd := f.toLinearIsometry.toLinearMap.denseRange_hilbertModuleTensorProductToCompletion
    (A := A) f.surjective
  exact ⟨IsPosSemidefCStarModuleAlong.equivOfInner (.id ℂ Aᵐᵒᵖ) g h hd,
    IsPosSemidefCStarModuleAlong.inner_equivOfInner_id g h hd⟩

/-- The unitary induced by an isometric equivalence has the corresponding induced isometry
as its underlying map. -/
@[simp] theorem toLinearIsometry_hilbertModuleTensorProductUnitary (f : H ≃ₗᵢ[ℂ] K) :
    (f.hilbertModuleTensorProductUnitary (A := A)).toLinearIsometryEquiv.toLinearIsometry =
      f.toLinearIsometry.hilbertModuleTensorProduct := by
  rw [hilbertModuleTensorProductUnitary,
    IsPosSemidefCStarModuleAlong.toLinearIsometry_equivOfInner]
  symm
  exact (IsPosSemidefCStarModuleAlong.eq_liftOfInner_iff _ _ _ _).mpr
    f.toLinearIsometry.hilbertModuleTensorProduct_coe

/-- On pure tensors the induced unitary applies the equivalence to the Hilbert-space factor. -/
@[simp] theorem hilbertModuleTensorProductUnitary_mk (f : H ≃ₗᵢ[ℂ] K) (ξ : H) (a : A) :
    f.hilbertModuleTensorProductUnitary (HilbertModuleTensorProduct.mk H A ξ a) =
      HilbertModuleTensorProduct.mk K A (f ξ) a := by
  have h := congrArg (fun g : HilbertModuleTensorProduct H A →ₗᵢ[ℂ]
      HilbertModuleTensorProduct K A ↦ g (HilbertModuleTensorProduct.mk H A ξ a))
    (f.toLinearIsometry_hilbertModuleTensorProductUnitary (A := A))
  simpa only [LinearIsometryEquiv.coe_toLinearIsometry,
    CStarModuleUnitary.toLinearIsometryEquiv_apply, LinearIsometry.hilbertModuleTensorProduct_mk]
    using h

/-- On pure tensors the inverse unitary applies the inverse equivalence to the Hilbert-space
factor. -/
@[simp] theorem hilbertModuleTensorProductUnitary_symm_mk (f : H ≃ₗᵢ[ℂ] K) (η : K) (a : A) :
    (f.hilbertModuleTensorProductUnitary (A := A)).symm (HilbertModuleTensorProduct.mk K A η a) =
      HilbertModuleTensorProduct.mk H A (f.symm η) a := by
  rw [CStarModuleUnitary.symm_apply_eq]
  simp

/-- Tensoring the identity equivalence gives the identity unitary on the completed module. -/
@[simp] theorem hilbertModuleTensorProductUnitary_refl :
    (LinearIsometryEquiv.refl ℂ H).hilbertModuleTensorProductUnitary (A := A) =
      CStarModuleUnitary.refl Aᵐᵒᵖ (HilbertModuleTensorProduct H A) := by
  apply CStarModuleUnitary.toLinearIsometryEquiv_injective
  apply LinearIsometryEquiv.toLinearIsometry_injective
  rw [toLinearIsometry_hilbertModuleTensorProductUnitary,
    CStarModuleUnitary.toLinearIsometryEquiv_refl]
  exact LinearIsometry.hilbertModuleTensorProduct_id

/-- Tensoring a composition gives the composition of the induced unitaries. -/
@[simp] theorem hilbertModuleTensorProductUnitary_trans {L : Type*} [NormedAddCommGroup L]
    [InnerProductSpace ℂ L] (f : H ≃ₗᵢ[ℂ] K) (g : K ≃ₗᵢ[ℂ] L) :
    (f.trans g).hilbertModuleTensorProductUnitary (A := A) =
      (f.hilbertModuleTensorProductUnitary (A := A)).trans g.hilbertModuleTensorProductUnitary := by
  apply CStarModuleUnitary.toLinearIsometryEquiv_injective
  apply LinearIsometryEquiv.toLinearIsometry_injective
  rw [toLinearIsometry_hilbertModuleTensorProductUnitary,
    CStarModuleUnitary.toLinearIsometryEquiv_trans]
  -- The isometry underlying a composite equivalence is the composite of the underlying maps.
  change (g.toLinearIsometry.comp f.toLinearIsometry).hilbertModuleTensorProduct (A := A) =
    ((g.hilbertModuleTensorProductUnitary (A := A)).toLinearIsometryEquiv.toLinearIsometry).comp
      (f.hilbertModuleTensorProductUnitary (A := A)).toLinearIsometryEquiv.toLinearIsometry
  rw [toLinearIsometry_hilbertModuleTensorProductUnitary,
    toLinearIsometry_hilbertModuleTensorProductUnitary]
  exact LinearIsometry.hilbertModuleTensorProduct_comp _ _

end LinearIsometryEquiv
