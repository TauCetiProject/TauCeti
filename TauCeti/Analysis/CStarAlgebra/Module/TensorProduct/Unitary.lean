/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.TensorProduct.Completion
public import TauCeti.Analysis.CStarAlgebra.Module.Unitary

/-!
# Transport of Hilbert C⋆-module tensor products by dense isometries

`LinearIsometry.hilbertModuleTensorProductUnitary` tensors a complex linear isometry with
dense range with the identity on the coefficient algebra, giving a unitary between the completed
right Hilbert modules. `LinearIsometryEquiv.hilbertModuleTensorProductUnitary` specializes this
construction to isometric equivalences.
-/

public section

open TauCeti MulOpposite

namespace LinearIsometry

variable {H K A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A complex linear isometry with dense range induces a unitary on completed tensor products
by acting on the Hilbert-space factor. -/
noncomputable def hilbertModuleTensorProductUnitary (f : H →ₗᵢ[ℂ] K) (hf : DenseRange f) :
    CStarModuleUnitary Aᵐᵒᵖ (HilbertModuleTensorProduct H A) (HilbertModuleTensorProduct K A) := by
  let g := f.toLinearMap.hilbertModuleTensorProductToCompletion (A := A)
  have h := f.inner_hilbertModuleTensorProductToCompletion (A := A)
  have hd := f.toLinearMap.denseRange_hilbertModuleTensorProductToCompletion (A := A) hf
  exact ⟨IsPosSemidefCStarModuleAlong.equivOfInner (.id ℂ Aᵐᵒᵖ) g h hd,
    IsPosSemidefCStarModuleAlong.inner_equivOfInner_id g h hd⟩

/-- The unitary induced by a dense-range isometry has the corresponding induced isometry
as its underlying map. -/
@[simp] theorem toLinearIsometry_hilbertModuleTensorProductUnitary (f : H →ₗᵢ[ℂ] K)
    (hf : DenseRange f) :
    (f.hilbertModuleTensorProductUnitary (A := A) hf).toLinearIsometryEquiv.toLinearIsometry =
      f.hilbertModuleTensorProduct := by
  rw [hilbertModuleTensorProductUnitary,
    IsPosSemidefCStarModuleAlong.toLinearIsometry_equivOfInner]
  symm
  exact (IsPosSemidefCStarModuleAlong.eq_liftOfInner_iff _ _ _ _).mpr
    f.hilbertModuleTensorProduct_coe

/-- On pure tensors the unitary induced by a dense-range isometry acts on the first factor. -/
@[simp] theorem hilbertModuleTensorProductUnitary_mk (f : H →ₗᵢ[ℂ] K) (hf : DenseRange f)
    (ξ : H) (a : A) :
    f.hilbertModuleTensorProductUnitary hf (HilbertModuleTensorProduct.mk H A ξ a) =
      HilbertModuleTensorProduct.mk K A (f ξ) a := by
  have h := congrArg (fun g : HilbertModuleTensorProduct H A →ₗᵢ[ℂ]
      HilbertModuleTensorProduct K A ↦ g (HilbertModuleTensorProduct.mk H A ξ a))
    (f.toLinearIsometry_hilbertModuleTensorProductUnitary (A := A) hf)
  simpa only [LinearIsometryEquiv.coe_toLinearIsometry,
    CStarModuleUnitary.toLinearIsometryEquiv_apply, hilbertModuleTensorProduct_mk] using h

end LinearIsometry

namespace LinearIsometryEquiv

private theorem toLinearIsometry_refl {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] : (refl ℂ E).toLinearIsometry = LinearIsometry.id := by
  ext x
  simp only [coe_toLinearIsometry, coe_refl, id_eq, LinearIsometry.id_apply]

private theorem toLinearIsometry_trans {E F G : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
    [NormedSpace ℂ E] [NormedSpace ℂ F] [NormedSpace ℂ G]
    (f : E ≃ₗᵢ[ℂ] F) (g : F ≃ₗᵢ[ℂ] G) :
    (f.trans g).toLinearIsometry = g.toLinearIsometry.comp f.toLinearIsometry := by
  ext x
  simp only [coe_toLinearIsometry, trans_apply, LinearIsometry.coe_comp, Function.comp_apply]

variable {H K A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A complex linear isometric equivalence induces a unitary on the completed tensor products
by acting on the Hilbert-space factor. -/
noncomputable def hilbertModuleTensorProductUnitary (f : H ≃ₗᵢ[ℂ] K) :
    CStarModuleUnitary Aᵐᵒᵖ (HilbertModuleTensorProduct H A) (HilbertModuleTensorProduct K A) :=
  f.toLinearIsometry.hilbertModuleTensorProductUnitary f.surjective.denseRange

/-- The unitary induced by an isometric equivalence has the corresponding induced isometry
as its underlying map. -/
@[simp] theorem toLinearIsometry_hilbertModuleTensorProductUnitary (f : H ≃ₗᵢ[ℂ] K) :
    (f.hilbertModuleTensorProductUnitary (A := A)).toLinearIsometryEquiv.toLinearIsometry =
      f.toLinearIsometry.hilbertModuleTensorProduct :=
  f.toLinearIsometry.toLinearIsometry_hilbertModuleTensorProductUnitary f.surjective.denseRange

/-- On pure tensors the induced unitary applies the equivalence to the Hilbert-space factor. -/
@[simp] theorem hilbertModuleTensorProductUnitary_mk (f : H ≃ₗᵢ[ℂ] K) (ξ : H) (a : A) :
    f.hilbertModuleTensorProductUnitary (HilbertModuleTensorProduct.mk H A ξ a) =
      HilbertModuleTensorProduct.mk K A (f ξ) a :=
  f.toLinearIsometry.hilbertModuleTensorProductUnitary_mk f.surjective.denseRange ξ a

/-- On pure tensors the inverse unitary applies the inverse equivalence to the Hilbert-space
factor. -/
@[simp] theorem hilbertModuleTensorProductUnitary_symm_mk (f : H ≃ₗᵢ[ℂ] K) (η : K) (a : A) :
    (f.hilbertModuleTensorProductUnitary (A := A)).symm (HilbertModuleTensorProduct.mk K A η a) =
      HilbertModuleTensorProduct.mk H A (f.symm η) a := by
  rw [CStarModuleUnitary.symm_apply_eq]
  simp

/-- Tensoring the inverse equivalence gives the inverse of the induced unitary. -/
@[simp] theorem hilbertModuleTensorProductUnitary_symm (f : H ≃ₗᵢ[ℂ] K) :
    f.symm.hilbertModuleTensorProductUnitary (A := A) =
      (f.hilbertModuleTensorProductUnitary (A := A)).symm := by
  apply CStarModuleUnitary.toLinearIsometryEquiv_injective
  apply LinearIsometryEquiv.toLinearIsometry_injective
  apply HilbertModuleTensorProduct.ext_linearIsometry
  intro η a
  simp only [LinearIsometryEquiv.coe_toLinearIsometry,
    CStarModuleUnitary.toLinearIsometryEquiv_apply, hilbertModuleTensorProductUnitary_mk,
    hilbertModuleTensorProductUnitary_symm_mk]

/-- Tensoring the identity equivalence gives the identity unitary on the completed module. -/
@[simp] theorem hilbertModuleTensorProductUnitary_refl :
    (LinearIsometryEquiv.refl ℂ H).hilbertModuleTensorProductUnitary (A := A) =
      CStarModuleUnitary.refl Aᵐᵒᵖ (HilbertModuleTensorProduct H A) := by
  apply CStarModuleUnitary.toLinearIsometryEquiv_injective
  apply LinearIsometryEquiv.toLinearIsometry_injective
  rw [toLinearIsometry_hilbertModuleTensorProductUnitary,
    toLinearIsometry_refl, CStarModuleUnitary.toLinearIsometryEquiv_refl,
    toLinearIsometry_refl]
  exact LinearIsometry.hilbertModuleTensorProduct_id

/-- Tensoring a composition gives the composition of the induced unitaries. -/
@[simp] theorem hilbertModuleTensorProductUnitary_trans {L : Type*} [NormedAddCommGroup L]
    [InnerProductSpace ℂ L] (f : H ≃ₗᵢ[ℂ] K) (g : K ≃ₗᵢ[ℂ] L) :
    (f.trans g).hilbertModuleTensorProductUnitary (A := A) =
      (f.hilbertModuleTensorProductUnitary (A := A)).trans g.hilbertModuleTensorProductUnitary := by
  apply CStarModuleUnitary.toLinearIsometryEquiv_injective
  apply LinearIsometryEquiv.toLinearIsometry_injective
  rw [toLinearIsometry_hilbertModuleTensorProductUnitary,
    toLinearIsometry_trans, CStarModuleUnitary.toLinearIsometryEquiv_trans,
    toLinearIsometry_trans, toLinearIsometry_hilbertModuleTensorProductUnitary,
    toLinearIsometry_hilbertModuleTensorProductUnitary]
  exact LinearIsometry.hilbertModuleTensorProduct_comp _ _

end LinearIsometryEquiv
