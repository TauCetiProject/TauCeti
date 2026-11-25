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

open HilbertModuleTensorProduct

variable {H K A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A complex linear isometric equivalence induces a unitary on the completed tensor products
by acting on the Hilbert-space factor. -/
noncomputable def hilbertModuleTensorProductUnitary (f : H ≃ₗᵢ[ℂ] K) :
    CStarModuleUnitary Aᵐᵒᵖ (HilbertModuleTensorProduct H A) (HilbertModuleTensorProduct K A) := by
  let u := mapIsometry (A := A) f.toLinearIsometry
  let v := mapIsometry (A := A) f.symm.toLinearIsometry
  have huv : u.toContinuousLinearMap.comp v.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (HilbertModuleTensorProduct K A) :=
    HilbertModuleTensorProduct.ext fun ξ a ↦ by simp [u, v]
  have hsurj : Function.Surjective u := fun y ↦ ⟨v y, DFunLike.congr_fun huv y⟩
  exact ⟨LinearIsometryEquiv.ofSurjective u hsurj,
    inner_mapIsometry (A := A) f.toLinearIsometry⟩

/-- On pure tensors the induced unitary applies the equivalence to the Hilbert-space factor. -/
@[simp] theorem hilbertModuleTensorProductUnitary_mk (f : H ≃ₗᵢ[ℂ] K) (ξ : H) (a : A) :
    f.hilbertModuleTensorProductUnitary (HilbertModuleTensorProduct.mk H A ξ a) =
      HilbertModuleTensorProduct.mk K A (f ξ) a :=
  mapIsometry_mk f.toLinearIsometry ξ a

/-- On pure tensors the inverse unitary applies the inverse equivalence to the Hilbert-space
factor. -/
@[simp] theorem hilbertModuleTensorProductUnitary_symm_mk (f : H ≃ₗᵢ[ℂ] K) (η : K) (a : A) :
    (f.hilbertModuleTensorProductUnitary (A := A)).symm (HilbertModuleTensorProduct.mk K A η a) =
      HilbertModuleTensorProduct.mk H A (f.symm η) a := by
  rw [CStarModuleUnitary.symm_apply_eq]
  simp

end LinearIsometryEquiv
