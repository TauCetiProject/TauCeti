/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.TensorProduct.Completion
public import TauCeti.Analysis.CStarAlgebra.Module.Unitary

/-!
# Finite orthonormal coordinates for Hilbert C⋆-module tensor products

For a finite orthonormal basis of `H`, `OrthonormalBasis.tensorProductUnitary` identifies
the completed tensor product of `H` and `A` with the finite orthogonal sum of copies of the
right self-module `A`. Its inverse sums the basis vectors tensored with their coefficients.
-/

public section

open TauCeti MulOpposite UniformSpace
open scoped TensorProduct WithCStarModule

namespace OrthonormalBasis

variable {H A ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype ι]
  (e : OrthonormalBasis ι ℂ H)

private noncomputable def finiteCoordinates :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) ≃ₗ[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
  (e.toBasis.tensorCoordinates (A := A)).trans (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).symm

private theorem finiteCoordinates_inner (x y : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    inner Aᵐᵒᵖ (finiteCoordinates e x) (finiteCoordinates e y) = inner Aᵐᵒᵖ x y := by
  apply unop_injective
  rw [WithCStarModule.pi_inner, e.unop_inner_tensor_eq_sum]
  simp [finiteCoordinates, CStarModule.inner_mulOpposite]

/-- A finite orthonormal basis identifies the completed tensor product unitarily with the
orthogonal sum of copies of the right self-module `A`, one for each basis vector. -/
noncomputable def tensorProductUnitary :
    CStarModuleUnitary Aᵐᵒᵖ (HilbertModuleTensorProduct H A) C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := by
  let f := (finiteCoordinates (A := A) e).toLinearMap
  have h := finiteCoordinates_inner (A := A) e
  have hd : DenseRange f := (finiteCoordinates (A := A) e).surjective.denseRange
  exact ⟨IsPosSemidefCStarModuleAlong.equivOfInner (.id ℂ Aᵐᵒᵖ) f h hd,
    IsPosSemidefCStarModuleAlong.inner_equivOfInner_id f h hd⟩

private theorem tensorProductUnitary_coe (x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    e.tensorProductUnitary (A := A) (x : HilbertModuleTensorProduct H A) =
      finiteCoordinates e x :=
  IsPosSemidefCStarModuleAlong.equivOfInner_coe (.id ℂ Aᵐᵒᵖ)
    (finiteCoordinates (A := A) e).toLinearMap (finiteCoordinates_inner (A := A) e)
    (finiteCoordinates (A := A) e).surjective.denseRange x

/-- The unitary's `i`th coordinate on a pure tensor is the coefficient multiplied by the
`i`th Fourier coordinate of the Hilbert-space factor. -/
@[simp] theorem tensorProductUnitary_mk (ξ : H) (a : A) (i : ι) :
    e.tensorProductUnitary (A := A) (HilbertModuleTensorProduct.mk H A ξ a) i =
      e.repr ξ i • a := by
  rw [HilbertModuleTensorProduct.mk_apply, tensorProductUnitary_coe]
  simp [finiteCoordinates]

/-- The inverse unitary sums the pure tensors of basis vectors with their coefficients. -/
theorem tensorProductUnitary_symm_apply (a : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    (e.tensorProductUnitary (A := A)).symm a =
      ∑ i, HilbertModuleTensorProduct.mk H A (e i) (a i) := by
  let f := finiteCoordinates (A := A) e
  have h : (e.tensorProductUnitary (A := A)).symm a =
      (f.symm a : HilbertModuleTensorProduct H A) := by
    rw [← CStarModuleUnitary.toLinearIsometryEquiv_apply,
      CStarModuleUnitary.toLinearIsometryEquiv_symm]
    simpa only [tensorProductUnitary, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      (IsPosSemidefCStarModuleAlong.equivOfInner_symm_apply (.id ℂ Aᵐᵒᵖ)
        f.toLinearMap (finiteCoordinates_inner (A := A) e) f.surjective.denseRange (f.symm a))
  have hc : f.symm a =
      ∑ i, WithCStarModule.tensorTmul A (e i) (a i) := by
    simpa [f, finiteCoordinates] using e.toBasis.tensorCoordinates_symm_apply
      (WithCStarModule.equiv Aᵐᵒᵖ (ι → A) a)
  rw [h, hc]
  simpa only [Completion.coe_toComplL, HilbertModuleTensorProduct.mk_apply] using
    map_sum (Completion.toComplL :
      C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) →L[ℂ] HilbertModuleTensorProduct H A)
      (fun i ↦ WithCStarModule.tensorTmul A (e i) (a i)) Finset.univ

end OrthonormalBasis
