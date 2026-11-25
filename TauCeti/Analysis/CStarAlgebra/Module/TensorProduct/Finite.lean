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

For a finite orthonormal basis of `H`,
`OrthonormalBasis.hilbertModuleTensorProductUnitary` identifies the completed tensor product of
`H` and `A` with the finite orthogonal sum of copies of the right self-module `A`. Its inverse
sums the basis vectors tensored with their coefficients.
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

omit [PartialOrder A] [StarOrderedRing A] in
private theorem finiteCoordinates_symm_apply (a : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    (finiteCoordinates e).symm a =
      e.toBasis.tensorCoordinates.symm (WithCStarModule.equiv Aᵐᵒᵖ (ι → A) a) := by
  rw [finiteCoordinates, LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
    WithCStarModule.linearEquiv_apply]

private theorem finiteCoordinates_inner (x y : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    inner Aᵐᵒᵖ (finiteCoordinates e x) (finiteCoordinates e y) = inner Aᵐᵒᵖ x y := by
  apply unop_injective
  rw [WithCStarModule.pi_inner, e.unop_inner_tensor_eq_sum]
  simp [finiteCoordinates, CStarModule.inner_mulOpposite]

/-- A finite orthonormal basis identifies the completed tensor product unitarily with the
orthogonal sum of copies of the right self-module `A`, one for each basis vector. -/
noncomputable def hilbertModuleTensorProductUnitary :
    CStarModuleUnitary Aᵐᵒᵖ (HilbertModuleTensorProduct H A) C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := by
  let f := (finiteCoordinates (A := A) e).toLinearMap
  have h := finiteCoordinates_inner (A := A) e
  have hd : DenseRange f := (finiteCoordinates (A := A) e).surjective.denseRange
  exact ⟨IsPosSemidefCStarModuleAlong.equivOfInner (.id ℂ Aᵐᵒᵖ) f h hd,
    IsPosSemidefCStarModuleAlong.inner_equivOfInner_id f h hd⟩

/-- The unitary's coordinates on an algebraic tensor are its basis tensor coordinates. -/
@[simp] theorem hilbertModuleTensorProductUnitary_coe
    (x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) (i : ι) :
    e.hilbertModuleTensorProductUnitary (A := A) (x : HilbertModuleTensorProduct H A) i =
      e.toBasis.tensorCoordinates x i := by
  rw [hilbertModuleTensorProductUnitary, CStarModuleUnitary.mk_apply,
    IsPosSemidefCStarModuleAlong.equivOfInner_coe, LinearEquiv.coe_coe]
  simp only [finiteCoordinates, LinearEquiv.trans_apply,
    WithCStarModule.linearEquiv_symm_apply, WithCStarModule.equiv_symm_pi_apply]

/-- The unitary's `i`th coordinate on a pure tensor is the coefficient multiplied by the
`i`th Fourier coordinate of the Hilbert-space factor. -/
@[simp] theorem hilbertModuleTensorProductUnitary_mk (ξ : H) (a : A) (i : ι) :
    e.hilbertModuleTensorProductUnitary (A := A) (HilbertModuleTensorProduct.mk H A ξ a) i =
      e.repr ξ i • a := by
  rw [HilbertModuleTensorProduct.mk_apply, hilbertModuleTensorProductUnitary_coe]
  simp

/-- The inverse unitary sums the pure tensors of basis vectors with their coefficients. -/
theorem hilbertModuleTensorProductUnitary_symm_apply (a : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    (e.hilbertModuleTensorProductUnitary (A := A)).symm a =
      ∑ i, HilbertModuleTensorProduct.mk H A (e i) (a i) := by
  have h : (e.hilbertModuleTensorProductUnitary (A := A)).symm a =
      ((finiteCoordinates e).symm a : HilbertModuleTensorProduct H A) := by
    let f := (finiteCoordinates (A := A) e).toLinearMap
    have hf := finiteCoordinates_inner (A := A) e
    have hd : DenseRange f := (finiteCoordinates (A := A) e).surjective.denseRange
    have hi := IsPosSemidefCStarModuleAlong.equivOfInner_symm_apply (.id ℂ Aᵐᵒᵖ)
      f hf hd ((finiteCoordinates e).symm a)
    rw [← CStarModuleUnitary.toLinearIsometryEquiv_apply,
      CStarModuleUnitary.toLinearIsometryEquiv_symm, hilbertModuleTensorProductUnitary]
    simpa only [f, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hi
  rw [h, finiteCoordinates_symm_apply, Module.Basis.tensorCoordinates_symm_apply]
  simpa only [Completion.coe_toComplL, HilbertModuleTensorProduct.mk_apply,
    OrthonormalBasis.coe_toBasis, WithCStarModule.equiv_pi_apply] using
    map_sum (Completion.toComplL :
      C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) →L[ℂ] HilbertModuleTensorProduct H A)
      (fun i ↦ tensorTmul A (e i) (a i)) Finset.univ

end OrthonormalBasis
