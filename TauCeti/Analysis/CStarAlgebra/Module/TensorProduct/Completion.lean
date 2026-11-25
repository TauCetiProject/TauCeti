/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Completion
public import TauCeti.Analysis.CStarAlgebra.Module.TensorProduct.Basic
public import TauCeti.Analysis.CStarAlgebra.Module.Unitary

/-!
# The Hilbert C⋆-module tensor product of a Hilbert space with a C⋆-algebra

`HilbertModuleTensorProduct H A` completes the complex algebraic tensor product of an inner
product space `H` and a possibly nonunital C⋆-algebra `A` in the `A`-valued inner-product norm.
The right action and inner product on pure tensors compute on the coefficient factor. The pure
tensors span a dense subspace, and bounded linear maps out of the completion are determined by
their values on these tensors. A finite orthonormal basis of `H` identifies the completed tensor
product unitarily with the corresponding finite orthogonal sum of copies of `A`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 4.
* The density and extensionality proofs follow `TensorProduct.dense_span_coe_tmul` and
  `TensorProduct.completion_ext` for scalar Hilbert tensor products.
-/

public section

open MulOpposite UniformSpace
open scoped TensorProduct WithCStarModule

namespace TauCeti

variable (H A : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The right Hilbert `A`-module `H ⊗ A`, the completion of the algebraic tensor product for
the inner product `⟨ξ ⊗ a, η ⊗ b⟩ = ⟨ξ, η⟩ • (star a * b)`. -/
abbrev HilbertModuleTensorProduct := Completion C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)

namespace HilbertModuleTensorProduct

private noncomputable def toCompletionLinear : H ⊗[ℂ] A →ₗ[ℂ] HilbertModuleTensorProduct H A :=
  Completion.toComplL.toLinearMap ∘ₗ (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).symm.toLinearMap

private theorem denseRange_toCompletionLinear : DenseRange (toCompletionLinear H A) :=
  Completion.denseRange_coe.comp
    (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).symm.surjective.denseRange
    (Completion.continuous_coe _)

/-- The canonical complex bilinear map into the completed Hilbert module tensor product. -/
noncomputable def mk : H →ₗ[ℂ] A →ₗ[ℂ] HilbertModuleTensorProduct H A :=
  (TensorProduct.mk ℂ H A).compr₂ (toCompletionLinear H A)

variable {H A}

/-- A pure tensor in the completed module is the image of the corresponding algebraic tensor. -/
theorem mk_apply (ξ : H) (a : A) : mk H A ξ a =
    (WithCStarModule.tensorTmul A ξ a : HilbertModuleTensorProduct H A) := by
  rw [WithCStarModule.tensorTmul_eq]
  rfl

/-- The inner product of two completed pure tensors in the opposite-algebra convention. -/
@[simp] theorem inner_mk (ξ η : H) (a b : A) :
    inner Aᵐᵒᵖ (mk H A ξ a) (mk H A η b) = op (inner ℂ ξ η • (star a * b)) := by
  rw [mk_apply, mk_apply, PosSemidefCStarModule.inner_coe,
    WithCStarModule.inner_tensorTmul_tensorTmul]

/-- Right multiplication of a pure tensor acts on its coefficient. -/
@[simp] theorem op_smul_mk (ξ : H) (a b : A) :
    op b • mk H A ξ a = mk H A ξ (a * b) := by
  rw [mk_apply, mk_apply, ← Completion.coe_smul, WithCStarModule.op_smul_tensorTmul]

/-- The norm of a pure tensor is the product of the norms of its two factors. -/
@[simp] theorem norm_mk (ξ : H) (a : A) : ‖mk H A ξ a‖ = ‖ξ‖ * ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  have hξ : ‖inner ℂ ξ ξ‖ = ‖ξ‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg ξ)]
  rw [CStarModule.norm_sq_eq Aᵐᵒᵖ, inner_mk, norm_op, norm_smul, hξ,
    CStarRing.norm_star_mul_self, ← sq, mul_pow]

/-- The complex span of the pure tensors is dense in the completed module. -/
theorem dense_span_range_mk :
    Dense (Submodule.span ℂ (Set.range fun p : H × A ↦ mk H A p.1 p.2) :
      Set (HilbertModuleTensorProduct H A)) := by
  have hspan : Submodule.span ℂ (Set.range fun p : H × A ↦ mk H A p.1 p.2) =
      (toCompletionLinear H A).range := by
    rw [← Submodule.map_top, ← TensorProduct.span_tmul_eq_top ℂ H A, Submodule.map_span]
    congr 1
    ext z
    simp [mk]
  rw [hspan, LinearMap.coe_range]
  exact denseRange_toCompletionLinear H A

/-- Continuous linear maps from the completed module agree if they agree on pure tensors. -/
@[ext] theorem ext {F : Type*} [AddCommMonoid F] [Module ℂ F] [TopologicalSpace F] [T2Space F]
    {f g : HilbertModuleTensorProduct H A →L[ℂ] F}
    (h : ∀ (ξ : H) (a : A), f (mk H A ξ a) = g (mk H A ξ a)) : f = g := by
  have heq : f.toLinearMap ∘ₗ toCompletionLinear H A = g.toLinearMap ∘ₗ toCompletionLinear H A :=
    TensorProduct.ext' h
  exact DFunLike.coe_injective <| (denseRange_toCompletionLinear H A).equalizer
    f.continuous g.continuous (funext (LinearMap.congr_fun heq))

section Finite

variable {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ H)

private noncomputable def finiteCoordinates :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) ≃ₗ[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
  (WithCStarModule.tensorCoordinates e).trans (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).symm

private theorem finiteCoordinates_inner (x y : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    inner Aᵐᵒᵖ (finiteCoordinates e x) (finiteCoordinates e y) = inner Aᵐᵒᵖ x y := by
  apply unop_injective
  rw [WithCStarModule.pi_inner, WithCStarModule.unop_inner_tensor_eq_sum e]
  simp [finiteCoordinates, CStarModule.inner_mulOpposite]

/-- A finite orthonormal basis identifies `H ⊗ A` unitarily with the orthogonal sum of copies
of the right self-module `A`, with one copy for each basis vector. -/
noncomputable def unitaryOfOrthonormalBasis :
    CStarModuleUnitary Aᵐᵒᵖ (HilbertModuleTensorProduct H A) C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := by
  let f := (finiteCoordinates (A := A) e).toLinearMap
  have h := finiteCoordinates_inner (A := A) e
  have hd : DenseRange f := (finiteCoordinates (A := A) e).surjective.denseRange
  exact ⟨IsPosSemidefCStarModuleAlong.equivOfInner (.id ℂ Aᵐᵒᵖ) f h hd,
    IsPosSemidefCStarModuleAlong.inner_equivOfInner_id f h hd⟩

/-- On a pure tensor, the coordinate unitary multiplies its coefficient by each Fourier
coordinate of its Hilbert-space factor. -/
@[simp] theorem unitaryOfOrthonormalBasis_mk (ξ : H) (a : A) (i : ι) :
    unitaryOfOrthonormalBasis (A := A) e (mk H A ξ a) i = e.repr ξ i • a := by
  rw [mk_apply]
  simp [unitaryOfOrthonormalBasis, finiteCoordinates]

/-- The inverse coordinate unitary sums the pure tensors of basis vectors with their
corresponding coefficients. -/
theorem unitaryOfOrthonormalBasis_symm_apply (a : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    (unitaryOfOrthonormalBasis (A := A) e).symm a = ∑ i, mk H A (e i) (a i) := by
  have h : (unitaryOfOrthonormalBasis (A := A) e).symm a =
      ((finiteCoordinates (A := A) e).symm a : HilbertModuleTensorProduct H A) := by
    apply EquivLike.injective (unitaryOfOrthonormalBasis (A := A) e)
    simp [unitaryOfOrthonormalBasis]
  have hc : (finiteCoordinates (A := A) e).symm a =
      ∑ i, WithCStarModule.tensorTmul A (e i) (a i) := by
    simpa [finiteCoordinates] using WithCStarModule.tensorCoordinates_symm_apply e
      (WithCStarModule.equiv Aᵐᵒᵖ (ι → A) a)
  rw [h, hc]
  simpa only [Completion.coe_toComplL, mk_apply] using
    map_sum (Completion.toComplL : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) →L[ℂ] HilbertModuleTensorProduct H A)
      (fun i ↦ WithCStarModule.tensorTmul A (e i) (a i)) Finset.univ

end Finite

end HilbertModuleTensorProduct

end TauCeti
