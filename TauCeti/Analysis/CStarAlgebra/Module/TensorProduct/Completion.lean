/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Completion
public import TauCeti.Analysis.CStarAlgebra.Module.TensorProduct.Basic

import TauCeti.Topology.Algebra.Module.Span

/-!
# The Hilbert C⋆-module tensor product of a Hilbert space with a C⋆-algebra

`HilbertModuleTensorProduct H A` completes the complex algebraic tensor product of an inner
product space `H` and a possibly nonunital C⋆-algebra `A` in the `A`-valued inner-product norm.
The right action of `a : A` is the left action of `MulOpposite.op a : Aᵐᵒᵖ`. Applying
`MulOpposite.unop` to Lean's opposite-valued inner product on pure tensors gives the usual
right-module formula, as recorded in `HilbertModuleTensorProduct.inner_mk`. The pure tensors
span a dense subspace, and continuous complex-linear maps into a Hausdorff codomain are
determined by their values on these tensors. A bilinear map into a complete normed space extends
to a continuous linear map when its algebraic linearization is bounded for the tensor-module
norm. Isometries of the Hilbert-space factor induce inner-product-preserving linear isometries.

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
the right-module inner product `⟨ξ ⊗ a, η ⊗ b⟩ = ⟨ξ, η⟩ • (star a * b)`.
In Lean, the right action is a left `Aᵐᵒᵖ` action and the formula is
`MulOpposite.unop` of `HilbertModuleTensorProduct.inner_mk`. -/
abbrev HilbertModuleTensorProduct := Completion C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)

namespace HilbertModuleTensorProduct

/-- The canonical complex bilinear map into the completed Hilbert module tensor product. -/
noncomputable def mk : H →ₗ[ℂ] A →ₗ[ℂ] HilbertModuleTensorProduct H A :=
  (tensorTmul A).compr₂ Completion.toComplL.toLinearMap

variable {H A}

/-- A pure tensor in the completed module is the image of the corresponding algebraic tensor. -/
theorem mk_apply (ξ : H) (a : A) : mk H A ξ a =
    (tensorTmul A ξ a : HilbertModuleTensorProduct H A) := by
  simp only [mk, LinearMap.compr₂_apply, ContinuousLinearMap.coe_coe, Completion.coe_toComplL]

/-- The inner product of two completed pure tensors in the opposite-algebra convention. -/
@[simp] theorem inner_mk (ξ η : H) (a b : A) :
    inner Aᵐᵒᵖ (mk H A ξ a) (mk H A η b) = op (inner ℂ ξ η • (star a * b)) := by
  rw [mk_apply, mk_apply, PosSemidefCStarModule.inner_coe,
    inner_tensorTmul_tensorTmul]

/-- Right multiplication of a pure tensor acts on its coefficient. -/
@[simp] theorem op_smul_mk (ξ : H) (a b : A) :
    op b • mk H A ξ a = mk H A ξ (a * b) := by
  rw [mk_apply, mk_apply, ← Completion.coe_smul, op_smul_tensorTmul]

/-- The norm of a pure tensor is the product of the norms of its two factors. -/
@[simp] theorem norm_mk (ξ : H) (a : A) : ‖mk H A ξ a‖ = ‖ξ‖ * ‖a‖ := by
  rw [mk_apply, Completion.norm_coe, norm_tensorTmul]

/-- The complex span of the pure tensors is dense in the completed module. -/
theorem dense_span_range_mk :
    Dense (Submodule.span ℂ (Set.range fun p : H × A ↦ mk H A p.1 p.2) :
      Set (HilbertModuleTensorProduct H A)) := by
  let e := WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ (H ⊗[ℂ] A)
  let v : H × A → C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) := fun p ↦ tensorTmul A p.1 p.2
  let tmul : H × A → H ⊗[ℂ] A := fun p ↦ p.1 ⊗ₜ[ℂ] p.2
  have hv : v = e.symm.toLinearMap ∘ tmul := by
    funext p
    apply e.injective
    simp [v, e, tmul]
  have hraw : Submodule.span ℂ (Set.range tmul) = ⊤ := by
    have hset : Set.range tmul = {t : H ⊗[ℂ] A | ∃ ξ a, ξ ⊗ₜ[ℂ] a = t} := by
      ext z
      simp only [tmul, Set.mem_range, Set.mem_ofPred_eq, Prod.exists]
    rw [hset, TensorProduct.span_tmul_eq_top]
  have hspan : Dense (Submodule.span ℂ (Set.range v) : Set C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) := by
    -- Expose the composition so that `Set.range_comp` turns the range into a linear image.
    rw [hv, Set.range_comp, ← Submodule.map_span, hraw, Submodule.map_top, LinearEquiv.range]
    exact dense_univ
  let g : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) →L[ℂ] HilbertModuleTensorProduct H A := Completion.toComplL
  have hg : DenseRange g.toLinearMap := Completion.denseRange_coe
  have hmk : g.toLinearMap ∘ v = fun p : H × A ↦ mk H A p.1 p.2 := by
    funext p
    simp only [g, v, Function.comp_apply, ContinuousLinearMap.coe_coe, Completion.coe_toComplL,
      mk_apply]
  rw [← hmk]
  exact hg.dense_span_range_comp g.continuous hspan

/-- Continuous linear maps into a Hausdorff codomain agree if they agree on pure tensors. -/
@[ext] theorem ext {F : Type*} [AddCommMonoid F] [Module ℂ F] [TopologicalSpace F] [T2Space F]
    {f g : HilbertModuleTensorProduct H A →L[ℂ] F}
    (h : ∀ (ξ : H) (a : A), f (mk H A ξ a) = g (mk H A ξ a)) : f = g := by
  apply ContinuousLinearMap.ext_on dense_span_range_mk
  rintro _ ⟨⟨ξ, a⟩, rfl⟩
  exact h ξ a

section Lift

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  (f : H →ₗ[ℂ] A →ₗ[ℂ] F) (C : ℝ)
  (hbound : ∀ x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A),
    ‖TensorProduct.lift f (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _ x)‖ ≤ C * ‖x‖)

/-- A bilinear map into a complete normed space extends uniquely to the completed tensor product
when its algebraic linearization is bounded for the tensor-module norm. -/
noncomputable def lift : HilbertModuleTensorProduct H A →L[ℂ] F :=
  ((TensorProduct.lift f ∘ₗ (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).toLinearMap).mkContinuous
    C hbound).fromCompletion

/-- The extension has operator norm at most the given nonnegative bound on the linearization. -/
theorem norm_lift_le (hC : 0 ≤ C) : ‖lift f C hbound‖ ≤ C := by
  rw [lift, ContinuousLinearMap.norm_fromCompletion]
  exact LinearMap.mkContinuous_norm_le _ hC hbound

/-- On the algebraic tensor product the extension equals the algebraic linearization. -/
@[simp] theorem lift_coe (x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    lift f C hbound (x : HilbertModuleTensorProduct H A) =
      TensorProduct.lift f (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _ x) := by
  simp only [lift, ContinuousLinearMap.fromCompletion_apply_coe, LinearMap.mkContinuous_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe]

/-- The extension of bounded bilinear data computes on pure tensors. -/
@[simp] theorem lift_mk (ξ : H) (a : A) : lift f C hbound (mk H A ξ a) = f ξ a := by
  rw [mk_apply, lift_coe, linearEquiv_tensorTmul, TensorProduct.lift.tmul]

/-- Agreement with the bilinear data on pure tensors characterizes the extension. -/
theorem lift_unique (g : HilbertModuleTensorProduct H A →L[ℂ] F)
    (h : ∀ ξ a, g (mk H A ξ a) = f ξ a) : g = lift f C hbound := by
  apply ext
  intro ξ a
  rw [h, lift_mk]

end Lift

/-- A continuous extension of bilinear data bounds its algebraic linearization by its
operator norm. -/
theorem norm_lift_apply_le_of_agrees {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : H →ₗ[ℂ] A →ₗ[ℂ] F) (g : HilbertModuleTensorProduct H A →L[ℂ] F)
    (h : ∀ ξ a, g (mk H A ξ a) = f ξ a)
    (x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    ‖TensorProduct.lift f (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _ x)‖ ≤ ‖g‖ * ‖x‖ := by
  let e := WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ (H ⊗[ℂ] A)
  have hlin : g.toLinearMap ∘ₗ Completion.toComplL.toLinearMap ∘ₗ e.symm.toLinearMap =
      TensorProduct.lift f := by
    apply TensorProduct.ext'
    intro ξ a
    rw [TensorProduct.lift.tmul, ← h ξ a]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
      Completion.coe_toComplL, mk_apply]
    rw [← linearEquiv_tensorTmul A ξ a, e.symm_apply_apply]
  rw [← hlin]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, e, LinearEquiv.symm_apply_apply,
    ContinuousLinearMap.coe_coe, Completion.coe_toComplL, Completion.norm_coe] using
    g.le_opNorm (x : HilbertModuleTensorProduct H A)

/-- Linear isometries out of the completed tensor product agree if they agree on pure tensors. -/
@[ext] theorem ext_linearIsometry {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    [T2Space F] {f g : HilbertModuleTensorProduct H A →ₗᵢ[ℂ] F}
    (h : ∀ (ξ : H) (a : A), f (mk H A ξ a) = g (mk H A ξ a)) : f = g :=
  LinearIsometry.toContinuousLinearMap_injective (ext h)

end HilbertModuleTensorProduct

end TauCeti

open TauCeti HilbertModuleTensorProduct

namespace LinearMap

section Algebraic

variable {H K A : Type*} [AddCommGroup H] [Module ℂ H] [AddCommGroup K] [Module ℂ K]
  [AddCommGroup A] [Module ℂ A] (f : H →ₗ[ℂ] K)

private def hilbertModuleTensorProductMap :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) →ₗ[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, K ⊗[ℂ] A) :=
  ((WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).arrowCongr
    (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _)).symm (TensorProduct.map f LinearMap.id)

private theorem linearEquiv_hilbertModuleTensorProductMap
    (x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _ (f.hilbertModuleTensorProductMap x) =
      TensorProduct.map f LinearMap.id (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _ x) := by
  simp only [hilbertModuleTensorProductMap, LinearEquiv.arrowCongr_symm_apply,
    LinearEquiv.apply_symm_apply]

end Algebraic

variable {H K A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (f : H →ₗ[ℂ] K)

/-- Tensor a linear map with the identity on coefficients, then include into the completed
target. The source is the algebraic tensor product. -/
noncomputable def hilbertModuleTensorProductToCompletion :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) →ₗ[ℂ] HilbertModuleTensorProduct K A :=
  Completion.toComplL.toLinearMap ∘ₗ f.hilbertModuleTensorProductMap

private theorem hilbertModuleTensorProductToCompletion_apply
    (x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    f.hilbertModuleTensorProductToCompletion x =
      (f.hilbertModuleTensorProductMap x : HilbertModuleTensorProduct K A) := by
  simp only [hilbertModuleTensorProductToCompletion, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, Completion.coe_toComplL]

/-- Algebraic transport sends a pure tensor to its completed image with the first factor mapped. -/
@[simp] theorem hilbertModuleTensorProductToCompletion_tensorTmul (ξ : H) (a : A) :
    f.hilbertModuleTensorProductToCompletion (tensorTmul A ξ a) =
      HilbertModuleTensorProduct.mk K A (f ξ) a := by
  rw [hilbertModuleTensorProductToCompletion_apply, mk_apply]
  congr 1
  apply (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).injective
  simp only [linearEquiv_hilbertModuleTensorProductMap, linearEquiv_tensorTmul,
    TensorProduct.map_tmul, LinearMap.id_apply]

/-- Transport by a surjective linear map has dense range in the completed target. -/
theorem denseRange_hilbertModuleTensorProductToCompletion (hf : Function.Surjective f) :
    DenseRange (f.hilbertModuleTensorProductToCompletion (A := A)) := by
  have hs : Function.Surjective (TensorProduct.map f (LinearMap.id : A →ₗ[ℂ] A)) :=
    TensorProduct.map_surjective hf Function.surjective_id
  have hmap : Function.Surjective (f.hilbertModuleTensorProductMap (A := A)) :=
    (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).symm.surjective.comp
      (hs.comp (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).surjective)
  rw [hilbertModuleTensorProductToCompletion, LinearMap.coe_comp, ContinuousLinearMap.coe_coe,
    Completion.coe_toComplL]
  exact Completion.denseRange_coe.comp hmap.denseRange (Completion.continuous_coe _)

end LinearMap

namespace LinearIsometry

variable {H K A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (f : H →ₗᵢ[ℂ] K)

/-- Algebraic transport by an isometry preserves the coefficient-valued inner product. -/
theorem inner_hilbertModuleTensorProductToCompletion
    (x y : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    inner Aᵐᵒᵖ (f.toLinearMap.hilbertModuleTensorProductToCompletion x)
      (f.toLinearMap.hilbertModuleTensorProductToCompletion y) = inner Aᵐᵒᵖ x y := by
  simp only [LinearMap.hilbertModuleTensorProductToCompletion_apply,
    PosSemidefCStarModule.inner_coe]
  apply unop_injective
  simp only [WithCStarModule.unop_inner_tensor_eq_tensorPairing,
    LinearMap.linearEquiv_hilbertModuleTensorProductMap, tensorPairing_map_map]

/-- An isometry of the Hilbert-space factor induces a linear isometry of completed tensor
products. It also preserves their coefficient-algebra-valued inner product. -/
noncomputable def hilbertModuleTensorProduct :
    HilbertModuleTensorProduct H A →ₗᵢ[ℂ] HilbertModuleTensorProduct K A :=
  IsPosSemidefCStarModuleAlong.liftOfInner (.id ℂ Aᵐᵒᵖ)
    f.toLinearMap.hilbertModuleTensorProductToCompletion
    f.inner_hilbertModuleTensorProductToCompletion

/-- On algebraic tensors, the completed isometry agrees with algebraic transport. -/
@[simp] theorem hilbertModuleTensorProduct_coe
    (x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    f.hilbertModuleTensorProduct (x : HilbertModuleTensorProduct H A) =
      f.toLinearMap.hilbertModuleTensorProductToCompletion x := by
  rw [hilbertModuleTensorProduct, IsPosSemidefCStarModuleAlong.liftOfInner_coe]

/-- Tensoring an isometry acts on the Hilbert-space factor of pure tensors. -/
@[simp] theorem hilbertModuleTensorProduct_mk (ξ : H) (a : A) :
    f.hilbertModuleTensorProduct (HilbertModuleTensorProduct.mk H A ξ a) =
      HilbertModuleTensorProduct.mk K A (f ξ) a := by
  rw [mk_apply, hilbertModuleTensorProduct_coe,
    LinearMap.hilbertModuleTensorProductToCompletion_tensorTmul, coe_toLinearMap]

/-- Tensoring an isometry preserves the coefficient-algebra-valued inner product. -/
@[simp] theorem inner_hilbertModuleTensorProduct (x y : HilbertModuleTensorProduct H A) :
    inner Aᵐᵒᵖ (f.hilbertModuleTensorProduct x) (f.hilbertModuleTensorProduct y) =
      inner Aᵐᵒᵖ x y :=
  IsPosSemidefCStarModuleAlong.inner_liftOfInner_id
    f.toLinearMap.hilbertModuleTensorProductToCompletion
    f.inner_hilbertModuleTensorProductToCompletion x y

/-- The induced isometry commutes with the right coefficient action. -/
@[simp] theorem hilbertModuleTensorProduct_smul (a : Aᵐᵒᵖ) (x : HilbertModuleTensorProduct H A) :
    f.hilbertModuleTensorProduct (a • x) = a • f.hilbertModuleTensorProduct x := by
  rw [hilbertModuleTensorProduct, IsPosSemidefCStarModuleAlong.liftOfInner_smul]

/-- Tensoring the identity isometry gives the identity on the completed module. -/
@[simp] theorem hilbertModuleTensorProduct_id :
    (LinearIsometry.id : H →ₗᵢ[ℂ] H).hilbertModuleTensorProduct (A := A) = LinearIsometry.id := by
  apply ext_linearIsometry
  intro ξ a
  simp

/-- Tensoring a composition gives the composition of the induced isometries. -/
@[simp] theorem hilbertModuleTensorProduct_comp {L : Type*} [NormedAddCommGroup L]
    [InnerProductSpace ℂ L] (g : K →ₗᵢ[ℂ] L) :
    (g.comp f).hilbertModuleTensorProduct (A := A) =
      (g.hilbertModuleTensorProduct (A := A)).comp f.hilbertModuleTensorProduct := by
  apply ext_linearIsometry
  intro ξ a
  simp

end LinearIsometry
