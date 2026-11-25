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
The right action and inner product on pure tensors compute on the coefficient factor. The pure
tensors span a dense subspace, and continuous complex-linear maps into a Hausdorff codomain are
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
the inner product `⟨ξ ⊗ a, η ⊗ b⟩ = ⟨ξ, η⟩ • (star a * b)`. -/
abbrev HilbertModuleTensorProduct := Completion C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)

namespace HilbertModuleTensorProduct

/-- The canonical complex bilinear map into the completed Hilbert module tensor product. -/
noncomputable def mk : H →ₗ[ℂ] A →ₗ[ℂ] HilbertModuleTensorProduct H A :=
  (WithCStarModule.tensorTmul A).compr₂ Completion.toComplL.toLinearMap

variable {H A}

/-- A pure tensor in the completed module is the image of the corresponding algebraic tensor. -/
theorem mk_apply (ξ : H) (a : A) : mk H A ξ a =
    (WithCStarModule.tensorTmul A ξ a : HilbertModuleTensorProduct H A) := by
  simp only [mk, LinearMap.compr₂_apply, ContinuousLinearMap.coe_coe, Completion.coe_toComplL]

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
  rw [mk_apply, Completion.norm_coe, WithCStarModule.norm_tensorTmul]

/-- The complex span of the pure tensors is dense in the completed module. -/
theorem dense_span_range_mk :
    Dense (Submodule.span ℂ (Set.range fun p : H × A ↦ mk H A p.1 p.2) :
      Set (HilbertModuleTensorProduct H A)) := by
  let e := WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ (H ⊗[ℂ] A)
  let v : H × A → C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) := fun p ↦ WithCStarModule.tensorTmul A p.1 p.2
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
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro z
  refine Completion.induction_on z (isClosed_le ((lift f C hbound).continuous.norm)
    (continuous_const.mul continuous_norm)) fun x ↦ ?_
  simpa only [lift, ContinuousLinearMap.fromCompletion_apply_coe, LinearMap.mkContinuous_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, Completion.norm_coe] using hbound x

/-- The extension of bounded bilinear data computes on pure tensors. -/
@[simp] theorem lift_mk (ξ : H) (a : A) : lift f C hbound (mk H A ξ a) = f ξ a := by
  rw [mk_apply]
  simp only [lift, ContinuousLinearMap.fromCompletion_apply_coe, LinearMap.mkContinuous_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, WithCStarModule.linearEquiv_tensorTmul,
    TensorProduct.lift.tmul]

/-- Agreement with the bilinear data on pure tensors characterizes the extension. -/
theorem lift_unique (g : HilbertModuleTensorProduct H A →L[ℂ] F)
    (h : ∀ ξ a, g (mk H A ξ a) = f ξ a) : g = lift f C hbound := by
  apply ext
  intro ξ a
  rw [h, lift_mk]

end Lift

section MapIsometry

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (f : H →ₗᵢ[ℂ] K)

/-- Tensor an isometry with the identity on coefficients, then include into the completed target. -/
noncomputable def mapToCompletion :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) →ₗ[ℂ] HilbertModuleTensorProduct K A :=
  Completion.toComplL.toLinearMap ∘ₗ (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).symm.toLinearMap ∘ₗ
    TensorProduct.map f.toLinearMap LinearMap.id ∘ₗ
    (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).toLinearMap

/-- Algebraic transport sends a pure tensor to its completed image with the first factor mapped. -/
@[simp] theorem mapToCompletion_tensorTmul (ξ : H) (a : A) :
    mapToCompletion (A := A) f (WithCStarModule.tensorTmul A ξ a) = mk K A (f ξ) a := by
  simp only [mapToCompletion, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    Completion.coe_toComplL, LinearEquiv.coe_coe, WithCStarModule.linearEquiv_tensorTmul,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearIsometry.coe_toLinearMap, mk_apply]
  congr 1
  apply (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).injective
  simp

/-- Algebraic transport followed by completion preserves the coefficient-valued inner product. -/
theorem inner_mapToCompletion (x y : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    inner Aᵐᵒᵖ (mapToCompletion (A := A) f x) (mapToCompletion (A := A) f y) =
      inner Aᵐᵒᵖ x y := by
  simp only [mapToCompletion, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    Completion.coe_toComplL, PosSemidefCStarModule.inner_coe]
  apply unop_injective
  rw [WithCStarModule.unop_inner_tensor_eq_tensorPairing,
    WithCStarModule.unop_inner_tensor_eq_tensorPairing]
  simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
    tensorPairing_map_map f (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _ x)
      (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _ y)

/-- Transport from an isometric equivalence has dense range in the completed target. -/
theorem denseRange_mapToCompletion (e : H ≃ₗᵢ[ℂ] K) :
    DenseRange (mapToCompletion (A := A) e.toLinearIsometry) := by
  have hs : Function.Surjective
      (TensorProduct.map e.toLinearEquiv.toLinearMap (LinearEquiv.refl ℂ A).toLinearMap) := by
    rw [← TensorProduct.toLinearMap_congr, LinearEquiv.coe_coe]
    exact (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl ℂ A)).surjective
  have he : e.toLinearEquiv.toLinearMap = e.toLinearIsometry.toLinearMap := by
    ext x
    simp
  rw [he, LinearEquiv.refl_toLinearMap] at hs
  let h := WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ (H ⊗[ℂ] A)
  let k := WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ (K ⊗[ℂ] A)
  simpa only [mapToCompletion, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ContinuousLinearMap.coe_coe, Completion.coe_toComplL] using
    Completion.denseRange_coe.comp (k.symm.surjective.comp (hs.comp h.surjective)).denseRange
      (Completion.continuous_coe _)

/-- An isometry of the Hilbert-space factor induces a linear isometry of completed tensor
products. It also preserves their coefficient-algebra-valued inner product. -/
noncomputable def mapIsometry :
    HilbertModuleTensorProduct H A →ₗᵢ[ℂ] HilbertModuleTensorProduct K A :=
  IsPosSemidefCStarModuleAlong.liftOfInner (.id ℂ Aᵐᵒᵖ)
    (mapToCompletion f) (inner_mapToCompletion f)

/-- Tensoring an isometry acts on the Hilbert-space factor of pure tensors. -/
@[simp] theorem mapIsometry_mk (ξ : H) (a : A) :
    mapIsometry (A := A) f (mk H A ξ a) = mk K A (f ξ) a := by
  rw [mk_apply, mapIsometry, IsPosSemidefCStarModuleAlong.liftOfInner_coe,
    mapToCompletion_tensorTmul]

/-- Tensoring an isometry preserves the coefficient-algebra-valued inner product. -/
@[simp] theorem inner_mapIsometry (x y : HilbertModuleTensorProduct H A) :
    inner Aᵐᵒᵖ (mapIsometry (A := A) f x) (mapIsometry (A := A) f y) = inner Aᵐᵒᵖ x y :=
  IsPosSemidefCStarModuleAlong.inner_liftOfInner_id
    (mapToCompletion f) (inner_mapToCompletion f) x y

/-- Tensoring the identity isometry gives the identity on the completed module. -/
@[simp] theorem mapIsometry_id :
    mapIsometry (A := A) (LinearIsometry.id : H →ₗᵢ[ℂ] H) = LinearIsometry.id := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply ext
  intro ξ a
  simp

/-- Tensoring a composition gives the composition of the induced isometries. -/
@[simp] theorem mapIsometry_comp {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (g : K →ₗᵢ[ℂ] L) :
    mapIsometry (A := A) (g.comp f) = (mapIsometry (A := A) g).comp (mapIsometry (A := A) f) := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply ext
  intro ξ a
  simp

end MapIsometry

end HilbertModuleTensorProduct

end TauCeti
