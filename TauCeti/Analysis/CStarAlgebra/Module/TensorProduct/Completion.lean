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
determined by their values on these tensors. Bounded bilinear data extend to continuous linear
maps, and
isometries of the Hilbert-space factor induce inner-product-preserving linear isometries.

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

private theorem toCompletionLinear_tmul (ξ : H) (a : A) :
    toCompletionLinear H A (ξ ⊗ₜ[ℂ] a) =
      (WithCStarModule.tensorTmul A ξ a : HilbertModuleTensorProduct H A) := by
  simp only [toCompletionLinear, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    Completion.coe_toComplL]
  congr 1
  apply (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).injective
  simp

/-- The canonical complex bilinear map into the completed Hilbert module tensor product. -/
noncomputable def mk : H →ₗ[ℂ] A →ₗ[ℂ] HilbertModuleTensorProduct H A :=
  (TensorProduct.mk ℂ H A).compr₂ (toCompletionLinear H A)

variable {H A}

/-- A pure tensor in the completed module is the image of the corresponding algebraic tensor. -/
theorem mk_apply (ξ : H) (a : A) : mk H A ξ a =
    (WithCStarModule.tensorTmul A ξ a : HilbertModuleTensorProduct H A) := by
  simpa only [mk, LinearMap.compr₂_apply, TensorProduct.mk_apply] using
    toCompletionLinear_tmul H A ξ a

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
  let e := (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ (H ⊗[ℂ] A)).symm
  have hspan : Submodule.span ℂ
      (Set.range fun p : H × A ↦ e (p.1 ⊗ₜ[ℂ] p.2)) = ⊤ := by
    have hraw : Submodule.span ℂ
        (Set.range fun p : H × A ↦ p.1 ⊗ₜ[ℂ] p.2) = ⊤ := by
      have hset : (Set.range fun p : H × A ↦ p.1 ⊗ₜ[ℂ] p.2) =
          {t : H ⊗[ℂ] A | ∃ ξ a, ξ ⊗ₜ[ℂ] a = t} := by
        ext z
        simp only [Set.mem_range, Set.mem_ofPred_eq, Prod.exists]
      rw [hset, TensorProduct.span_tmul_eq_top]
    rw [show (fun p : H × A ↦ e (p.1 ⊗ₜ[ℂ] p.2)) =
      e.toLinearMap ∘ (fun p : H × A ↦ p.1 ⊗ₜ[ℂ] p.2) from rfl,
      Set.range_comp, ← Submodule.map_span, hraw, Submodule.map_top, LinearEquiv.range]
  have hd : DenseRange
      (Completion.toComplL : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) →L[ℂ]
        HilbertModuleTensorProduct H A).toLinearMap := Completion.denseRange_coe
  have hv : Dense (Submodule.span ℂ
      (Set.range fun p : H × A ↦ e (p.1 ⊗ₜ[ℂ] p.2)) :
        Set C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) := by
    rw [hspan]
    exact dense_univ
  exact hd.dense_span_range_comp (Completion.continuous_coe _) hv

/-- Continuous linear maps from the completed module agree if they agree on pure tensors. -/
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

/-- A bilinear map whose algebraic linearization is bounded for the tensor-module norm extends
uniquely to the completed tensor product. -/
noncomputable def lift : HilbertModuleTensorProduct H A →L[ℂ] F :=
  ((TensorProduct.lift f ∘ₗ (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).toLinearMap).mkContinuous
    C hbound).fromCompletion

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

private noncomputable def mapToCompletion :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) →ₗ[ℂ] HilbertModuleTensorProduct K A :=
  toCompletionLinear K A ∘ₗ TensorProduct.map f.toLinearMap LinearMap.id ∘ₗ
    (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).toLinearMap

private theorem inner_mapToCompletion (x y : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    inner Aᵐᵒᵖ (mapToCompletion (A := A) f x) (mapToCompletion (A := A) f y) =
      inner Aᵐᵒᵖ x y := by
  simp only [mapToCompletion, toCompletionLinear, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, Completion.coe_toComplL,
    PosSemidefCStarModule.inner_coe]
  apply unop_injective
  rw [WithCStarModule.unop_inner_tensor_eq_tensorPairing,
    WithCStarModule.unop_inner_tensor_eq_tensorPairing]
  simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
    tensorPairing_map_map f (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _ x)
      (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _ y)

/-- An isometry of the Hilbert-space factor induces a linear isometry of completed tensor
products. It also preserves their coefficient-algebra-valued inner product. -/
noncomputable def mapIsometry :
    HilbertModuleTensorProduct H A →ₗᵢ[ℂ] HilbertModuleTensorProduct K A :=
  IsPosSemidefCStarModuleAlong.liftOfInner (.id ℂ Aᵐᵒᵖ)
    (mapToCompletion f) (inner_mapToCompletion f)

/-- Tensoring an isometry acts on the Hilbert-space factor of pure tensors. -/
@[simp] theorem mapIsometry_mk (ξ : H) (a : A) :
    mapIsometry (A := A) f (mk H A ξ a) = mk K A (f ξ) a := by
  rw [mk_apply]
  simp only [mapIsometry, IsPosSemidefCStarModuleAlong.liftOfInner_coe,
    mapToCompletion, LinearMap.comp_apply, LinearEquiv.coe_coe,
    WithCStarModule.linearEquiv_tensorTmul, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearIsometry.coe_toLinearMap]
  exact (toCompletionLinear_tmul K A (f ξ) a).trans (mk_apply (f ξ) a).symm

/-- Tensoring an isometry preserves the coefficient-algebra-valued inner product. -/
@[simp] theorem inner_mapIsometry (x y : HilbertModuleTensorProduct H A) :
    inner Aᵐᵒᵖ (mapIsometry (A := A) f x) (mapIsometry (A := A) f y) = inner Aᵐᵒᵖ x y :=
  IsPosSemidefCStarModuleAlong.inner_liftOfInner_id
    (mapToCompletion f) (inner_mapToCompletion f) x y

end MapIsometry

end HilbertModuleTensorProduct

end TauCeti
