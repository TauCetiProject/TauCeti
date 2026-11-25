/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Action
public import TauCeti.Analysis.CStarAlgebra.Module.Completion
public import TauCeti.Analysis.CStarAlgebra.Module.TensorProduct.Basic

import TauCeti.Topology.Algebra.Module.Span
import TauCeti.Topology.Algebra.Module.TensorProduct

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
  `TensorProduct.completion_ext` in
  `TauCeti.Analysis.InnerProductSpace.TensorProduct.Completion` for scalar Hilbert tensor products.
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

private theorem subsingleton_completion {E : Type*} [UniformSpace E] [Subsingleton E] :
    Subsingleton (Completion E) := by
  have h := (Set.subsingleton_range ((↑) : E → Completion E)).closure
  rw [Completion.denseRange_coe.closure_eq] at h
  exact Set.subsingleton_univ_iff.mp h

/-- Tensoring the zero inner product space gives the zero Hilbert module. -/
instance [Subsingleton H] : Subsingleton (HilbertModuleTensorProduct H A) := by
  let : Unique (H ⊗[ℂ] A) := TensorProduct.uniqueLeft
  exact subsingleton_completion

/-- Tensoring with the zero coefficient algebra gives the zero Hilbert module. -/
instance [Subsingleton A] : Subsingleton (HilbertModuleTensorProduct H A) := by
  let : Unique (H ⊗[ℂ] A) := TensorProduct.uniqueRight
  exact subsingleton_completion

/-- The completed coefficient action preserves vector addition and zero. -/
noncomputable instance : DistribSMul Aᵐᵒᵖ (HilbertModuleTensorProduct H A) :=
  CStarModule.distribSMul Aᵐᵒᵖ (HilbertModuleTensorProduct H A)

/-- A zero coefficient acts by zero on the completed tensor product. -/
noncomputable instance : SMulWithZero Aᵐᵒᵖ (HilbertModuleTensorProduct H A) :=
  CStarModule.smulWithZero Aᵐᵒᵖ (HilbertModuleTensorProduct H A)

/-- Coefficient multiplication agrees with successive actions on the completed tensor product. -/
noncomputable instance : SemigroupAction Aᵐᵒᵖ (HilbertModuleTensorProduct H A) :=
  CStarModule.semigroupAction Aᵐᵒᵖ (HilbertModuleTensorProduct H A)

/-- Complex scalars commute with coefficient multiplication on the completed tensor product. -/
instance : SMulCommClass ℂ Aᵐᵒᵖ (HilbertModuleTensorProduct H A) :=
  CStarModule.smulCommClass Aᵐᵒᵖ (HilbertModuleTensorProduct H A)

/-- Complex scaling of a coefficient agrees with successive actions on the completion. -/
instance : IsScalarTower ℂ Aᵐᵒᵖ (HilbertModuleTensorProduct H A) :=
  CStarModule.isScalarTower Aᵐᵒᵖ (HilbertModuleTensorProduct H A)

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
  let f : H ⊗[ℂ] A →ₗ[ℂ] HilbertModuleTensorProduct H A :=
    Completion.toComplL.toLinearMap ∘ₗ e.symm.toLinearMap
  have hf : DenseRange f := by
    rw [DenseRange,
      show ⇑f = ((↑) : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) → HilbertModuleTensorProduct H A) ∘ e.symm by
      simp only [f, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Completion.coe_toComplL,
        LinearEquiv.coe_coe], e.symm.surjective.range_comp]
    exact Completion.denseRange_coe
  have hmk (ξ : H) (a : A) : f (ξ ⊗ₜ[ℂ] a) = mk H A ξ a := by
    rw [← linearEquiv_tensorTmul A ξ a, mk_apply]
    simp only [f, e, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe, Completion.coe_toComplL]
  simpa only [hmk] using hf.dense_span_range_tmul

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
theorem norm_tensorProductLift_apply_le_opNorm_mul {F : Type*}
    [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (f : H →ₗ[ℂ] A →ₗ[ℂ] F) (g : HilbertModuleTensorProduct H A →L[ℂ] F)
    (h : ∀ ξ a, g (mk H A ξ a) = f ξ a)
    (x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    ‖TensorProduct.lift f (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _ x)‖ ≤ ‖g‖ * ‖x‖ := by
  let e := WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ (H ⊗[ℂ] A)
  let G := g.toLinearMap ∘ₗ Completion.toComplL.toLinearMap ∘ₗ e.symm.toLinearMap
  have hG (z : H ⊗[ℂ] A) : G z = g (e.symm z : HilbertModuleTensorProduct H A) := by
    simp only [G, LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
      Completion.coe_toComplL]
  have hlin : G = TensorProduct.lift f := by
    apply TensorProduct.lift.unique
    intro ξ a
    rw [hG, ← h ξ a, mk_apply, ← linearEquiv_tensorTmul A ξ a, e.symm_apply_apply]
  rw [← hlin, hG, e.symm_apply_apply]
  simpa only [Completion.norm_coe] using g.le_opNorm (x : HilbertModuleTensorProduct H A)

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

variable {H K A : Type*} [AddCommGroup H] [Module ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (f : H →ₗ[ℂ] K)

/-- Tensor a linear map with the identity on coefficients, then include into the completed
target. The source is the algebraic tensor product. -/
noncomputable def hilbertModuleTensorProductToCompletion :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) →ₗ[ℂ] HilbertModuleTensorProduct K A :=
  Completion.toComplL.toLinearMap ∘ₗ f.hilbertModuleTensorProductMap

private theorem hilbertModuleTensorProductToCompletion_apply_map
    (x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    f.hilbertModuleTensorProductToCompletion x =
      (f.hilbertModuleTensorProductMap x : HilbertModuleTensorProduct K A) := by
  simp only [hilbertModuleTensorProductToCompletion, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, Completion.coe_toComplL]

/-- On arbitrary algebraic tensors, transport maps the first factor before completion. -/
theorem hilbertModuleTensorProductToCompletion_apply
    (x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    f.hilbertModuleTensorProductToCompletion x =
      (((WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).symm
        (TensorProduct.map f LinearMap.id (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _ x)) :
          C⋆ᵐᵒᵈ(Aᵐᵒᵖ, K ⊗[ℂ] A)) : HilbertModuleTensorProduct K A) := by
  rw [hilbertModuleTensorProductToCompletion_apply_map]
  apply congrArg (fun y : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, K ⊗[ℂ] A) ↦
    (y : HilbertModuleTensorProduct K A))
  apply (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).injective
  rw [linearEquiv_hilbertModuleTensorProductMap, LinearEquiv.apply_symm_apply]

/-- Algebraic transport sends a pure tensor to its completed image with the first factor mapped. -/
@[simp] theorem hilbertModuleTensorProductToCompletion_tensorTmul (ξ : H) (a : A) :
    f.hilbertModuleTensorProductToCompletion (tensorTmul A ξ a) =
      HilbertModuleTensorProduct.mk K A (f ξ) a := by
  rw [hilbertModuleTensorProductToCompletion_apply_map, mk_apply]
  congr 1
  apply (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).injective
  simp only [linearEquiv_hilbertModuleTensorProductMap, linearEquiv_tensorTmul,
    TensorProduct.map_tmul, LinearMap.id_apply]

/-- Transport by a linear map with dense range has dense range in the completed target. -/
theorem denseRange_hilbertModuleTensorProductToCompletion (hf : DenseRange f) :
    DenseRange (f.hilbertModuleTensorProductToCompletion (A := A)) := by
  let g := f.hilbertModuleTensorProductToCompletion (A := A)
  let L : K → A → HilbertModuleTensorProduct K A := fun ξ a ↦
    HilbertModuleTensorProduct.mk K A ξ a
  have hL (a : A) : Continuous (fun ξ ↦ L ξ a) :=
    (((HilbertModuleTensorProduct.mk K A).flip a).mkContinuous ‖a‖ fun ξ ↦ by
      simp only [LinearMap.flip_apply, norm_mk, mul_comm, le_refl]).continuous
  have hspan : (⋃ ξ, Set.range (L ξ)) = Set.range (fun p : K × A ↦ L p.1 p.2) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_range, Prod.exists]
  have hp : g.range.topologicalClosure = ⊤ := eq_top_iff.2 <|
    calc
      ⊤ = (Submodule.span ℂ (⋃ ξ : H, Set.range (L (f ξ)))).topologicalClosure := by
        rw [hf.topologicalClosure_span_iUnion_range_comp_eq hL, hspan]
        exact (Submodule.dense_iff_topologicalClosure_eq_top.1 dense_span_range_mk).symm
      _ ≤ g.range.topologicalClosure := Submodule.topologicalClosure_mono <|
          Submodule.span_le.2 <| by
            intro z hz
            obtain ⟨ξ, a, rfl⟩ := Set.mem_iUnion.mp hz
            exact ⟨tensorTmul A ξ a, f.hilbertModuleTensorProductToCompletion_tensorTmul ξ a⟩
  simpa only [DenseRange, LinearMap.coe_range] using
    (Submodule.dense_iff_topologicalClosure_eq_top.2 hp)

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
  simp only [LinearMap.hilbertModuleTensorProductToCompletion_apply_map,
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
