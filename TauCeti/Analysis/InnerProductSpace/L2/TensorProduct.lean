/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import TauCeti.Analysis.InnerProductSpace.L2.Product
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# `L²` of a product measure is the completed Hilbert tensor product

For σ-finite measures `μ` and `ν`, the space `L²(μ ⊗ ν)` is the completed Hilbert tensor product
of `L²(μ)` and `L²(ν)`: there is a unique unitary

`Completion (L²(μ) ⊗[𝕜] L²(ν)) ≃ₗᵢ[𝕜] L²(μ ⊗ ν)`

sending each elementary tensor `f ⊗ g` to the class of the pointwise product
`(x, y) ↦ f x * g y` (`MeasureTheory.Lp.completedTensorProdEquiv`). Here `L²(μ) ⊗[𝕜] L²(ν)` is the
algebraic tensor product with Mathlib's tensor inner product
`⟪f₁ ⊗ g₁, f₂ ⊗ g₂⟫ = ⟪f₁, f₂⟫ * ⟪g₁, g₂⟫`, and `Completion` is its uniform completion. This is the
form in which operators on the two factors, such as elliptic operators on two compact manifolds,
act on functions on the product: an operator acting on each factor separately is an operator on
the completed tensor product, and this unitary carries it to `L²` of the product.

The construction has two steps.

* By Fubini's theorem the pointwise product preserves the tensor inner product
  (`MeasureTheory.Lp.inner_prodMul`), so the linear map
  `MeasureTheory.Lp.tensorProdMul : L²(μ) ⊗[𝕜] L²(ν) →ₗ[𝕜] L²(μ ⊗ ν)` induced by it is an isometry
  (`MeasureTheory.Lp.tensorProdMulₗᵢ`). This needs only s-finite measures.
* Pointwise products of two Hilbert bases form a Hilbert basis of `L²(μ ⊗ ν)`
  (`HilbertBasis.prod`), so the range of `tensorProdMul` is dense
  (`MeasureTheory.Lp.denseRange_tensorProdMul`). The extension of the isometry to the completion
  has complete, hence closed, range, so it is onto.

No separability is assumed: the Hilbert bases may have any index type.

## Main declarations

* `MeasureTheory.Lp.tensorProdMul`: the linear map `f ⊗ g ↦ (x, y) ↦ f x * g y` on the algebraic
  tensor product, with `MeasureTheory.Lp.inner_tensorProdMul` and
  `MeasureTheory.Lp.norm_tensorProdMul`.
* `MeasureTheory.Lp.tensorProdMulₗᵢ`: the same map as a linear isometry.
* `MeasureTheory.Lp.denseRange_tensorProdMul`: its range is dense for σ-finite measures.
* `MeasureTheory.Lp.completedTensorProdEquiv`: the unitary from the completed tensor product onto
  `L²(μ ⊗ ν)`, with its values `MeasureTheory.Lp.completedTensorProdEquiv_coe_tmul` on elementary
  tensors, their almost everywhere representatives
  `MeasureTheory.Lp.coeFn_completedTensorProdEquiv_coe_tmul`, and the inverse
  `MeasureTheory.Lp.completedTensorProdEquiv_symm_prodMul`.
* `MeasureTheory.Lp.eq_completedTensorProdEquiv_iff`: it is the only continuous linear map from
  the completed tensor product with these values on elementary tensors.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  edition, Academic Press, 1980, §II.4, Theorem II.10.
-/

public section

open MeasureTheory UniformSpace
open scoped TensorProduct

variable {𝕜 α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β}

namespace MeasureTheory.Lp

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜]

/-- The linear map from the algebraic tensor product `L²(μ) ⊗[𝕜] L²(ν)` to `L²(μ ⊗ ν)` sending
`f ⊗ g` to the pointwise product `(x, y) ↦ f x * g y`. -/
noncomputable def tensorProdMul : Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν →ₗ[𝕜] Lp 𝕜 2 (μ.prod ν) :=
  TensorProduct.lift (prodMulL (𝕜 := 𝕜) (μ := μ) (ν := ν)).toLinearMap₁₂

/-- On an elementary tensor, `tensorProdMul` is the pointwise product. -/
@[simp]
theorem tensorProdMul_tmul (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    tensorProdMul (F ⊗ₜ[𝕜] G) = prodMul F G := by
  simp [tensorProdMul]

end NontriviallyNormedField

variable [RCLike 𝕜] [SFinite μ] [SFinite ν]

/-- `tensorProdMul` preserves inner products: by Fubini's theorem the pointwise product turns the
tensor inner product `⟪f₁ ⊗ g₁, f₂ ⊗ g₂⟫ = ⟪f₁, f₂⟫ * ⟪g₁, g₂⟫` into the inner product of
`L²(μ ⊗ ν)`. -/
@[simp]
theorem inner_tensorProdMul (x y : Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν) :
    inner 𝕜 (tensorProdMul x) (tensorProdMul y) = inner 𝕜 x y := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | tmul F₁ G₁ =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | tmul F₂ G₂ => simp

/-- `tensorProdMul` as a linear isometry from the algebraic tensor product into `L²(μ ⊗ ν)`. -/
noncomputable def tensorProdMulₗᵢ : Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν →ₗᵢ[𝕜] Lp 𝕜 2 (μ.prod ν) :=
  tensorProdMul.isometryOfInner inner_tensorProdMul

@[simp]
theorem coe_tensorProdMulₗᵢ :
    ⇑(tensorProdMulₗᵢ : Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν →ₗᵢ[𝕜] Lp 𝕜 2 (μ.prod ν)) = tensorProdMul := by
  rw [tensorProdMulₗᵢ, LinearMap.coe_isometryOfInner]

/-- `tensorProdMul` preserves norms. -/
@[simp]
theorem norm_tensorProdMul (x : Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν) : ‖tensorProdMul x‖ = ‖x‖ := by
  simpa using tensorProdMulₗᵢ.norm_map x

/-- `tensorProdMul` is injective. -/
theorem tensorProdMul_injective :
    Function.Injective (tensorProdMul : Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν → Lp 𝕜 2 (μ.prod ν)) := by
  simpa using (tensorProdMulₗᵢ (𝕜 := 𝕜) (μ := μ) (ν := ν)).injective

omit [SFinite μ] [SFinite ν] in
/-- For σ-finite measures, finite sums of pointwise products `(x, y) ↦ f x * g y` are dense in
`L²(μ ⊗ ν)`: the range of `tensorProdMul` contains the span of the product Hilbert basis built
from any Hilbert bases of `L²(μ)` and `L²(ν)`. -/
theorem denseRange_tensorProdMul [SigmaFinite μ] [SigmaFinite ν] :
    DenseRange (tensorProdMul : Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν → Lp 𝕜 2 (μ.prod ν)) := by
  obtain ⟨w₁, b₁, -⟩ := exists_hilbertBasis 𝕜 (Lp 𝕜 2 μ)
  obtain ⟨w₂, b₂, -⟩ := exists_hilbertBasis 𝕜 (Lp 𝕜 2 ν)
  have hspan : Submodule.span 𝕜 (Set.range (b₁.prod b₂)) ≤ LinearMap.range tensorProdMul := by
    rw [Submodule.span_le]
    rintro _ ⟨ij, rfl⟩
    exact ⟨b₁ ij.1 ⊗ₜ[𝕜] b₂ ij.2, by simp⟩
  have hdense : Dense (Submodule.span 𝕜 (Set.range (b₁.prod b₂)) : Set (Lp 𝕜 2 (μ.prod ν))) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 (b₁.prod b₂).dense_span
  simpa only [DenseRange, ← LinearMap.coe_range] using hdense.mono hspan

variable [SigmaFinite μ] [SigmaFinite ν]

/-- The extension of `tensorProdMulₗᵢ` to the completion is onto: its range is complete, hence
closed, and contains the dense range of `tensorProdMul`. -/
private theorem surjective_fromCompletion_tensorProdMulₗᵢ :
    Function.Surjective (tensorProdMulₗᵢ.fromCompletion :
      Completion (Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν) →ₗᵢ[𝕜] Lp 𝕜 2 (μ.prod ν)) := by
  set f := (tensorProdMulₗᵢ : Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν →ₗᵢ[𝕜] Lp 𝕜 2 (μ.prod ν)).fromCompletion
  have hclosed : IsClosed (Set.range f) := f.isometry.isUniformInducing.isComplete_range.isClosed
  intro h
  refine closure_minimal ?_ hclosed (denseRange_tensorProdMul h)
  rintro _ ⟨x, rfl⟩
  exact ⟨x, tensorProdMulₗᵢ.fromCompletion_apply_coe x⟩

/-- **`L²` of a product measure is the completed Hilbert tensor product.** For σ-finite `μ` and
`ν`, the unitary from the completion of `L²(μ) ⊗[𝕜] L²(ν)` onto `L²(μ ⊗ ν)` sending `f ⊗ g` to the
pointwise product `(x, y) ↦ f x * g y`. -/
noncomputable def completedTensorProdEquiv :
    Completion (Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν) ≃ₗᵢ[𝕜] Lp 𝕜 2 (μ.prod ν) :=
  LinearIsometryEquiv.ofSurjective _ surjective_fromCompletion_tensorProdMulₗᵢ

/-- On the algebraic tensor product, `completedTensorProdEquiv` is `tensorProdMul`. -/
@[simp]
theorem completedTensorProdEquiv_coe (x : Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν) :
    completedTensorProdEquiv (x : Completion (Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν)) = tensorProdMul x :=
  tensorProdMulₗᵢ.fromCompletion_apply_coe x

/-- `completedTensorProdEquiv` sends `f ⊗ g` to the pointwise product `(x, y) ↦ f x * g y`. -/
theorem completedTensorProdEquiv_coe_tmul (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    completedTensorProdEquiv ((F ⊗ₜ[𝕜] G : Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν) :
      Completion (Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν)) = prodMul F G := by
  simp

/-- The image of `f ⊗ g` under `completedTensorProdEquiv` is represented almost everywhere by
the pointwise product of representatives of `f` and `g`. -/
theorem coeFn_completedTensorProdEquiv_coe_tmul (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    ⇑(completedTensorProdEquiv ((F ⊗ₜ[𝕜] G : Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν) :
      Completion (Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν))) =ᵐ[μ.prod ν] fun p ↦ F p.1 * G p.2 := by
  rw [completedTensorProdEquiv_coe_tmul]
  exact coeFn_prodMul F G

/-- The inverse of `completedTensorProdEquiv` sends the pointwise product
`(x, y) ↦ f x * g y` to `f ⊗ g`. -/
@[simp]
theorem completedTensorProdEquiv_symm_prodMul (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    completedTensorProdEquiv.symm (prodMul F G) =
      ((F ⊗ₜ[𝕜] G : Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν) : Completion (Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν)) := by
  rw [LinearIsometryEquiv.symm_apply_eq, completedTensorProdEquiv_coe_tmul]

/-- **Uniqueness of the unitary.** A continuous linear map from the completed tensor product to
`L²(μ ⊗ ν)` is `completedTensorProdEquiv` exactly when it sends every `f ⊗ g` to the pointwise
product `(x, y) ↦ f x * g y`. -/
theorem eq_completedTensorProdEquiv_iff
    {T : Completion (Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν) →L[𝕜] Lp 𝕜 2 (μ.prod ν)} :
    T = completedTensorProdEquiv.toContinuousLinearEquiv.toContinuousLinearMap ↔
      ∀ (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν),
        T ((F ⊗ₜ[𝕜] G : Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν) : Completion (Lp 𝕜 2 μ ⊗[𝕜] Lp 𝕜 2 ν)) =
          prodMul F G := by
  refine ⟨fun h F G ↦ by simp [h], fun h ↦ ?_⟩
  -- Both maps extend `tensorProdMul` from the algebraic tensor product to its completion.
  refine (ContinuousLinearMap.fromCompletion_unique _ T fun x ↦ ?_).symm
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => rw [map_add, Completion.coe_add, map_add, h₁, h₂]
  | tmul F G => simp [h F G]

end MeasureTheory.Lp
