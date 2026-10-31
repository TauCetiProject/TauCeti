/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.TensorProduct.Map
public import TauCeti.Analysis.Normed.Operator.Completion

/-!
# Completed projective and injective tensor products

The completed projective tensor product `E ⊗̂π F` and the completed injective tensor product
`E ⊗̂ε F` are the completions of the algebraic tensor product `E ⊗[𝕜] F` for the projective and
the injective norm. Here they are `TauCeti.CompletedProjectiveTensor 𝕜 E F` and
`TauCeti.CompletedInjectiveTensor 𝕜 E F`, Mathlib's `UniformSpace.Completion` of
`TauCeti.ProjectiveTensor 𝕜 E F` and `TauCeti.InjectiveTensor 𝕜 E F`. They are Banach spaces,
and the completion map `UniformSpace.Completion.toComplₗᵢ` is a linear isometry with dense range
from the algebraic tensor product; when `E` and `F` are normed spaces over `ℝ` or `ℂ`, both
seminorms are norms and it is an isometric embedding.

Bounded operators `f : E →L[𝕜] E'` and `g : F →L[𝕜] F'` induce operators `x ⊗ₜ y ↦ f x ⊗ₜ g y`
of norm at most `‖f‖ * ‖g‖` on both completed tensor products, functorially, and the contraction
from the projective to the injective tensor product extends to a natural contraction
`E ⊗̂π F → E ⊗̂ε F`.

The completed projective tensor product has the norm-preserving universal property for Banach
targets: bounded bilinear maps `E →L[𝕜] F →L[𝕜] G` into a Banach space `G` correspond
isometrically to bounded operators `E ⊗̂π F →L[𝕜] G`. When `𝕜` is complete, for instance `ℝ` or
`ℂ`, taking `G = 𝕜` identifies the dual of `E ⊗̂π F` isometrically with the space of bounded
bilinear forms on `E × F`.

## Main definitions

* `TauCeti.CompletedProjectiveTensor 𝕜 E F` and `TauCeti.CompletedInjectiveTensor 𝕜 E F`: the
  completed projective and injective tensor products.
* `TauCeti.CompletedProjectiveTensor.liftIsometry`: the isometric universal property of the
  completed projective tensor product.
* `TauCeti.CompletedProjectiveTensor.mapL` and `TauCeti.CompletedInjectiveTensor.mapL`: the
  operators induced by a pair of bounded operators.
* `TauCeti.CompletedProjectiveTensor.toCompletedInjectiveTensor`: the contraction
  `E ⊗̂π F → E ⊗̂ε F`.

## Main results

* `TauCeti.CompletedProjectiveTensor.continuousLinearMap_ext` and
  `TauCeti.CompletedInjectiveTensor.continuousLinearMap_ext`: bounded operators out of the
  completed tensor products are determined by their values on pure tensors.
* `TauCeti.CompletedProjectiveTensor.norm_coe_tmul_le`: the completed norm of a pure tensor is at
  most the product of the norms of its factors.
* `TauCeti.CompletedProjectiveTensor.norm_mapL_le` and
  `TauCeti.CompletedInjectiveTensor.norm_mapL_le`: `‖mapL f g‖ ≤ ‖f‖ * ‖g‖`.
* `TauCeti.CompletedProjectiveTensor.toCompletedInjectiveTensor_comp_mapL`: naturality of the
  contraction from the completed projective to the completed injective tensor product.

## References

* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, §§2.1, 3.1.
* V. Runde, *Lectures on Amenability*, Springer, 2002, Appendix B.2.
-/

public section

open scoped TensorProduct

open UniformSpace

namespace TauCeti

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The completed projective tensor product `E ⊗̂π F`: the completion of the algebraic tensor
product `E ⊗[𝕜] F` for the projective norm. -/
abbrev CompletedProjectiveTensor :=
  Completion (ProjectiveTensor 𝕜 E F)

/-- The completed injective tensor product `E ⊗̂ε F`: the completion of the algebraic tensor
product `E ⊗[𝕜] F` for the injective norm. -/
abbrev CompletedInjectiveTensor :=
  Completion (InjectiveTensor 𝕜 E F)

variable {𝕜 E F} {E' E'' F' F'' G : Type*}
  [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E'] [SeminormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [SeminormedAddCommGroup F'] [NormedSpace 𝕜 F'] [SeminormedAddCommGroup F''] [NormedSpace 𝕜 F'']

namespace CompletedProjectiveTensor

/-- Two bounded operators from the completed projective tensor product to a Hausdorff space agree
when they agree on pure tensors. -/
@[ext]
theorem continuousLinearMap_ext {M : Type*} [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
    [T2Space M] {l l' : CompletedProjectiveTensor 𝕜 E F →L[𝕜] M}
    (h : ∀ x y, l (⟨x ⊗ₜ y⟩ : ProjectiveTensor 𝕜 E F) = l' (⟨x ⊗ₜ y⟩ : ProjectiveTensor 𝕜 E F)) :
    l = l' := by
  have h' : l ∘L Completion.toComplL = l' ∘L Completion.toComplL :=
    ProjectiveTensor.continuousLinearMap_ext fun x y ↦ by simpa using h x y
  exact DFunLike.coe_injective <|
    Completion.ext l.continuous l'.continuous fun u ↦ by simpa using congr($h' u)

/-- The completed projective norm of a pure tensor is at most the product of the norms of its
factors. -/
theorem norm_coe_tmul_le (x : E) (y : F) :
    ‖((⟨x ⊗ₜ y⟩ : ProjectiveTensor 𝕜 E F) : CompletedProjectiveTensor 𝕜 E F)‖ ≤ ‖x‖ * ‖y‖ := by
  simpa [Completion.norm_coe, ProjectiveTensor.norm_def] using
    TensorProduct.projectiveSeminorm_tmul_le (𝕜 := 𝕜) x y

/-- The bounded operator `x ⊗ₜ y ↦ f x ⊗ₜ g y` between completed projective tensor products
induced by bounded operators `f` and `g`. -/
noncomputable def mapL (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    CompletedProjectiveTensor 𝕜 E F →L[𝕜] CompletedProjectiveTensor 𝕜 E' F' :=
  (ProjectiveTensor.mapL f g).completion

/-- On the algebraic tensor product, the induced operator is `ProjectiveTensor.mapL f g`. -/
@[simp]
theorem mapL_coe (f : E →L[𝕜] E') (g : F →L[𝕜] F') (u : ProjectiveTensor 𝕜 E F) :
    mapL f g u = ProjectiveTensor.mapL f g u :=
  ContinuousLinearMap.completion_apply_coe _ u

/-- The operator induced by `f` and `g` on completed projective tensor products has norm at most
`‖f‖ * ‖g‖`. -/
theorem norm_mapL_le (f : E →L[𝕜] E') (g : F →L[𝕜] F') : ‖mapL f g‖ ≤ ‖f‖ * ‖g‖ :=
  (ContinuousLinearMap.norm_completion _).trans_le (ProjectiveTensor.norm_mapL_le f g)

/-- The identity operators induce the identity of the completed projective tensor product. -/
@[simp]
theorem mapL_id :
    mapL (ContinuousLinearMap.id 𝕜 E) (ContinuousLinearMap.id 𝕜 F) =
      ContinuousLinearMap.id 𝕜 (CompletedProjectiveTensor 𝕜 E F) :=
  continuousLinearMap_ext fun _ _ ↦ by simp

/-- The operator induced on completed projective tensor products respects composition. -/
theorem mapL_comp (f₂ : E' →L[𝕜] E'') (f₁ : E →L[𝕜] E') (g₂ : F' →L[𝕜] F'') (g₁ : F →L[𝕜] F') :
    mapL (f₂ ∘L f₁) (g₂ ∘L g₁) = mapL f₂ g₂ ∘L mapL f₁ g₁ :=
  continuousLinearMap_ext fun _ _ ↦ by simp

variable (𝕜 E F) in
/-- The contraction from the completed projective to the completed injective tensor product: the
extension of the identity of the underlying algebraic tensors. -/
noncomputable def toCompletedInjectiveTensor :
    CompletedProjectiveTensor 𝕜 E F →L[𝕜] CompletedInjectiveTensor 𝕜 E F :=
  (ProjectiveTensor.toInjectiveTensor 𝕜 E F).completion

/-- On the algebraic tensor product, the contraction is `ProjectiveTensor.toInjectiveTensor`. -/
@[simp]
theorem toCompletedInjectiveTensor_coe (u : ProjectiveTensor 𝕜 E F) :
    toCompletedInjectiveTensor 𝕜 E F u = ProjectiveTensor.toInjectiveTensor 𝕜 E F u :=
  ContinuousLinearMap.completion_apply_coe _ u

/-- The map from the completed projective to the completed injective tensor product is a
contraction. -/
theorem norm_toCompletedInjectiveTensor_le : ‖toCompletedInjectiveTensor 𝕜 E F‖ ≤ 1 :=
  (ContinuousLinearMap.norm_completion _).trans_le ProjectiveTensor.norm_toInjectiveTensor_le

section Lift

variable [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

variable (𝕜 E F G) in
/-- The **universal property** of the completed projective tensor product: bounded bilinear maps
`E →L[𝕜] F →L[𝕜] G` into a Banach space correspond isometrically to bounded operators on
`CompletedProjectiveTensor 𝕜 E F`. The operator induced by `B` sends `x ⊗ₜ y` to `B x y`.

When `𝕜` is complete, taking `G = 𝕜` identifies the dual of the completed projective tensor
product isometrically with the bounded bilinear forms on `E × F`. -/
noncomputable def liftIsometry :
    (E →L[𝕜] F →L[𝕜] G) ≃ₗᵢ[𝕜] (CompletedProjectiveTensor 𝕜 E F →L[𝕜] G) where
  toFun B := (ProjectiveTensor.liftIsometry 𝕜 E F G B).fromCompletion
  map_add' B B' := continuousLinearMap_ext fun x y ↦ by simp
  map_smul' a B := continuousLinearMap_ext fun x y ↦ by simp
  invFun l := (ProjectiveTensor.liftIsometry 𝕜 E F G).symm (l ∘L Completion.toComplL)
  left_inv B := by ext x y; simp
  right_inv l := continuousLinearMap_ext fun x y ↦ by simp
  norm_map' B := by simp [(ProjectiveTensor.liftIsometry 𝕜 E F G).norm_map]

/-- On the algebraic tensor product, the operator induced by a bounded bilinear map is the one
given by the universal property of `ProjectiveTensor 𝕜 E F`. -/
@[simp]
theorem liftIsometry_coe (B : E →L[𝕜] F →L[𝕜] G) (u : ProjectiveTensor 𝕜 E F) :
    liftIsometry 𝕜 E F G B u = ProjectiveTensor.liftIsometry 𝕜 E F G B u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

/-- The bilinear map corresponding to an operator `l` on the completed projective tensor product
is `(x, y) ↦ l (x ⊗ₜ y)`. -/
@[simp]
theorem liftIsometry_symm_apply_apply (l : CompletedProjectiveTensor 𝕜 E F →L[𝕜] G) (x : E)
    (y : F) : (liftIsometry 𝕜 E F G).symm l x y = l (⟨x ⊗ₜ y⟩ : ProjectiveTensor 𝕜 E F) := by
  obtain ⟨B, rfl⟩ := (liftIsometry 𝕜 E F G).surjective l
  simp

/-- Composing the operator induced by a bilinear map `B` with `mapL f g` gives the operator
induced by `(x, y) ↦ B (f x) (g y)`. -/
theorem liftIsometry_comp_mapL (B : E' →L[𝕜] F' →L[𝕜] G) (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    liftIsometry 𝕜 E' F' G B ∘L mapL f g = liftIsometry 𝕜 E F G (B.bilinearComp f g) :=
  continuousLinearMap_ext fun x y ↦ by simp

end Lift

end CompletedProjectiveTensor

namespace CompletedInjectiveTensor

/-- Two bounded operators from the completed injective tensor product to a Hausdorff space agree
when they agree on pure tensors. -/
@[ext]
theorem continuousLinearMap_ext {M : Type*} [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
    [T2Space M] {l l' : CompletedInjectiveTensor 𝕜 E F →L[𝕜] M}
    (h : ∀ x y, l (⟨x ⊗ₜ y⟩ : InjectiveTensor 𝕜 E F) = l' (⟨x ⊗ₜ y⟩ : InjectiveTensor 𝕜 E F)) :
    l = l' := by
  have h' : l ∘L Completion.toComplL = l' ∘L Completion.toComplL :=
    InjectiveTensor.continuousLinearMap_ext fun x y ↦ by simpa using h x y
  exact DFunLike.coe_injective <|
    Completion.ext l.continuous l'.continuous fun u ↦ by simpa using congr($h' u)

/-- The bounded operator `x ⊗ₜ y ↦ f x ⊗ₜ g y` between completed injective tensor products
induced by bounded operators `f` and `g`. -/
noncomputable def mapL (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    CompletedInjectiveTensor 𝕜 E F →L[𝕜] CompletedInjectiveTensor 𝕜 E' F' :=
  (InjectiveTensor.mapL f g).completion

/-- On the algebraic tensor product, the induced operator is `InjectiveTensor.mapL f g`. -/
@[simp]
theorem mapL_coe (f : E →L[𝕜] E') (g : F →L[𝕜] F') (u : InjectiveTensor 𝕜 E F) :
    mapL f g u = InjectiveTensor.mapL f g u :=
  ContinuousLinearMap.completion_apply_coe _ u

/-- The operator induced by `f` and `g` on completed injective tensor products has norm at most
`‖f‖ * ‖g‖`. -/
theorem norm_mapL_le (f : E →L[𝕜] E') (g : F →L[𝕜] F') : ‖mapL f g‖ ≤ ‖f‖ * ‖g‖ :=
  (ContinuousLinearMap.norm_completion _).trans_le (InjectiveTensor.norm_mapL_le f g)

/-- The identity operators induce the identity of the completed injective tensor product. -/
@[simp]
theorem mapL_id :
    mapL (ContinuousLinearMap.id 𝕜 E) (ContinuousLinearMap.id 𝕜 F) =
      ContinuousLinearMap.id 𝕜 (CompletedInjectiveTensor 𝕜 E F) :=
  continuousLinearMap_ext fun _ _ ↦ by simp

/-- The operator induced on completed injective tensor products respects composition. -/
theorem mapL_comp (f₂ : E' →L[𝕜] E'') (f₁ : E →L[𝕜] E') (g₂ : F' →L[𝕜] F'') (g₁ : F →L[𝕜] F') :
    mapL (f₂ ∘L f₁) (g₂ ∘L g₁) = mapL f₂ g₂ ∘L mapL f₁ g₁ :=
  continuousLinearMap_ext fun _ _ ↦ by simp

end CompletedInjectiveTensor

/-- The contraction from the completed projective to the completed injective tensor product is
natural: it intertwines the operators induced by `f` and `g`. -/
theorem CompletedProjectiveTensor.toCompletedInjectiveTensor_comp_mapL (f : E →L[𝕜] E')
    (g : F →L[𝕜] F') :
    toCompletedInjectiveTensor 𝕜 E' F' ∘L mapL f g =
      CompletedInjectiveTensor.mapL f g ∘L toCompletedInjectiveTensor 𝕜 E F :=
  continuousLinearMap_ext fun x y ↦ by simp

end TauCeti
