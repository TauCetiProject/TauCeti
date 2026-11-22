/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Forgetting continuity of bilinear maps

`ContinuousLinearMap.toLinearMap₁₂` sends a continuous bilinear map `L : E →L F →L G` to the
underlying bilinear map `E →ₗ F →ₗ G`. This file records how it commutes with the basic
operations on continuous bilinear maps, so that algebraic results stated for bilinear maps (such
as the metric trace `LinearMap.BilinMap.metricTrace`) apply to converted continuous maps without
reproving the conversion pointwise:

* `ContinuousLinearMap.toLinearMap₁₂_comp`: precomposition in the first argument,
  `(L.comp g).toLinearMap₁₂ = L.toLinearMap₁₂.comp g`;
* `ContinuousLinearMap.toLinearMap₁₂_flip`: transposition, `L.flip.toLinearMap₁₂ =
  L.toLinearMap₁₂.flip`;
* `ContinuousLinearMap.toLinearMap₁₂_bilinearComp`: precomposition in both arguments,
  `(L.bilinearComp f g).toLinearMap₁₂ = L.toLinearMap₁₂.compl₁₂ f g`;
* `ContinuousLinearMap.toLinearMap₁₂_smulRight`: rank-one maps, `(f.smulRight A).toLinearMap₁₂ =
  (f : E →ₗ 𝕜).smulRight (A : F →ₗ G)`.
-/

public section

namespace ContinuousLinearMap

section Comp

variable {R₀ R₁ 𝕜₂ 𝕜₃ : Type*} [Semiring R₀] [Semiring R₁] [NormedField 𝕜₂] [NormedField 𝕜₃]
  {D E F G : Type*} [AddCommMonoid D] [Module R₀ D] [TopologicalSpace D]
  [AddCommMonoid E] [Module R₁ E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜₃ G]
  {σ₀₁ : R₀ →+* R₁} {σ₁₃ : R₁ →+* 𝕜₃} {σ₀₃ : R₀ →+* 𝕜₃} [RingHomCompTriple σ₀₁ σ₁₃ σ₀₃]
  {σ₂₃ : 𝕜₂ →+* 𝕜₃}

/-- Forgetting continuity commutes with precomposition in the first argument. -/
@[simp]
theorem toLinearMap₁₂_comp (L : E →SL[σ₁₃] F →SL[σ₂₃] G) (g : D →SL[σ₀₁] E) :
    toLinearMap₁₂ (L.comp g) = (toLinearMap₁₂ L).comp (g : D →ₛₗ[σ₀₁] E) :=
  LinearMap.ext₂ fun _ _ ↦ by
    simp only [toLinearMap₁₂_apply_apply_apply, LinearMap.comp_apply, coe_comp, Function.comp_apply,
      coe_coe]

end Comp

section Flip

variable {𝕜 𝕜₂ 𝕜₃ : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NontriviallyNormedField 𝕜₃] {σ₁₃ : 𝕜 →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃}
  [RingHomIsometric σ₁₃] [RingHomIsometric σ₂₃]
  {E F G : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsNormableSpace 𝕜 E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F] [IsNormableSpace 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace G] [IsNormableSpace 𝕜₃ G]
  [IsTopologicalAddGroup G]

/-- Forgetting continuity commutes with transposing the arguments. -/
@[simp]
theorem toLinearMap₁₂_flip (L : E →SL[σ₁₃] F →SL[σ₂₃] G) :
    toLinearMap₁₂ L.flip = (toLinearMap₁₂ L).flip :=
  LinearMap.ext₂ fun _ _ ↦ by
    simp only [toLinearMap₁₂_apply_apply_apply, LinearMap.flip_apply, flip_apply]

end Flip

section SMulRight

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Forgetting continuity sends the rank-one map `(v, w) ↦ f v • A w` to the rank-one bilinear map
of the underlying linear maps. -/
@[simp]
theorem toLinearMap₁₂_smulRight (f : E →L[𝕜] 𝕜) (A : F →L[𝕜] G) :
    toLinearMap₁₂ (f.smulRight A) = (f : E →ₗ[𝕜] 𝕜).smulRight (A : F →ₗ[𝕜] G) :=
  LinearMap.ext₂ fun _ _ ↦ by
    simp only [toLinearMap₁₂_apply_apply_apply, LinearMap.smulRight_apply, smulRight_apply,
      LinearMap.smul_apply, smul_apply, coe_coe]

end SMulRight

section BilinearComp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G E' F' : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsNormableSpace 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsNormableSpace 𝕜 G]
  [IsTopologicalAddGroup G]
  [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E'] [IsNormableSpace 𝕜 E']
  [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F'] [IsNormableSpace 𝕜 F']

/-- Forgetting continuity commutes with precomposition in both arguments: the continuous pullback
`L.bilinearComp f g` becomes the algebraic pullback `L.compl₁₂ f g`. -/
@[simp]
theorem toLinearMap₁₂_bilinearComp (L : E →L[𝕜] F →L[𝕜] G) (f : E' →L[𝕜] E) (g : F' →L[𝕜] F) :
    toLinearMap₁₂ (L.bilinearComp f g) =
      (toLinearMap₁₂ L).compl₁₂ (f : E' →ₗ[𝕜] E) (g : F' →ₗ[𝕜] F) :=
  LinearMap.ext₂ fun _ _ ↦ by
    simp only [toLinearMap₁₂_apply_apply_apply, LinearMap.compl₁₂_apply, bilinearComp_apply,
      coe_coe]

end BilinearComp

end ContinuousLinearMap
