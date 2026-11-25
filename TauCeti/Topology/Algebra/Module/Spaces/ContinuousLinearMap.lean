/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Forgetting continuity of bilinear maps

`ContinuousLinearMap.toLinearMap₁₂` sends a continuous bilinear map `L : E →L F →L G` to the
underlying bilinear map `E →ₗ F →ₗ G`. This file records how it commutes with the topology-level
operations on continuous bilinear maps, so that algebraic results stated for bilinear maps (such
as the metric trace `LinearMap.BilinMap.metricTrace`) apply to converted continuous maps without
reproving the conversion pointwise:

* `ContinuousLinearMap.toLinearMap₁₂_comp`: precomposition in the first argument,
  `(L.comp g).toLinearMap₁₂ = L.toLinearMap₁₂.comp g`;
* `ContinuousLinearMap.toLinearMap₁₂_smulRight`: rank-one maps, `(f.smulRight A).toLinearMap₁₂ =
  (f : E →ₗ 𝕜).smulRight (A : F →ₛₗ G)`, also for a semilinear `A`.

The corresponding lemmas for the normed-space operations `flip` and `bilinearComp` live in
`TauCeti.Analysis.Normed.Operator.Bilinear`.
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

section SMulRight

variable {𝕜 𝕜₂ : Type*} [NormedField 𝕜] [NormedField 𝕜₂] {σ : 𝕜₂ →+* 𝕜} [RingHomSurjective σ]
  [RingHomIsometric σ]
  {E F G : Type*} [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul 𝕜 G]

/-- Forgetting continuity sends the rank-one map `(v, w) ↦ f v • A w` to the rank-one bilinear map
of the underlying maps. The second slot may be semilinear, as for the conjugate-linear slot of a
sesquilinear map. -/
@[simp]
theorem toLinearMap₁₂_smulRight (f : E →L[𝕜] 𝕜) (A : F →SL[σ] G) :
    toLinearMap₁₂ (f.smulRight A) = (f : E →ₗ[𝕜] 𝕜).smulRight (A : F →ₛₗ[σ] G) :=
  LinearMap.ext₂ fun _ _ ↦ by
    simp only [toLinearMap₁₂_apply_apply_apply, LinearMap.smulRight_apply, smulRight_apply,
      LinearMap.smul_apply, smul_apply, coe_coe]

end SMulRight

end ContinuousLinearMap
