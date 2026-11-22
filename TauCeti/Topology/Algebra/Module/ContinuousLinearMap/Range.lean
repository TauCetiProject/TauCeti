/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Restricting operators to a range

Equality after restriction to the range of a continuous linear map is equivalent to equality
after precomposition with that map. This identifies derivatives on parametrized tangent planes.
For an injective continuous linear map, `ContinuousLinearMap.coe_ofInjective_eq_rangeRestrict`
identifies the coercion of `LinearEquiv.ofInjective` with `ContinuousLinearMap.rangeRestrict`.
-/

public section

namespace ContinuousLinearMap

/-- Two operators agree on the range of `T` exactly when their composites with `T` agree. -/
theorem comp_subtypeL_range_eq_iff
    {R₁ R₂ R₃ E G F : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
    {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}
    [RingHomSurjective σ₁₂] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
    [TopologicalSpace E] [AddCommMonoid E] [Module R₁ E]
    [TopologicalSpace G] [AddCommMonoid G] [Module R₂ G]
    [TopologicalSpace F] [AddCommMonoid F] [Module R₃ F]
    (T : E →SL[σ₁₂] G) (M₁ M₂ : G →SL[σ₂₃] F) :
    M₁.comp T.range.subtypeL = M₂.comp T.range.subtypeL ↔ M₁.comp T = M₂.comp T := by
  constructor
  · intro h
    simpa only [comp_assoc, subtypeL_comp_codRestrict] using congrArg (·.comp T.rangeRestrict) h
  · intro h
    ext v
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp v.property
    rw [coe_coe] at hx
    simpa only [comp_apply, Submodule.subtypeL_apply, ← hx] using congrArg (· x) h

/-- The coercion of `LinearEquiv.ofInjective f.toLinearMap hinj` agrees with `f.rangeRestrict`. -/
theorem coe_ofInjective_eq_rangeRestrict {R E F : Type*} [Semiring R]
    [AddCommMonoid E] [TopologicalSpace E] [Module R E]
    [AddCommMonoid F] [TopologicalSpace F] [Module R F]
    (f : E →L[R] F) (hinj : Function.Injective f) :
    ⇑(LinearEquiv.ofInjective f.toLinearMap hinj) = f.rangeRestrict := by
  ext x
  rw [LinearEquiv.ofInjective_apply, coe_codRestrict_apply, coe_coe]

end ContinuousLinearMap
