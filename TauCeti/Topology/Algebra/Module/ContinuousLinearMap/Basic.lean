/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Basic facts about continuous linear maps

A commutative square of continuous (semi)linear maps between topological modules is also a
commutative square of the underlying (semi)linear maps. This lets results about commuting squares
of linear maps, such as the module snake lemma, be applied to continuous linear maps.

Precomposing with a continuous linear equivalence does not change whether a continuous linear map
vanishes.

## Main results

* `ContinuousLinearMap.toLinearMap_comp_eq`: a commutative square of continuous semilinear maps
  commutes after coercion to semilinear maps.
* `ContinuousLinearMap.comp_continuousLinearEquiv_eq_zero_iff`: `L ∘ e = 0` exactly when `L = 0`,
  for a continuous semilinear equivalence `e`.
* `ContinuousLinearMap.surjective_iff_ne_zero`: a continuous linear functional is surjective
  exactly when it is nonzero.
-/

public section

namespace ContinuousLinearMap

variable {R₁ R₂ R₃ R₄ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃] [Semiring R₄]
  {σ₁₂ : R₁ →+* R₂} {σ₁₃ : R₁ →+* R₃} {σ₂₄ : R₂ →+* R₄} {σ₃₄ : R₃ →+* R₄} {σ₁₄ : R₁ →+* R₄}
  [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]
  {M₁ M₂ M₃ M₄ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R₃ M₃]
  [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₄ M₄]

/-- A commutative square of continuous semilinear maps commutes as a square of semilinear
maps. -/
theorem toLinearMap_comp_eq {f : M₁ →SL[σ₁₂] M₂} {g : M₃ →SL[σ₃₄] M₄} {i : M₁ →SL[σ₁₃] M₃}
    {i' : M₂ →SL[σ₂₄] M₄} (h : g ∘SL i = i' ∘SL f) :
    (g : M₃ →ₛₗ[σ₃₄] M₄) ∘ₛₗ (i : M₁ →ₛₗ[σ₁₃] M₃) =
      (i' : M₂ →ₛₗ[σ₂₄] M₄) ∘ₛₗ (f : M₁ →ₛₗ[σ₁₂] M₂) := by
  rw [← toLinearMap_comp, h, toLinearMap_comp]

/-- Precomposing with a continuous semilinear equivalence gives the zero map exactly when the
original map is zero. -/
theorem comp_continuousLinearEquiv_eq_zero_iff {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁]
    [RingHomInvPair σ₂₁ σ₁₂] (L : M₂ →SL[σ₂₄] M₄)
    (e : M₁ ≃SL[σ₁₂] M₂) : L.comp (e : M₁ →SL[σ₁₂] M₂) = 0 ↔ L = 0 := by
  refine ⟨fun h ↦ ext fun v ↦ ?_, fun h ↦ by rw [h, zero_comp]⟩
  simpa using congr($h (e.symm v))

/-- A continuous linear functional with values in a division semiring is surjective exactly when
it is nonzero. -/
theorem surjective_iff_ne_zero {R M : Type*} [DivisionSemiring R] [TopologicalSpace R]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M] {f : M →L[R] R} :
    Function.Surjective f ↔ f ≠ 0 :=
  LinearMap.surjective_iff_ne_zero.trans (not_congr (coe_inj (g := 0)))

end ContinuousLinearMap
