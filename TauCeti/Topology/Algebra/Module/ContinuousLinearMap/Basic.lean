/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Basic facts about continuous linear maps

A commutative square of continuous (semi)linear maps between topological modules is also a
commutative square of the underlying (semi)linear maps. This lets results about commuting squares
of linear maps, such as the module snake lemma, be applied to continuous linear maps.

A continuous linear map out of `κ → R`, with `κ` finite, is determined by its values on the
coordinate vectors `Pi.single k 1`.

## Main results

* `ContinuousLinearMap.toLinearMap_comp_eq`: a commutative square of continuous semilinear maps
  commutes after coercion to semilinear maps.
* `ContinuousLinearMap.surjective_iff_ne_zero`: a continuous linear functional is surjective
  exactly when it is nonzero.
* `ContinuousLinearMap.pi_ext_single_one`: a continuous linear map out of `κ → R`, `κ` finite, is
  determined by its values on the coordinate vectors.
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

/-- A continuous linear functional with values in a division semiring is surjective exactly when
it is nonzero. -/
theorem surjective_iff_ne_zero {R M : Type*} [DivisionSemiring R] [TopologicalSpace R]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M] {f : M →L[R] R} :
    Function.Surjective f ↔ f ≠ 0 :=
  LinearMap.surjective_iff_ne_zero.trans (not_congr (coe_inj (g := 0)))

/-- A continuous linear map out of `κ → R`, with `κ` finite, is determined by its values on the
coordinate vectors `Pi.single k 1`. -/
theorem pi_ext_single_one {R M κ : Type*} [Semiring R] [TopologicalSpace R] [TopologicalSpace M]
    [AddCommMonoid M] [Module R M] [Finite κ] [DecidableEq κ] {f g : (κ → R) →L[R] M}
    (h : ∀ k, f (Pi.single k 1) = g (Pi.single k 1)) : f = g :=
  coe_injective <| LinearMap.pi_ext' fun k ↦ LinearMap.ext_ring <| h k

end ContinuousLinearMap
