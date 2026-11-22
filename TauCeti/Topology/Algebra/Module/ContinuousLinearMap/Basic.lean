/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Continuous linear maps as linear maps

A commutative square of continuous (semi)linear maps between topological modules is also a
commutative square of the underlying (semi)linear maps. This lets results about commuting squares
of linear maps, such as the module snake lemma, be applied to continuous linear maps.

A semilinear family `μ : M₁ →ₛₗ[σ₁₃] M₂ →SL[σ₂₃] M₃` of continuous semilinear maps becomes a
family of semilinear maps after composing with the coercion `ContinuousLinearMap.coeLMₛₗ`, and
then Mathlib's algebraic flip `LinearMap.flip` applies to it.

## Main results

* `ContinuousLinearMap.toLinearMap_comp_eq`: a commutative square of continuous semilinear maps
  commutes after coercion to semilinear maps.
* `LinearMap.flip_coeLMₛₗ_comp_apply`: evaluation of the algebraic flip of such a family `μ`,
  `((ContinuousLinearMap.coeLMₛₗ σ₂₃).comp μ).flip y x = μ x y`.
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

end ContinuousLinearMap

namespace LinearMap

variable {R₁ R₂ R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₃ : R₁ →+* R₃} {σ₂₃ : R₂ →+* R₃} {M₁ M₂ M₃ : Type*}
  [AddCommMonoid M₁] [Module R₁ M₁]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R₃ M₃] [ContinuousAdd M₃]
  [ContinuousConstSMul R₃ M₃] [SMulCommClass R₃ R₃ M₃]

/-- Evaluation of the algebraic flip of a semilinear family `μ` of continuous semilinear maps,
with each `μ x` viewed as a semilinear map through `ContinuousLinearMap.coeLMₛₗ`: it sends `y`
and then `x` to `μ x y`. -/
theorem flip_coeLMₛₗ_comp_apply (μ : M₁ →ₛₗ[σ₁₃] M₂ →SL[σ₂₃] M₃) (y : M₂) (x : M₁) :
    ((ContinuousLinearMap.coeLMₛₗ σ₂₃).comp μ).flip y x = μ x y := by
  rw [flip_apply, comp_apply, ContinuousLinearMap.coeLMₛₗ_apply, ContinuousLinearMap.coe_coe]

end LinearMap
