/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# Composition of semilinear maps with finite sums

Composition of semilinear maps distributes on both sides over finite sums
(`LinearMap.comp_finsetSum` and `LinearMap.finsetSum_comp`), extending `LinearMap.comp_add` and
`LinearMap.add_comp` and mirroring `ContinuousLinearMap.comp_finsetSum` and
`ContinuousLinearMap.finsetSum_comp`.
-/

public section

namespace LinearMap

variable {ι R₁ R₂ R₃ M₁ M₂ M₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- Postcomposition with a semilinear map distributes over a finite sum. -/
theorem comp_finsetSum {s : Finset ι} (g : M₂ →ₛₗ[σ₂₃] M₃) (f : ι → M₁ →ₛₗ[σ₁₂] M₂) :
    (g.comp (∑ i ∈ s, f i) : M₁ →ₛₗ[σ₁₃] M₃) = ∑ i ∈ s, g.comp (f i) :=
  ext fun _ => by simp only [comp_apply, LinearMap.sum_apply, map_sum]

/-- Precomposition with a semilinear map distributes over a finite sum. -/
theorem finsetSum_comp {s : Finset ι} (g : ι → M₂ →ₛₗ[σ₂₃] M₃) (f : M₁ →ₛₗ[σ₁₂] M₂) :
    ((∑ i ∈ s, g i).comp f : M₁ →ₛₗ[σ₁₃] M₃) = ∑ i ∈ s, (g i).comp f :=
  ext fun _ => by simp only [comp_apply, LinearMap.sum_apply]

end LinearMap
