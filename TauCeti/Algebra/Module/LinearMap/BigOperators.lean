/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# Composition with a finite sum of linear maps

Composition of linear maps is additive in each argument, so it distributes over finite sums:
`(∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g` and `g ∘ₗ ∑ i ∈ s, f i = ∑ i ∈ s, g ∘ₗ f i`.

## Main results

* `LinearMap.finsetSum_comp`: composition on the right distributes over a finite sum.
* `LinearMap.comp_finsetSum`: composition on the left distributes over a finite sum.
-/

public section

namespace LinearMap

variable {R M N P ι : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P]

/-- Composition on the right distributes over a finite sum of linear maps. -/
theorem finsetSum_comp (s : Finset ι) (f : ι → N →ₗ[R] P) (g : M →ₗ[R] N) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g :=
  LinearMap.ext fun x ↦ by simp only [comp_apply, LinearMap.sum_apply]

/-- Composition on the left distributes over a finite sum of linear maps. -/
theorem comp_finsetSum (s : Finset ι) (f : ι → M →ₗ[R] N) (g : N →ₗ[R] P) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i :=
  LinearMap.ext fun x ↦ by simp only [comp_apply, LinearMap.sum_apply, map_sum]

end LinearMap
