/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Surjectivity of coproducts of continuous linear maps

For continuous linear maps `f₁ : M₁ →L[R] M` and `f₂ : M₂ →L[R] M`, the coproduct
`f₁.coprod f₂ : M₁ × M₂ →L[R] M`, `(x, y) ↦ f₁ x + f₂ y`, is surjective if and only if the ranges
of `f₁` and `f₂` span `M` (`f₁.range ⊔ f₂.range = ⊤`). Over a ring, when `M₂` is an additive
commutative group and `M` is a topological additive group, the same subspace-sum condition
characterizes surjectivity of `f₁.coprod (-f₂)`, `(x, y) ↦ f₁ x - f₂ y`, which is the linear
transversality condition for two maps with a common target.

## Main results

* `ContinuousLinearMap.surjective_coprod_iff`: `Function.Surjective (f₁.coprod f₂)` is equivalent
  to `f₁.range ⊔ f₂.range = ⊤`.
* `ContinuousLinearMap.surjective_coprod_neg_iff`: `Function.Surjective (f₁.coprod (-f₂))` is
  equivalent to `f₁.range ⊔ f₂.range = ⊤`.
-/

public section

namespace ContinuousLinearMap

section Semiring

variable {R M M₁ M₂ : Type*} [Semiring R]
  [TopologicalSpace M] [TopologicalSpace M₁] [TopologicalSpace M₂]
  [AddCommMonoid M] [Module R M] [ContinuousAdd M]
  [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- The coproduct `(x, y) ↦ f₁ x + f₂ y` of two continuous linear maps is surjective if and only
if their ranges together span the codomain. -/
theorem surjective_coprod_iff (f₁ : M₁ →L[R] M) (f₂ : M₂ →L[R] M) :
    Function.Surjective (f₁.coprod f₂) ↔ f₁.range ⊔ f₂.range = ⊤ := by
  rw [← coe_coe, ← LinearMap.range_eq_top, range_coprod]

end Semiring

section Ring

variable {R M M₁ M₂ : Type*} [Ring R]
  [TopologicalSpace M] [TopologicalSpace M₁] [TopologicalSpace M₂]
  [AddCommGroup M] [Module R M] [IsTopologicalAddGroup M]
  [AddCommMonoid M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- The difference coproduct `(x, y) ↦ f₁ x - f₂ y` of two continuous linear maps is surjective if
and only if their ranges together span the codomain. -/
theorem surjective_coprod_neg_iff (f₁ : M₁ →L[R] M) (f₂ : M₂ →L[R] M) :
    Function.Surjective (f₁.coprod (-f₂)) ↔ f₁.range ⊔ f₂.range = ⊤ := by
  rw [surjective_coprod_iff, toLinearMap_neg, LinearMap.range_neg]

end Ring

end ContinuousLinearMap
