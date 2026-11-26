/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import TauCeti.LinearAlgebra.Prod

/-!
# Coproducts of continuous linear maps and their surjectivity

For continuous linear maps `f₁ : M₁ →L[R] M` and `f₂ : M₂ →L[R] M`, the coproduct
`f₁.coprod f₂ : M₁ × M₂ →L[R] M`, `(x, y) ↦ f₁ x + f₂ y`, is surjective if and only if the ranges
of `f₁` and `f₂` span `M` (`f₁.range ⊔ f₂.range = ⊤`). Over a ring, when `M₂` is an additive
commutative group and `M` is a topological additive group, the same subspace-sum condition
characterizes surjectivity of `f₁.coprod (-f₂)`, `(x, y) ↦ f₁ x - f₂ y`, which is the linear
transversality condition for two maps with a common target. Extending a map by the zero map on a
second factor only sees the first component (`ContinuousLinearMap.coprod_zero_right`), so a right
inverse `g` of `f` pads to the right inverse `x ↦ (g x, 0)` of the extended map
(`ContinuousLinearMap.coprod_zero_comp_prod_zero`).

## Main results

* `ContinuousLinearMap.surjective_coprod_iff`: `Function.Surjective (f₁.coprod f₂)` is equivalent
  to `f₁.range ⊔ f₂.range = ⊤`.
* `ContinuousLinearMap.surjective_coprod_neg_iff`: `Function.Surjective (f₁.coprod (-f₂))` is
  equivalent to `f₁.range ⊔ f₂.range = ⊤`.
* `ContinuousLinearMap.coprod_zero_right`: `f.coprod 0 = f.comp (fst R M₁ M₂)`.
* `ContinuousLinearMap.coprod_zero_comp_prod_zero`: `(f.coprod 0).comp (g.prod 0) = f.comp g`.
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
  rw [← coe_coe, coe_coprod]
  exact LinearMap.surjective_coprod_iff _ _

/-- The coproduct of `f` with the zero map on a second factor is `f` composed with the first
projection. -/
theorem coprod_zero_right (f : M₁ →L[R] M) :
    f.coprod (0 : M₂ →L[R] M) = f.comp (fst R M₁ M₂) := by
  ext <;> simp

/-- Precomposing the coproduct of `f` with the zero map by `x ↦ (g x, 0)` gives `f ∘ g`. In
particular a right inverse `g` of `f` gives the right inverse `x ↦ (g x, 0)` of `f.coprod 0`. -/
theorem coprod_zero_comp_prod_zero {N : Type*} [TopologicalSpace N] [AddCommMonoid N]
    [Module R N] (f : M₁ →L[R] M) (g : N →L[R] M₁) :
    (f.coprod (0 : M₂ →L[R] M)).comp (g.prod 0) = f.comp g := by
  rw [coprod_zero_right, comp_assoc, fst_comp_prod]

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
  rw [← coe_coe, coe_coprod, toLinearMap_neg]
  exact LinearMap.surjective_coprod_neg_iff _ _

end Ring

end ContinuousLinearMap
