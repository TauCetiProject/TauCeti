/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Algebra.Ring.Defs

/-!
# Scaling one coordinate of a power of a topological ring

For a topological ring `R`, an index `x₀ : X` and a scalar `u : R`,
`ContinuousMonoidHom.scaleCoord x₀ u` is the diagonal endomorphism of the additive group `X → R`,
viewed as the multiplicative group `Multiplicative (X → R)`, that multiplies the coordinate at `x₀`
by `u` and leaves every other coordinate unchanged, as a continuous homomorphism.

## Main definitions

* `ContinuousMonoidHom.scaleCoord`: the coordinate-scaling continuous homomorphism.
* `ContinuousMonoidHom.toAdd_scaleCoord_apply`, `ContinuousMonoidHom.toAdd_scaleCoord`: its
  coordinates, as a conditional and as a `Function.update`.
-/

@[expose] public section

namespace ContinuousMonoidHom

variable {X R : Type*} [DecidableEq X] [TopologicalSpace R] [NonUnitalNonAssocSemiring R]
  [ContinuousMul R] (x₀ : X) (u : R)

/-- **Scaling one coordinate.** The continuous homomorphism of `Multiplicative (X → R)` that
multiplies the coordinate at `x₀` by `u` and fixes every other coordinate. -/
def scaleCoord : Multiplicative (X → R) →ₜ* Multiplicative (X → R) where
  toFun a := Multiplicative.ofAdd fun k ↦ if k = x₀ then u * a.toAdd k else a.toAdd k
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext k
    simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext k
    by_cases hk : k = x₀ <;> simp [hk, mul_add]
  continuous_toFun := continuous_ofAdd.comp <| continuous_pi fun k ↦ by
    by_cases hk : k = x₀
    · simp only [hk, ↓reduceIte]
      exact continuous_const.mul ((continuous_apply x₀).comp continuous_toAdd)
    · simp only [hk, ↓reduceIte]
      exact (continuous_apply k).comp continuous_toAdd

/-- The coordinate at `k` of the image under `scaleCoord x₀ u` is `u` times the coordinate of the
argument if `k = x₀`, and the coordinate of the argument otherwise. -/
theorem toAdd_scaleCoord_apply (a : Multiplicative (X → R)) (k : X) :
    (scaleCoord x₀ u a).toAdd k = if k = x₀ then u * a.toAdd k else a.toAdd k :=
  rfl

/-- `scaleCoord x₀ u` replaces the coordinate at `x₀` by `u` times it. -/
theorem toAdd_scaleCoord (a : Multiplicative (X → R)) :
    (scaleCoord x₀ u a).toAdd = Function.update a.toAdd x₀ (u * a.toAdd x₀) := by
  funext k
  by_cases hk : k = x₀
  · subst hk
    simp [toAdd_scaleCoord_apply]
  · simp [toAdd_scaleCoord_apply, hk]

end ContinuousMonoidHom
