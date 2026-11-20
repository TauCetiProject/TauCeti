/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Manifold.IsManifold.Pi

/-!
# Finite products of Lie groups

A finite product `∀ i, G i` of `C^n` Lie groups, with the product model with corners
`ModelWithCorners.pi I` and the product manifold structure `TauCeti.instIsManifoldPi`, is a `C^n`
Lie group: multiplication and inversion act coordinatewise, and a map into a finite product is
`C^n` exactly when each coordinate is (`contMDiff_pi_iff`). The additive versions cover tori such
as `ι → AddCircle p`.

## Main results

* `TauCeti.instContMDiffMulPi`, `TauCeti.instContMDiffAddPi`: a finite product of `C^n` monoids is
  a `C^n` monoid.
* `TauCeti.instLieGroupPi`, `TauCeti.instLieAddGroupPi`: a finite product of `C^n` Lie groups is a
  `C^n` Lie group.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Example 7.3(e)
  (products of Lie groups).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {H : ι → Type*} [∀ i, TopologicalSpace (H i)] {I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)}
  {G : ι → Type*} [∀ i, TopologicalSpace (G i)] [∀ i, ChartedSpace (H i) (G i)] {n : ℕ∞ω}

/-- A finite product of `C^n` monoids is a `C^n` monoid for the product model with corners. -/
@[to_additive /-- A finite product of `C^n` additive monoids is a `C^n` additive monoid for the
product model with corners. -/]
instance instContMDiffMulPi [∀ i, Mul (G i)] [∀ i, ContMDiffMul (I i) n (G i)] :
    ContMDiffMul (ModelWithCorners.pi I) n (∀ i, G i) where
  contMDiff_mul := contMDiff_pi_iff.2 fun i ↦ (contMDiff_mul (I i) n).comp
    ((contMDiff_apply.comp contMDiff_fst).prodMk (contMDiff_apply.comp contMDiff_snd))

/-- A finite product of `C^n` Lie groups is a `C^n` Lie group for the product model with
corners. -/
@[to_additive /-- A finite product of `C^n` additive Lie groups is a `C^n` additive Lie group for
the product model with corners. -/]
instance instLieGroupPi [∀ i, Group (G i)] [∀ i, LieGroup (I i) n (G i)] :
    LieGroup (ModelWithCorners.pi I) n (∀ i, G i) where
  contMDiff_inv := contMDiff_pi_iff.2 fun i ↦ (contMDiff_inv (I i) n).comp contMDiff_apply

end TauCeti
