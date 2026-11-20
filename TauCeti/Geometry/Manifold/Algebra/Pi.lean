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

A finite product `∀ i, G i` of Lie groups, charted by Mathlib's product charts `piChartedSpace`
on the product model `ModelWithCorners.pi I`, is a Lie group: multiplication and inversion act
coordinatewise, and a map into a finite product is `C^n` exactly when every coordinate is
(`contMDiff_pi_iff`). This is the finite-product analogue of Mathlib's `Prod.instLieGroup`. In
particular a torus `ι → AddCircle p` is an additive Lie group.

## Main declarations

* `Pi.contMDiffMul`, `Pi.contMDiffAdd`: a finite product of `C^n` monoids is a `C^n` monoid.
* `Pi.lieGroup`, `Pi.lieAddGroup`: a finite product of Lie groups is a Lie group.
-/

public section

open scoped Manifold ContDiff

namespace Pi

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞} {ι : Type*} [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {H : ι → Type*} [∀ i, TopologicalSpace (H i)] {I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)}
  {G : ι → Type*} [∀ i, TopologicalSpace (G i)] [∀ i, ChartedSpace (H i) (G i)]

/-- A finite product of `C^n` monoids is a `C^n` monoid for the product model. -/
@[to_additive /-- A finite product of `C^n` additive monoids is a `C^n` additive monoid for the
product model. -/]
instance contMDiffMul [∀ i, Mul (G i)] [∀ i, ContMDiffMul (I i) n (G i)] :
    ContMDiffMul (ModelWithCorners.pi I) n (∀ i, G i) where
  contMDiff_mul := contMDiff_pi_iff.2 fun i ↦
    (contMDiff_mul (I i) n).comp
      ((contMDiff_apply.comp contMDiff_fst).prodMk (contMDiff_apply.comp contMDiff_snd))

/-- A finite product of Lie groups is a Lie group for the product model. -/
@[to_additive /-- A finite product of additive Lie groups is an additive Lie group for the product
model. -/]
instance lieGroup [∀ i, Group (G i)] [∀ i, LieGroup (I i) n (G i)] :
    LieGroup (ModelWithCorners.pi I) n (∀ i, G i) where
  contMDiff_inv := contMDiff_pi_iff.2 fun i ↦ (contMDiff_inv (I i) n).comp contMDiff_apply

end Pi
