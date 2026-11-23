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
`ModelWithCorners.pi I`, is a `C^n` Lie group: multiplication and inversion are computed
coordinatewise, and a map into the product is `C^n` exactly when its coordinates are
(Mathlib's `contMDiff_pi_iff`). This is the finite-product analogue of Mathlib's `LieGroup.prod`.
For instance the torus `(ℝ / pℤ)^ι` is an additive Lie group.
-/

public section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {H : ι → Type*} [∀ i, TopologicalSpace (H i)] {I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)}
  {G : ι → Type*} [∀ i, TopologicalSpace (G i)] [∀ i, ChartedSpace (H i) (G i)]
  {n : WithTop ℕ∞}

/-- A finite product of manifolds with `C^n` multiplication has `C^n` multiplication. -/
@[to_additive /-- A finite product of manifolds with `C^n` addition has `C^n` addition. -/]
instance Pi.contMDiffMul [∀ i, Mul (G i)] [∀ i, ContMDiffMul (I i) n (G i)] :
    ContMDiffMul (ModelWithCorners.pi I) n (∀ i, G i) where
  contMDiff_mul := by
    refine contMDiff_pi_iff.2 fun i ↦ ?_
    exact (contMDiff_apply.comp contMDiff_fst).mul (contMDiff_apply.comp contMDiff_snd)

/-- **A finite product of Lie groups is a Lie group.** -/
@[to_additive /-- **A finite product of additive Lie groups is an additive Lie group.** -/]
instance Pi.lieGroup [∀ i, Group (G i)] [∀ i, LieGroup (I i) n (G i)] :
    LieGroup (ModelWithCorners.pi I) n (∀ i, G i) where
  contMDiff_inv := by
    refine contMDiff_pi_iff.2 fun i ↦ ?_
    exact (contMDiff_apply (Ii := I) (Mi := G) (i := i)).inv
