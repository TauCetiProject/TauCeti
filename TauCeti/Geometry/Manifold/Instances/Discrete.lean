/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Discrete Lie groups

A discrete group is a Lie group over a trivial normed model, with the canonical discrete
charts. The differentiability order is arbitrary, over any nontrivially normed scalar field.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Example 7.3(m).
-/

public section

open scoped ContDiff Manifold

variable {𝕜 E D : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Unique E]
  [Group D] [TopologicalSpace D] [DiscreteTopology D]

attribute [local instance] ChartedSpace.ofDiscreteTopology

/-- A discrete group with its canonical charts over a trivial model is a Lie group. -/
@[to_additive /-- A discrete additive group with its canonical charts over a trivial model
is an additive Lie group. -/]
theorem LieGroup.of_discreteTopology (n : ℕ∞ω) : LieGroup 𝓘(𝕜, E) n D where
  toContMDiffMul :=
    { toIsManifold := IsManifold.of_discreteTopology n
      contMDiff_mul := contMDiff_of_discreteTopology }
  contMDiff_inv := contMDiff_of_discreteTopology
