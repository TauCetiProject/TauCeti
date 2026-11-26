/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Star.Real
public import Mathlib.Topology.Instances.RealVectorSpace

/-!
# A continuous star operation commutes with real scalars

A continuous additive map between real topological vector spaces is `ℝ`-linear (Mathlib's
`map_real_smul`). Applied to the star operation `starAddEquiv`, this shows that a continuous
star on a real topological vector space makes it a `StarModule ℝ`, with no compatibility
between the star and the scalar action assumed.

## Main results

* `ContinuousStar.starModule_real`: a continuous star operation commutes with real scalars.
-/

public section

/-- **A continuous star operation is real-linear.** On a real topological vector space with a
continuous star operation, `star (r • x) = r • star x` for all real `r`: the star operation is a
continuous additive map, hence `ℝ`-linear. This is a theorem rather than an instance, to be
introduced locally where needed. -/
theorem ContinuousStar.starModule_real {E : Type*} [AddCommGroup E] [StarAddMonoid E]
    [Module ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E] [T2Space E] [ContinuousStar E] :
    StarModule ℝ E :=
  ⟨fun r x ↦ by simpa using map_real_smul (starAddEquiv (R := E)) continuous_star r x⟩
