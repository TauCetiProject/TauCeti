/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Basic.Real.Star
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Real scalar compatibility of a continuous involution

A continuous additive involution on a Hausdorff real topological vector space commutes
with real scalar multiplication. The named theorem `StarModule.real_of_continuousStar`
supplies this compatibility without installing a global instance. It can be enabled locally
with `attribute [local instance] StarModule.real_of_continuousStar`.

## References

* Mathlib, `map_real_smul` in `Mathlib.Topology.Instances.RealVectorSpace`: continuous
  additive maps between real topological vector spaces are real-linear.
-/

public section

/-- A continuous additive star on a Hausdorff real topological vector space commutes
with real scalar multiplication. This theorem can be enabled as a local instance. -/
theorem StarModule.real_of_continuousStar (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousSMul ℝ E] [T2Space E] [StarAddMonoid E]
    [ContinuousStar E] : StarModule ℝ E :=
  ⟨fun r x ↦ map_real_smul (starAddEquiv (R := E)) continuous_star r x⟩
