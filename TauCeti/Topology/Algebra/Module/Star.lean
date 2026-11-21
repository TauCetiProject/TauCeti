/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.Module
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Star

/-!
# Continuity of `star` in finite dimension

On a finite-dimensional Hausdorff topological vector space `E` over a complete nontrivially normed
star field `𝕜` with continuous `star`, every `star` operation compatible with the scalar action
(`StarModule 𝕜 E`) is continuous: `FiniteDimensional.continuousStar`. Indeed, in a basis `b`,
`star x = ∑ i, star (b.repr x i) • star (b i)`, and the coordinates are continuous. For instance
coordinatewise conjugation on a finite-dimensional complex space is continuous.
-/

public section

/-- On a finite-dimensional Hausdorff topological vector space, a `star` operation compatible
with the scalar action is continuous. -/
theorem FiniteDimensional.continuousStar (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [StarRing 𝕜] [ContinuousStar 𝕜] [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T2Space E]
    [FiniteDimensional 𝕜 E] [StarAddMonoid E] [StarModule 𝕜 E] : ContinuousStar E := by
  let b := Module.finBasis 𝕜 E
  have h (x : E) : star x = ∑ i, star (b.repr x i) • star (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [star_sum, star_smul]
  exact ⟨(continuous_finsetSum _ fun i _ ↦
    ((b.coord i).continuous_of_finiteDimensional.star).smul continuous_const).congr
      fun x ↦ (h x).symm⟩
