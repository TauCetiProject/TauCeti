/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ApproximateUnit

/-!
# Images of approximate units

The image of an approximate unit under a continuous surjective multiplicative map is again an
approximate unit, `Filter.IsApproximateUnit.map`. Surjectivity is what lets every element of the
target be written as an image, so that its products with the image filter converge. This is the
input for transferring approximate units, and quantities computed as their limits, from a
C⋆-algebra to its quotients.
-/

public section

open Filter Topology

namespace Filter.IsApproximateUnit

variable {α β F : Type*} [TopologicalSpace α] [Mul α] [TopologicalSpace β] [Mul β]
  [FunLike F α β] [MulHomClass F α β]

/-- The image of an approximate unit under a continuous surjective multiplicative map is an
approximate unit. -/
theorem map {l : Filter α} (hl : l.IsApproximateUnit) (f : F) (hf : Continuous f)
    (hf' : Function.Surjective f) : (l.map f).IsApproximateUnit where
  tendsto_mul_left m := by
    obtain ⟨a, rfl⟩ := hf' m
    simpa [tendsto_map'_iff, Function.comp_def, ← map_mul] using
      (hf.tendsto a).comp (hl.tendsto_mul_left a)
  tendsto_mul_right m := by
    obtain ⟨a, rfl⟩ := hf' m
    simpa [tendsto_map'_iff, Function.comp_def, ← map_mul] using
      (hf.tendsto a).comp (hl.tendsto_mul_right a)
  neBot := hl.neBot.map f

end Filter.IsApproximateUnit
