/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ApproximateUnit

/-!
# Approximate units: images and products

An approximate unit is a proper filter along which the left and the right multiplications by
each element converge to it; `Filter.IsApproximateUnit.iff_neBot_and_tendsto_prod` packages the
two convergences as a single one in the product `α × α`.

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

/-- A filter is an approximate unit iff it is proper and, for every `a`, the pair of products
`(e * a, a * e)` tends to `(a, a)` along it. -/
theorem iff_neBot_and_tendsto_prod {l : Filter α} :
    l.IsApproximateUnit ↔ l.NeBot ∧ ∀ a, Tendsto (fun e ↦ (e * a, a * e)) l (𝓝 (a, a)) := by
  simp only [nhds_prod_eq, tendsto_prod_iff']
  exact ⟨fun h ↦ ⟨h.neBot, fun a ↦ ⟨h.tendsto_mul_right a, h.tendsto_mul_left a⟩⟩,
    fun ⟨_, h⟩ ↦ ⟨fun a ↦ (h a).2, fun a ↦ (h a).1⟩⟩

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
