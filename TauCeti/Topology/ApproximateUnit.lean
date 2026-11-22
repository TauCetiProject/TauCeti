/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Topology.Algebra.Star
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
C⋆-algebra to its quotients. Likewise, pushing a filter forward along a continuous
anti-multiplicative involution `star` swaps left and right multiplication and therefore preserves
approximate units in both directions (`Filter.IsApproximateUnit.map_star` and
`Filter.IsApproximateUnit.map_star_iff`).

In a Hausdorff space, a one-sided approximate unit forces the corresponding annihilator to
vanish: `TauCeti.faithfulSMul_of_tendsto_mul_left` (if `x * c = y * c` for every `c`, then
`x = y`) and `TauCeti.faithfulSMul_mulOpposite_of_tendsto_mul_right` (if `c * x = c * y` for
every `c`, then `x = y`). This nondegeneracy is what makes double centralizers of an algebra with
an approximate unit behave like multipliers.

Taking adjoints along a filter of self-adjoint elements turns a right approximate unit for `z`
into a left approximate unit for `star z`, `TauCeti.tendsto_mul_star_of_tendsto_mul`.
-/

public section

open Filter Topology

namespace Filter.IsApproximateUnit

section

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

end

/-- Pushing an approximate unit forward along a continuous anti-multiplicative involution `star`
yields an approximate unit. -/
theorem map_star {α : Type*} [TopologicalSpace α] [Mul α] [StarMul α] [ContinuousStar α]
    {l : Filter α} (hl : l.IsApproximateUnit) : (l.map star).IsApproximateUnit where
  tendsto_mul_left a := by
    rw [tendsto_map'_iff]
    simpa [Function.comp_def, star_mul, star_star] using
      (hl.tendsto_mul_right (star a)).star
  tendsto_mul_right a := by
    rw [tendsto_map'_iff]
    simpa [Function.comp_def, star_mul, star_star] using
      (hl.tendsto_mul_left (star a)).star
  neBot := hl.neBot.map star

/-- Pushing a filter forward along a continuous anti-multiplicative involution `star` preserves
approximate units in both directions. -/
@[simp]
theorem map_star_iff {α : Type*} [TopologicalSpace α] [Mul α] [StarMul α] [ContinuousStar α]
    {l : Filter α} : (l.map star).IsApproximateUnit ↔ l.IsApproximateUnit :=
  ⟨fun h => by simpa [Filter.map_map, Function.comp_def, star_star] using h.map_star,
    fun h => h.map_star⟩

end Filter.IsApproximateUnit

namespace TauCeti

variable {α : Type*} [TopologicalSpace α] [Mul α] [T2Space α] {l : Filter α} [l.NeBot]

/-- If `a * e → a` along a proper filter for every `a`, in a Hausdorff space, an element is
determined by its products on the right: the action of `α` on itself by left multiplication is
faithful. This applies to every approximate unit, via
`Filter.IsApproximateUnit.tendsto_mul_left`. -/
theorem faithfulSMul_of_tendsto_mul_left (hl : ∀ a, Tendsto (a * ·) l (𝓝 a)) :
    FaithfulSMul α α where
  eq_of_smul_eq_smul {x y} h := by
    have hxy : (x * ·) = (y * ·) := funext fun c => by simpa only [smul_eq_mul] using h c
    exact tendsto_nhds_unique (hl x) (hxy ▸ hl y)

/-- If `e * a → a` along a proper filter for every `a`, in a Hausdorff space, an element is
determined by its products on the left: the action of `αᵐᵒᵖ` on `α` by right multiplication is
faithful. This applies to every approximate unit, via
`Filter.IsApproximateUnit.tendsto_mul_right`. -/
theorem faithfulSMul_mulOpposite_of_tendsto_mul_right (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) :
    FaithfulSMul αᵐᵒᵖ α where
  eq_of_smul_eq_smul {x y} h := by
    have hxy : (· * x.unop) = (· * y.unop) := funext fun c => by
      simpa only [MulOpposite.smul_eq_mul_unop] using h c
    exact MulOpposite.unop_injective <| tendsto_nhds_unique (hl x.unop) (hxy ▸ hl y.unop)

/-- Along a filter of self-adjoint elements, `z * e → z` implies `e * star z → star z`. -/
theorem tendsto_mul_star_of_tendsto_mul {R : Type*} [Mul R] [StarMul R] [TopologicalSpace R]
    [ContinuousStar R] {l : Filter R} {z : R} (he : ∀ᶠ e in l, IsSelfAdjoint e)
    (hz : Tendsto (z * ·) l (𝓝 z)) : Tendsto (· * star z) l (𝓝 (star z)) :=
  hz.star.congr' (he.mono fun _ he ↦ by rw [star_mul, he.star_eq])

end TauCeti
