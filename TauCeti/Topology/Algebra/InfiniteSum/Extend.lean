/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Fiber sums of injective maps

Summing along the fibers of an injective map extends a function by zero off the image.
This identifies fiber sums with `Function.extend`, allowing its measurability API to be used.
-/

public section

open Function Set

/-- A fiber sum along an injective map is the extension by zero of the summand. -/
theorem Function.Injective.tsum_fiber_eq_extend {α β M : Type*}
    [AddCommMonoid M] [TopologicalSpace M] {f : α → β} (hf : Injective f) (g : α → M)
    (y : β) : (∑' x : f ⁻¹' {y}, g x) = extend f g 0 y := by
  classical
  by_cases hy : ∃ x, f x = y
  · obtain ⟨x, rfl⟩ := hy
    rw [hf.extend_apply]
    exact tsum_eq_single (⟨x, rfl⟩ : f ⁻¹' {f x}) fun z hz ↦ by
      exfalso
      apply hz
      exact Subtype.ext (hf z.property)
  · rw [extend_apply' _ _ _ hy]
    have : IsEmpty (f ⁻¹' {y}) := ⟨fun x ↦ hy ⟨x, x.property⟩⟩
    exact tsum_empty
