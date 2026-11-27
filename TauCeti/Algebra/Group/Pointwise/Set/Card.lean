/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Set.Card

/-!
# Overlaps of translates of a set along a homomorphism

Let `φ : I → G` be a homomorphism of groups, `G` commutative, and `K ⊆ G`. A point `y` lies in the
translate `φ i * K` for at most `#φ⁻¹(K⁻¹ * K)` indices `i`
(`Set.encard_setOf_div_mem_le`): if `y` lies in `φ i₀ * K`, then `i ↦ i / i₀` maps those indices
injectively into `φ⁻¹(K⁻¹ * K)`. This is the counting step of amalgam (Wiener-type) bounds, where
the translates of a compact neighbourhood of `0` by a discrete set of points overlap boundedly.

## Main results

* `Set.encard_setOf_div_mem_le`, and its additive version `Set.encard_setOf_sub_mem_le`.

## Provenance

Extracted from the proof of `New.Heisenberg.IsVacuum.wiener_bound` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Weil/Construction/WeilOperators.lean`.
-/

public section

open scoped Pointwise

namespace Set

variable {I G : Type*} [Group I] [CommGroup G]

/-- A point `y` lies in at most `#φ⁻¹(K⁻¹ * K)` of the translates `φ i * K`. -/
@[to_additive /-- A point `y` lies in at most `#φ⁻¹(-K + K)` of the translates `φ i + K`. -/]
theorem encard_setOf_div_mem_le (φ : I →* G) (K : Set G) (y : G) :
    {i : I | y / φ i ∈ K}.encard ≤ (φ ⁻¹' (K⁻¹ * K)).encard := by
  obtain h_empty | ⟨i₀, hi₀⟩ := {i : I | y / φ i ∈ K}.eq_empty_or_nonempty
  · simp [h_empty]
  · have h_mem (i : I) (hi : y / φ i ∈ K) : φ (i / i₀) ∈ K⁻¹ * K := by
      refine ⟨(y / φ i)⁻¹, inv_mem_inv.2 hi, y / φ i₀, hi₀, ?_⟩
      simp only [map_div, inv_div, div_mul_div_cancel]
    exact encard_le_encard_of_injOn (f := (· / i₀)) h_mem div_left_injective.injOn

end Set
