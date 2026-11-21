/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Fiber products and sums of injective maps

Multiplying (resp. summing) along the fibers of an injective map extends a function by one
(resp. zero) off the image. This identifies fiber products and sums with `Function.extend`,
allowing its measurability API to be used. Also provides `tprod_subtype_ite` / `tsum_subtype_ite`
for restricting a subtype infinite product or sum by a predicate guard.
-/

public section

open Function Set

/-- A fiber product along an injective map is the extension by one of the factor. -/
@[to_additive /-- A fiber sum along an injective map is the extension by zero of the summand. -/]
theorem Function.Injective.tprod_fiber_eq_extend {α β M : Type*}
    [CommMonoid M] [TopologicalSpace M] {f : α → β} (hf : Injective f) (g : α → M)
    (y : β) : (∏' x : f ⁻¹' {y}, g x) = extend f g 1 y := by
  classical
  by_cases hy : ∃ x, f x = y
  · obtain ⟨x, rfl⟩ := hy
    rw [hf.extend_apply]
    exact tprod_eq_mulSingle (⟨x, rfl⟩ : f ⁻¹' {f x}) fun z hz ↦
      (hz <| Subtype.ext <| hf z.property).elim
  · rw [extend_apply' _ _ _ hy]
    have : IsEmpty (f ⁻¹' {y}) := ⟨fun x ↦ hy ⟨x, x.property⟩⟩
    exact tprod_empty

/-- Restricting a `tprod` over a set `s` by an `if` guard equals the `tprod` over `{x ∈ s | p x}`.
-/
@[to_additive /-- Restricting a `tsum` over a set `s` by an `if` guard equals the `tsum` over
`{x ∈ s | p x}`. -/]
theorem tprod_subtype_ite {α M : Type*} [CommMonoid M] [TopologicalSpace M]
    (s : Set α) (p : α → Prop) [DecidablePred p] (f : α → M) :
    (∏' x : s, if p x.val then f x.val else 1) = ∏' x : {x ∈ s | p x}, f x.val := by
  classical
  rw [tprod_subtype s (fun x ↦ if p x then f x else 1), tprod_subtype {x ∈ s | p x} f]
  refine tprod_congr fun x ↦ ?_
  by_cases hs : x ∈ s <;> by_cases hp : p x <;> simp [Set.mulIndicator, hs, hp]
