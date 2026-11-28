/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered

/-!
# Cardinal filtered preorders

For a regular cardinal `κ`, a preorder `J` is a `κ`-filtered category exactly when every subset
of `J` with fewer than `κ` elements is bounded above
(`CategoryTheory.isCardinalFiltered_preorder_iff`): a cocone on a diagram in `J` is an upper bound
of its objects. This complements Mathlib's
`CategoryTheory.isCardinalFiltered_preorder`, which gives one direction for preorders in the
universe of `κ`; it is the comparison through which `κ`-filtered simplicial sets and `κ`-filtered
colimits in nerves of preorders are compared with Mathlib's `κ`-filtered categories.

## References

* J. Adámek and J. Rosický, *Locally presentable and accessible categories*, Chapter 1.
-/

public section

universe w u

namespace CategoryTheory

/-- For a regular cardinal `κ`, a preorder is `κ`-filtered exactly when every subset with fewer
than `κ` elements is bounded above. -/
lemma isCardinalFiltered_preorder_iff (J : Type u) [Preorder J] (κ : Cardinal.{w})
    [Fact κ.IsRegular] :
    IsCardinalFiltered J κ ↔ ∀ s : Set J, HasCardinalLT s κ → BddAbove s := by
  refine ⟨fun _ s hs ↦ ⟨IsCardinalFiltered.max (fun x : s ↦ x.val) hs, fun x hx ↦
    (IsCardinalFiltered.toMax (fun x : s ↦ x.val) hs ⟨x, hx⟩).le⟩, fun h ↦ ⟨fun {A _} F hA ↦ ?_⟩⟩
  -- The objects of a diagram with fewer than `κ` arrows form a set with fewer than `κ` elements.
  obtain ⟨j, hj⟩ := h (Set.range F.obj)
    ((hasCardinalLT_of_hasCardinalLT_arrow hA).of_surjective _ Set.rangeFactorization_surjective)
  exact ⟨Preorder.coconeOfUpperBound F hj⟩

end CategoryTheory
