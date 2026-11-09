/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Function

/-!
# Injectivity on a union, and involutions mapping a set into itself

* `Set.InjOn.union_of_disjoint_image`: a map injective on two sets with disjoint images is
  injective on their union.
* `Set.MapsTo.image_eq_of_involutive` and `Set.MapsTo.preimage_eq_of_involutive`: an involution
  mapping a set into itself maps it onto itself, and the set is its own preimage.
-/

public section

namespace Set

variable {α β : Type*} {f : α → β} {s t : Set α}

/-- A map injective on two sets whose images are disjoint is injective on their union. -/
theorem InjOn.union_of_disjoint_image (hs : InjOn f s) (ht : InjOn f t)
    (h : Disjoint (f '' s) (f '' t)) : InjOn f (s ∪ t) :=
  (injOn_union h.of_image).2 ⟨hs, ht, fun _ hx _ hy hxy ↦
    disjoint_left.1 h (mem_image_of_mem f hx) (hxy ▸ mem_image_of_mem f hy)⟩

/-- An involution mapping a set into itself maps it onto itself. -/
theorem MapsTo.image_eq_of_involutive {f : α → α} {s : Set α} (hf : Function.Involutive f)
    (h : MapsTo f s s) : f '' s = s :=
  h.image_subset.antisymm fun x hx => ⟨f x, h hx, hf x⟩

/-- A set mapped into itself by an involution is its own preimage. -/
theorem MapsTo.preimage_eq_of_involutive {f : α → α} {s : Set α} (hf : Function.Involutive f)
    (h : MapsTo f s s) : f ⁻¹' s = s :=
  Subset.antisymm (fun x hx => hf x ▸ h hx) fun _ hx => h hx

end Set
