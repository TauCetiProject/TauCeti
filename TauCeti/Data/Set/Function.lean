/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Function

/-!
# Injectivity on a union

* `Set.InjOn.union_of_disjoint_image`: a map injective on two sets with disjoint images is
  injective on their union.
-/

public section

namespace Set

variable {α β : Type*} {f : α → β} {s t : Set α}

/-- A map injective on two sets whose images are disjoint is injective on their union. -/
theorem InjOn.union_of_disjoint_image (hs : InjOn f s) (ht : InjOn f t)
    (h : Disjoint (f '' s) (f '' t)) : InjOn f (s ∪ t) :=
  (injOn_union h.of_image).2 ⟨hs, ht, fun _ hx _ hy hxy ↦
    disjoint_left.1 h (mem_image_of_mem f hx) (hxy ▸ mem_image_of_mem f hy)⟩

end Set
