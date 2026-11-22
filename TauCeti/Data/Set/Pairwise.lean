/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Pairwise relations on images of sets

* `Set.pairwise_image_of_refl`: for a reflexive relation, the image of a set under any map is
  pairwise related exactly when the set is pairwise related along the map. Unlike
  `Set.InjOn.pairwise_image`, this needs no injectivity: two points with the same image are
  related along the map by reflexivity.
-/

public section

open Function

namespace Set

variable {ι α : Type*} {r : α → α → Prop} {f : ι → α} {s : Set ι}

/-- For a reflexive relation, the image of a set under any map is pairwise related exactly when
the set is pairwise related along the map. See also `Set.InjOn.pairwise_image`. -/
theorem pairwise_image_of_refl [Std.Refl r] :
    (f '' s).Pairwise r ↔ s.Pairwise (r on f) :=
  ⟨fun h _ hx _ hy _ ↦ h.forall₂ (mem_image_of_mem f hx) (mem_image_of_mem f hy),
    Pairwise.image⟩

end Set
