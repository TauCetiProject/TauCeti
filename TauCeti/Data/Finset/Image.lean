/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Image

/-!
# Images of filtered finsets

* `Finset.image_filter_mem_subset`: the image under `f` of the elements of `s` that `f` maps into
  `t` lies in `t`.
-/

public section

namespace Finset

variable {α β : Type*} [DecidableEq β]

/-- The image under `f` of the elements of `s` that `f` maps into `t` lies in `t`. -/
theorem image_filter_mem_subset (f : α → β) (s : Finset α) (t : Finset β) :
    {a ∈ s | f a ∈ t}.image f ⊆ t :=
  image_subset_iff.2 fun _ ha ↦ (mem_filter.1 ha).2

end Finset
