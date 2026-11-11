/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path

/-!
# Images of paths under maps continuous on their range

Mathlib's `Path.map'` transports a path along a map that is only continuous on the range of the
path, and records the coercion of the image path and its compatibility with concatenation only
for its continuous special case `Path.map` (`Path.map_coe`, `Path.map_trans`). This file supplies
the corresponding statements for `Path.map'`.

## Main declarations

* `Path.map'_coe` -- the image path `γ.map' h` is the composite `f ∘ γ`.
* `Path.map'_trans` -- the image of a concatenation is the concatenation of the images.
-/

public section

namespace Path

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X}

/-- The image of a path along a map continuous on its range is the composite path. -/
@[simp, grind =]
theorem map'_coe (γ : Path x y) {f : X → Y} (h : ContinuousOn f (Set.range γ)) :
    ⇑(γ.map' h) = f ∘ γ :=
  rfl

/-- The image of a concatenation of paths along a map continuous on its range is the concatenation
of the images. -/
theorem map'_trans (γ : Path x y) (γ' : Path y z) {f : X → Y}
    (h : ContinuousOn f (Set.range (γ.trans γ'))) :
    (γ.trans γ').map' h =
      (γ.map' (h.mono (trans_range γ γ' ▸ Set.subset_union_left))).trans
        (γ'.map' (h.mono (trans_range γ γ' ▸ Set.subset_union_right))) := by
  ext t
  simp only [map'_coe, Function.comp_apply, trans_apply]
  split_ifs <;> rfl

end Path

end
