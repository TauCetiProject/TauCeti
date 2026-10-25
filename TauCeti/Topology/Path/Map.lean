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
path, and records the coercion of the image path only for its continuous special case
`Path.map` (`Path.map_coe`). This file supplies the corresponding statement for `Path.map'`.

## Main declarations

* `Path.map'_coe` -- the image path `γ.map' h` is the composite `f ∘ γ`.
-/

public section

namespace Path

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y : X}

/-- The image of a path along a map continuous on its range is the composite path. -/
@[simp, grind =]
theorem map'_coe (γ : Path x y) {f : X → Y} (h : ContinuousOn f (Set.range γ)) :
    ⇑(γ.map' h) = f ∘ γ :=
  rfl

end Path

end
