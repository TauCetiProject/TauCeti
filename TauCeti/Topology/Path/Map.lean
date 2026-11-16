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

It also records that a map carrying two composable paths onto two composable paths carries their
concatenation onto the concatenation of the images (`Path.comp_trans_eq_of_comp_eq`); unlike
`Path.map_trans`, the map need not be continuous.

## Main declarations

* `Path.map'_coe` -- the image path `γ.map' h` is the composite `f ∘ γ`.
* `Path.comp_trans_eq_of_comp_eq` -- if `f ∘ Γ = γ` and `f ∘ Γ' = γ'`, then
  `f ∘ Γ.trans Γ' = γ.trans γ'`.
-/

public section

namespace Path

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y : X}

/-- The image of a path along a map continuous on its range is the composite path. -/
@[simp, grind =]
theorem map'_coe (γ : Path x y) {f : X → Y} (h : ContinuousOn f (Set.range γ)) :
    ⇑(γ.map' h) = f ∘ γ :=
  rfl

/-- If `f` carries the path `Γ` onto `γ` and `Γ'` onto `γ'`, it carries the concatenation
`Γ.trans Γ'` onto `γ.trans γ'`. -/
theorem comp_trans_eq_of_comp_eq {z : X} {a b c : Y} {f : X → Y} {Γ : Path x y} {Γ' : Path y z}
    {γ : Path a b} {γ' : Path b c} (h : f ∘ Γ = γ) (h' : f ∘ Γ' = γ') :
    f ∘ Γ.trans Γ' = γ.trans γ' := by
  funext t
  simp only [Function.comp_apply, trans_apply, apply_dite f, ← h, ← h']

end Path

end
