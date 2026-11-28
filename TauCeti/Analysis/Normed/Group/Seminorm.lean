/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Seminorm

/-!
# Additional lemmas on group seminorms

This file extends `Mathlib.Analysis.Normed.Group.Seminorm` with helper lemmas for additive group
seminorms.

## Main results

* `TauCeti.map_add_eq_left_of_map_eq_zero`: adding an element where an additive group seminorm
  vanishes leaves the seminorm unchanged.
-/

public section

namespace TauCeti

/-- Adding an element on which an additive group seminorm vanishes leaves the seminorm
unchanged. -/
theorem map_add_eq_left_of_map_eq_zero {F α β : Type*} [AddGroup α] [AddCommMonoid β]
    [PartialOrder β] [FunLike F α β] [AddGroupSeminormClass F α β] (p : F) (x : α) {y : α}
    (hy : p y = 0) : p (x + y) = p x :=
  le_antisymm
    (by simpa [hy] using map_add_le_add p x y)
    (by simpa [hy] using map_add_le_add p (x + y) (-y))

end TauCeti
