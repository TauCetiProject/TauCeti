/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Post-composition with a monoid homomorphism and one-point families

`MonoidHom.compLeft f I` applies `f : α →* β` coordinatewise to a family `I → α`. It sends the
one-point family `Pi.mulSingle i a` to the one-point family `Pi.mulSingle i (f a)`, since `f` sends
`1` to `1`.

## Main results

* `MonoidHom.compLeft_mulSingle`, `AddMonoidHom.compLeft_single`: post-composition maps
  one-point families to one-point families.
-/

public section

namespace MonoidHom

variable {α β I : Type*} [MulOneClass α] [MulOneClass β] [DecidableEq I]

/-- Post-composition with `f` sends the one-point family `Pi.mulSingle i a` to
`Pi.mulSingle i (f a)`. -/
@[to_additive (attr := simp) /-- Post-composition with `f` sends the one-point family
`Pi.single i a` to `Pi.single i (f a)`. -/]
theorem compLeft_mulSingle (f : α →* β) (i : I) (a : α) :
    f.compLeft I (Pi.mulSingle i a) = Pi.mulSingle i (f a) :=
  funext fun j ↦ Pi.apply_mulSingle (fun _ ↦ f) (fun _ ↦ map_one f) i a j

end MonoidHom
