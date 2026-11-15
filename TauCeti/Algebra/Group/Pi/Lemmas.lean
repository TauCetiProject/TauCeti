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
* `TauCeti.map_comp_mulSingle`, `TauCeti.map_comp_single`: function composition `f ∘ Pi.mulSingle`
  / `f ∘ Pi.single` for maps preserving `1` / `0`.
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

namespace TauCeti

/-- Post-composing a one-point family `Pi.mulSingle i a` with a map preserving `1` gives
`Pi.mulSingle i (f a)`. -/
@[to_additive (attr := simp)
/-- Post-composing a one-point family `Pi.single i a` with a map preserving `0` gives
`Pi.single i (f a)`. -/]
theorem map_comp_mulSingle {I α β F : Type*} [DecidableEq I] [One α] [One β]
    [FunLike F α β] [OneHomClass F α β] (f : F) (i : I) (a : α) :
    (f : α → β) ∘ Pi.mulSingle i a = Pi.mulSingle i (f a) :=
  (Pi.mulSingle_op (fun _ ↦ f) (fun _ ↦ map_one f) i a).symm

end TauCeti
