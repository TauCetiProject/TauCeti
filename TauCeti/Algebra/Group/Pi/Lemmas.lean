/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import TauCeti.Logic.Function.Extend

/-!
# Post-composition with a monoid homomorphism, one-point families and restriction

`MonoidHom.compLeft f I` applies `f : α →* β` coordinatewise to a family `I → α`. It sends the
one-point family `Pi.mulSingle i a` to the one-point family `Pi.mulSingle i (f a)`, since `f` sends
`1` to `1`; more generally, `f ∘ Pi.mulSingle i a = Pi.mulSingle i (f a)` holds for any
`1`-preserving map `f` (`TauCeti.map_comp_mulSingle`, `TauCeti.map_comp_single`).

Restriction `g ↦ fun i ↦ g (f i)` of a product of monoids along an injective map `f`, the monoid
homomorphism `MonoidHom.pi fun i ↦ Pi.evalMonoidHom G (f i)`, is surjective: extend by `1` off the
range of `f`.

## Main results

* `TauCeti.map_comp_mulSingle`, `TauCeti.map_comp_single`: composing a `1`- or `0`-preserving map
  with a one-point family gives the mapped one-point family.
* `MonoidHom.compLeft_mulSingle`, `AddMonoidHom.compLeft_single`: post-composition maps
  one-point families to one-point families.
* `MonoidHom.pi_evalMonoidHom_surjective_of_injective`,
  `AddMonoidHom.pi_evalAddMonoidHom_surjective_of_injective`: restriction of a product of monoids
  along an injective map is surjective.
-/

public section

namespace TauCeti

/-- A map preserving `1` applied coordinatewise to `Pi.mulSingle i a` gives
`Pi.mulSingle i (f a)`. -/
@[to_additive (attr := simp) /-- A map preserving `0` applied coordinatewise to `Pi.single i a`
gives `Pi.single i (f a)`. -/]
theorem map_comp_mulSingle {F α β I : Type*} [One α] [One β] [DecidableEq I] [FunLike F α β]
    [OneHomClass F α β] (f : F) (i : I) (a : α) :
    f ∘ Pi.mulSingle i a = Pi.mulSingle i (f a) :=
  (Pi.mulSingle_op (fun _ ↦ f) (fun _ ↦ map_one f) i a).symm

end TauCeti

namespace MonoidHom

variable {α β I : Type*} [MulOneClass α] [MulOneClass β] [DecidableEq I]

/-- Post-composition with `f` sends the one-point family `Pi.mulSingle i a` to
`Pi.mulSingle i (f a)`. -/
@[to_additive (attr := simp) /-- Post-composition with `f` sends the one-point family
`Pi.single i a` to `Pi.single i (f a)`. -/]
theorem compLeft_mulSingle (f : α →* β) (i : I) (a : α) :
    f.compLeft I (Pi.mulSingle i a) = Pi.mulSingle i (f a) :=
  TauCeti.map_comp_mulSingle f i a

/-- Restriction `g ↦ fun i ↦ g (f i)` of a product of monoids along an injective map `f` is
surjective: extend by `1` off the range of `f`. -/
@[to_additive /-- Restriction `g ↦ fun i ↦ g (f i)` of a product of additive monoids along an
injective map `f` is surjective: extend by `0` off the range of `f`. -/]
theorem pi_evalMonoidHom_surjective_of_injective {σ τ : Type*} {G : τ → Type*}
    [∀ j, MulOneClass (G j)] {f : σ → τ} (hf : Function.Injective f) :
    Function.Surjective (MonoidHom.pi fun i ↦ Pi.evalMonoidHom G (f i)) :=
  hf.surjective_pi_comp_right 1

end MonoidHom
