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
`1` to `1`.

Restriction `g ↦ fun i ↦ g (f i)` of a product of monoids along an injective map `f`, the monoid
homomorphism `MonoidHom.pi fun i ↦ Pi.evalMonoidHom G (f i)`, is surjective: extend by `1` off the
range of `f`.

## Main results

* `MonoidHom.compLeft_mulSingle`, `AddMonoidHom.compLeft_single`: post-composition maps
  one-point families to one-point families.
* `MonoidHom.pi_evalMonoidHom_surjective_of_injective`,
  `AddMonoidHom.pi_evalAddMonoidHom_surjective_of_injective`: restriction of a product of monoids
  along an injective map is surjective.
* `Function.extend_const_eq_mulSingle`, `Function.extend_const_eq_single`: extending a constant
  family from a unique index type yields `Pi.mulSingle` / `Pi.single`.
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

/-- Restriction `g ↦ fun i ↦ g (f i)` of a product of monoids along an injective map `f` is
surjective: extend by `1` off the range of `f`. -/
@[to_additive /-- Restriction `g ↦ fun i ↦ g (f i)` of a product of additive monoids along an
injective map `f` is surjective: extend by `0` off the range of `f`. -/]
theorem pi_evalMonoidHom_surjective_of_injective {σ τ : Type*} {G : τ → Type*}
    [∀ j, MulOneClass (G j)] {f : σ → τ} (hf : Function.Injective f) :
    Function.Surjective (MonoidHom.pi fun i ↦ Pi.evalMonoidHom G (f i)) :=
  hf.surjective_pi_comp_right 1

end MonoidHom

/-- Extending a constant family on a unique index type `κ` along `f : κ → ι` with fallback `1`
produces `Pi.mulSingle (f default) x`. -/
@[to_additive /-- Extending a constant family on a unique index type `κ` along `f : κ → ι` with
fallback `0` produces `Pi.single (f default) x`. -/]
theorem Function.extend_const_eq_mulSingle {κ ι α : Type*} [Unique κ] [DecidableEq ι]
    [One α] (f : κ → ι) (x : α) :
    Function.extend f (fun _ ↦ x) 1 = Pi.mulSingle (f default) x := by
  rw [← Subsingleton.pi_mulSingle_eq default x,
    (Function.injective_of_subsingleton f).extend_mulSingle]
