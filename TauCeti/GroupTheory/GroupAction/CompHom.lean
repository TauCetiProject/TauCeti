/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Orbit, stabilizer, and fixed-point transfer along surjections

When a `P`-action on `X` factors through a surjective homomorphism `p : P →* Q` via
`α : Q →* M` (for a monoid `M` acting on `X`), the induced `Q`-action `MulAction.compHom X α`
has the same orbits and fixed points as the `P`-action, and its point stabilizers are the images
under `p` of the `P`-stabilizers.

## Main statements

* `TauCeti.MulAction.orbit_compHom_eq_of_surjective`: orbits agree under `MulAction.compHom`
  along a surjection (additive counterpart `TauCeti.AddAction.orbit_compHom_eq_of_surjective`).
* `TauCeti.MulAction.stabilizer_compHom_eq_of_surjective`: stabilizers under `MulAction.compHom`
  are the images of source stabilizers under the surjection (additive counterpart
  `TauCeti.AddAction.stabilizer_compHom_eq_of_surjective`).
* `TauCeti.MulAction.fixedPoints_compHom_eq_of_surjective`: fixed points agree under
  `MulAction.compHom` along a surjection (additive counterpart
  `TauCeti.AddAction.fixedPoints_compHom_eq_of_surjective`).
-/

public section

namespace TauCeti.MulAction

/-- Orbits of a `Q`-action `MulAction.compHom X α` factoring a `P`-action through a surjection
`p : P →* Q` coincide with the `P`-orbits. -/
@[to_additive TauCeti.AddAction.orbit_compHom_eq_of_surjective
  /-- Orbits of a `Q`-action `AddAction.compHom X α` factoring a `P`-action through a surjection
  `p : P →+ Q` coincide with the `P`-orbits. -/]
theorem orbit_compHom_eq_of_surjective {P Q M X : Type*} [Monoid P] [Monoid Q] [Monoid M]
    [MulAction P X] [MulAction M X] {p : P →* Q} (hp : Function.Surjective p) (α : Q →* M)
    (hα : ∀ g (x : X), α (p g) • x = g • x) (x : X) :
    letI := _root_.MulAction.compHom X α
    _root_.MulAction.orbit Q x = _root_.MulAction.orbit P x := by
  let _ := _root_.MulAction.compHom X α
  have h : (fun q : Q ↦ q • x) ∘ p = fun g : P ↦ g • x := funext fun g ↦ hα g x
  exact (hp.range_comp (fun q : Q ↦ q • x)).symm.trans (congrArg Set.range h)

/-- Stabilizers under a `Q`-action `MulAction.compHom X α` factoring a `P`-action through a
surjection `p : P →* Q` are the images under `p` of the `P`-stabilizers. -/
@[to_additive TauCeti.AddAction.stabilizer_compHom_eq_of_surjective
  /-- Stabilizers under a `Q`-action `AddAction.compHom X α` factoring a `P`-action through a
  surjection `p : P →+ Q` are the images under `p` of the `P`-stabilizers. -/]
theorem stabilizer_compHom_eq_of_surjective {P Q M X : Type*} [Group P] [Group Q] [Monoid M]
    [MulAction P X] [MulAction M X] {p : P →* Q} (hp : Function.Surjective p) (α : Q →* M)
    (hα : ∀ g (x : X), α (p g) • x = g • x) (x : X) :
    letI := _root_.MulAction.compHom X α
    _root_.MulAction.stabilizer Q x = (_root_.MulAction.stabilizer P x).map p := by
  let _ := _root_.MulAction.compHom X α
  rw [← Subgroup.map_comap_eq_self_of_surjective hp (_root_.MulAction.stabilizer Q x)]
  congr 1
  ext g
  simp only [Subgroup.mem_comap, _root_.MulAction.mem_stabilizer_iff]
  exact iff_of_eq (congrArg (· = x) (hα g x))

/-- Fixed points of a `Q`-action `MulAction.compHom X α` factoring a `P`-action through a
surjection `p : P →* Q` coincide with the `P`-fixed points. -/
@[to_additive TauCeti.AddAction.fixedPoints_compHom_eq_of_surjective
  /-- Fixed points of a `Q`-action `AddAction.compHom X α` factoring a `P`-action through a
  surjection `p : P →+ Q` coincide with the `P`-fixed points. -/]
theorem fixedPoints_compHom_eq_of_surjective {P Q M X : Type*} [Monoid P] [Monoid Q] [Monoid M]
    [MulAction P X] [MulAction M X] {p : P →* Q} (hp : Function.Surjective p) (α : Q →* M)
    (hα : ∀ g (x : X), α (p g) • x = g • x) :
    letI := _root_.MulAction.compHom X α
    _root_.MulAction.fixedPoints Q X = _root_.MulAction.fixedPoints P X := by
  let _ := _root_.MulAction.compHom X α
  ext x
  simp only [_root_.MulAction.mem_fixedPoints]
  exact hp.forall.trans (forall_congr' fun g ↦ iff_of_eq (congrArg (· = x) (hα g x)))

end TauCeti.MulAction
