/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Orbit, stabilizer, and fixed-point transfer along surjections

When a `Q`-action on `X` agrees with a `P`-action on `X` along a surjection `f : P → Q` (meaning
`f p • x = p • x`), the `Q`-action has the same orbits and fixed points as the `P`-action, and
when `f : P →* Q` is a surjective group homomorphism, its point stabilizers are the images under
`f` of the `P`-stabilizers.

## Main statements

* `TauCeti.MulAction.orbit_eq_of_surjective`: orbits agree along a surjection preserving the
  action (additive counterpart `TauCeti.AddAction.orbit_eq_of_surjective`).
* `TauCeti.MulAction.stabilizer_eq_map_of_surjective`: stabilizers under a compatible action are
  the images of source stabilizers under a surjective group homomorphism (additive counterpart
  `TauCeti.AddAction.stabilizer_eq_map_of_surjective`).
* `TauCeti.MulAction.fixedPoints_eq_of_surjective`: fixed points agree along a surjection
  preserving the action (additive counterpart `TauCeti.AddAction.fixedPoints_eq_of_surjective`).
-/

public section

namespace TauCeti.MulAction

/-- Orbits of a `Q`-action coinciding with a `P`-action at `x` along a surjection `f : P → Q`
coincide with the `P`-orbits at `x`. -/
@[to_additive TauCeti.AddAction.orbit_eq_of_surjective
  /-- Orbits of a `Q`-action coinciding with a `P`-action at `x` along a surjection `f : P → Q`
  coincide with the `P`-orbits at `x`. -/]
theorem orbit_eq_of_surjective {P Q X : Type*} [SMul P X] [SMul Q X] {f : P → Q}
    (hf : Function.Surjective f) (x : X) (hsmul : ∀ p : P, f p • x = p • x) :
    _root_.MulAction.orbit Q x = _root_.MulAction.orbit P x := by
  have h : (fun q : Q ↦ q • x) ∘ f = fun p : P ↦ p • x := funext hsmul
  exact (hf.range_comp (fun q : Q ↦ q • x)).symm.trans (congrArg Set.range h)

/-- Stabilizers under a `Q`-action coinciding with a `P`-action at `x` along a surjective group
homomorphism `f : P →* Q` are the images under `f` of the `P`-stabilizers. -/
@[to_additive TauCeti.AddAction.stabilizer_eq_map_of_surjective
  /-- Stabilizers under a `Q`-action coinciding with a `P`-action at `x` along a surjective
  additive group homomorphism `f : P →+ Q` are the images under `f` of the `P`-stabilizers. -/]
theorem stabilizer_eq_map_of_surjective {P Q X : Type*} [Group P] [Group Q]
    [MulAction P X] [MulAction Q X] {f : P →* Q} (hf : Function.Surjective f) (x : X)
    (hsmul : ∀ p : P, f p • x = p • x) :
    _root_.MulAction.stabilizer Q x = (_root_.MulAction.stabilizer P x).map f := by
  rw [← Subgroup.map_comap_eq_self_of_surjective hf (_root_.MulAction.stabilizer Q x)]
  congr 1
  ext p
  simp only [Subgroup.mem_comap, _root_.MulAction.mem_stabilizer_iff]
  exact iff_of_eq (congrArg (· = x) (hsmul p))

/-- Fixed points of a `Q`-action coinciding with a `P`-action along a surjection `f : P → Q`
coincide with the `P`-fixed points. -/
@[to_additive TauCeti.AddAction.fixedPoints_eq_of_surjective
  /-- Fixed points of a `Q`-action coinciding with a `P`-action along a surjection `f : P → Q`
  coincide with the `P`-fixed points. -/]
theorem fixedPoints_eq_of_surjective {P Q X : Type*} [Monoid P] [Monoid Q]
    [MulAction P X] [MulAction Q X] {f : P → Q} (hf : Function.Surjective f)
    (hsmul : ∀ (p : P) (x : X), f p • x = p • x) :
    _root_.MulAction.fixedPoints Q X = _root_.MulAction.fixedPoints P X := by
  ext x
  simp only [_root_.MulAction.mem_fixedPoints]
  exact hf.forall.trans (forall_congr' fun p ↦ iff_of_eq (congrArg (· = x) (hsmul p x)))

end TauCeti.MulAction
