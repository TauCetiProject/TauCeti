/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# The trivial F₂ coefficient representation

This file defines a trivial object of `TopRep ℤ G` whose carrier is a universe lift of `ZMod 2`.
It is stable under restriction and is smooth discrete, as needed for continuous cohomology with
trivial `𝔽₂` coefficients.

For `G : Type u`, Mathlib's continuous-cohomology resolution requires the coefficient module to
live in `Type u`. The carrier of `trivialF2 G` is therefore `ULift.{u} (ZMod 2)`, not
`ZMod 2`. The action is trivial, and restriction to a subgroup is definitionally the corresponding
trivial coefficient object for that subgroup.

## Main definitions

* `TauCeti.trivialF2`: trivial `𝔽₂` coefficients over an arbitrary
  universe.
* `TauCeti.trivialF2ResMap`: restriction on continuous cohomology with trivial `𝔽₂`
  coefficients.

## Main results

* `TauCeti.trivialF2_V`: the carrier is `ULift (ZMod 2)`.
* `TauCeti.trivialF2Equiv`: the additive equivalence that crosses the universe lift.
* `TauCeti.res_trivialF2`: restriction preserves the coefficient object on the nose.
* `TauCeti.trivialF2_isSmoothDiscrete`: the coefficient object is smooth discrete.
-/

public section

namespace TauCeti

universe u

section Monoid

variable (G : Type u) [Monoid G]

/-- Trivial `𝔽₂` coefficients as an object of `TopRep ℤ G` in the universe of `G`.

The lift is forced by the universe of Mathlib's continuous-cohomology resolution. -/
noncomputable def trivialF2 : TopRep ℤ G :=
  TopRep.of (ContRepresentation.trivial ℤ G (ULift.{u} (ZMod 2)))

/-- The carrier of `trivialF2 G` is the universe lift of `ZMod 2`. -/
@[simp] theorem trivialF2_V : (trivialF2 G).V = ULift.{u} (ZMod 2) := (rfl)

/-- The additive equivalence from the lifted carrier of `trivialF2 G` to `ZMod 2`. -/
noncomputable def trivialF2Equiv : (trivialF2 G).V ≃+ ZMod 2 := by
  change ULift.{u} (ZMod 2) ≃+ ZMod 2
  exact AddEquiv.ulift

/-- `trivialF2Equiv` sends a lifted element to its underlying value. -/
@[simp]
theorem trivialF2Equiv_apply (x : ULift.{u} (ZMod 2)) :
    trivialF2Equiv G (cast (trivialF2_V G).symm x) = x.down :=
  -- `(rfl)`, not `rfl`: the body of `trivialF2Equiv` is hidden, and this lemma is its public
  -- application rule.
  (rfl)

/-- The inverse of `trivialF2Equiv` lifts a value. -/
@[simp]
theorem trivialF2Equiv_symm_apply (x : ZMod 2) :
    (trivialF2Equiv G).symm x = cast (trivialF2_V G).symm (ULift.up x) :=
  -- As above, the parenthesized proof keeps the hidden definition out of downstream reduction.
  (rfl)

/-- The lifted carrier of `trivialF2 G` has the discrete topology. -/
instance : DiscreteTopology (trivialF2 G).V :=
  inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod 2)))

variable [TopologicalSpace G]

/-- The trivial `𝔽₂` coefficient object is smooth discrete. -/
theorem trivialF2_isSmoothDiscrete : IsSmoothDiscrete ℤ (trivialF2 G) :=
  trivial_isSmoothDiscrete ℤ (ULift.{u} (ZMod 2))

end Monoid

section Group

variable (G : Type u) [Group G]

/-- Restriction preserves the trivial `𝔽₂` coefficient object on the nose. -/
theorem res_trivialF2 (S : Subgroup G) :
    TopRep.res (S.subtype : S →* G) (trivialF2 G) = trivialF2 S :=
  res_trivial ℤ G (ULift.{u} (ZMod 2)) S.subtype

open CategoryTheory _root_.ContinuousCohomology

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Restriction on continuous cohomology with trivial `𝔽₂` coefficients. This is the
generic restriction map followed by the on-the-nose identification `res_trivialF2`. -/
noncomputable def trivialF2ResMap (S : Subgroup G) (n : ℕ) :
    continuousCohomology n (trivialF2 G) ⟶ continuousCohomology n (trivialF2 S) :=
  ContinuousCohomology.res S (trivialF2 G) n ≫
    eqToHom (congrArg (continuousCohomology n) (res_trivialF2 G S))

end Group

end TauCeti
