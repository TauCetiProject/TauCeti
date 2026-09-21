/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# The trivial F₂ coefficient representation

The index-two Evens norm uses continuous cohomology with trivial `𝔽₂` coefficients. Its
canonical cohomology groups use an object of `TopRep ℤ G`, while its explicit cocycle formulas are
valued in `ZMod 2`. This file supplies the canonical coefficient object.

For a group `G : Type u`, Mathlib's continuous-cohomology resolution requires the coefficient
module to live in `Type u`.  The carrier of `trivialF2 G` is therefore `ULift.{u} (ZMod 2)`, not
`ZMod 2`. The action is trivial, and restriction to a subgroup is definitionally the corresponding
trivial coefficient object for that subgroup.

## Main definitions

* `TauCeti.trivialF2`: trivial `𝔽₂` coefficients over an arbitrary
  universe.

## Main results

* `TauCeti.res_trivialF2`: restriction preserves the coefficient object on the nose.
* `TauCeti.trivialF2_isSmoothDiscrete`: the coefficient object is smooth discrete.
-/

public section

namespace TauCeti

universe u

variable (G : Type u) [Group G]

/-- Trivial `𝔽₂` coefficients as an object of `TopRep ℤ G` in the universe of `G`.

The lift is forced by the universe of Mathlib's continuous-cohomology resolution.  Explicit
cochain formulas may remain `ZMod 2`-valued and cross this lift only when entering the canonical
complex. -/
@[expose] noncomputable def trivialF2 : TopRep ℤ G :=
  TopRep.of (ContRepresentation.trivial ℤ G (ULift.{u} (ZMod 2)))

/-- The carrier of `trivialF2 G` is the universe lift of `ZMod 2`. -/
@[simp] theorem trivialF2_V : (trivialF2 G).V = ULift.{u} (ZMod 2) := (rfl)

/-- The lifted carrier of `trivialF2 G` has the discrete topology. -/
instance : DiscreteTopology (trivialF2 G).V :=
  inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod 2)))

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- Every group element acts trivially on `trivialF2 G`. -/
@[simp]
theorem trivialF2_ρ_apply_apply (g : G) (x : (trivialF2 G).V) :
    (trivialF2 G).ρ g x = x :=
  trivial_ρ_apply ℤ G (ULift.{u} (ZMod 2)) g x

/-- Restriction preserves the trivial `𝔽₂` coefficient object on the nose. -/
theorem res_trivialF2 (S : Subgroup G) :
    TopRep.res (S.subtype : S →* G) (trivialF2 G) = trivialF2 S :=
  res_trivial ℤ G (ULift.{u} (ZMod 2)) S.subtype

variable [TopologicalSpace G]

/-- The trivial `𝔽₂` coefficient object is smooth discrete. -/
theorem trivialF2_isSmoothDiscrete : IsSmoothDiscrete ℤ (trivialF2 G) :=
  trivial_isSmoothDiscrete ℤ (ULift.{u} (ZMod 2))

end TauCeti
