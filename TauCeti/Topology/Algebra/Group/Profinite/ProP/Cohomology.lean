/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Algebra.Algebra
public import TauCeti.RepresentationTheory.Continuous.Restriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete

/-!
# Trivial finite-field coefficients for profinite cohomology

This file provides the canonical coefficient object for cohomology of pro-`p` groups: the
trivial representation `trivialFp p G` of a group `G` on `ZMod p`.  When `p` is prime this is
the field `𝔽_p`. Mathlib's continuous-cohomology resolution requires coefficients in the universe
of `G`, so its carrier is the corresponding universe lift of `ZMod p`. The abbreviation
`cohomFp p G n` is continuous cohomology with these coefficients.

The coefficient object is deliberately available for an arbitrary topological group.  The
pro-`p` hypothesis belongs to the theorems which compute this cohomology, not to its definition.
The restriction map is named because later rank and cup-product arguments must change groups
without repeatedly transporting across the definitional equality of trivial representations.

## Main definitions

* `TauCeti.trivialFp`: trivial `𝔽_p` coefficients in the universe of the group.
* `TauCeti.cohomFp`: continuous cohomology with trivial `𝔽_p` coefficients.
* `TauCeti.cohomFpResMap`: restriction on `cohomFp`.

## Main results

* `TauCeti.trivialFp_ρ_apply_apply`: the action is trivial.
* `TauCeti.ofDiscreteModule_trivialFp`: the discrete-coefficient dictionary recovers
  `trivialFp`.
* `TauCeti.res_trivialFp`: restriction preserves trivial coefficients on the nose.

## References

* J.-P. Serre, *Galois Cohomology*, I §4.
-/

public section

namespace TauCeti

universe u

attribute [local instance] DiscreteTopology.instContinuousSMul

section Monoid

variable (p : ℕ) (G : Type u) [Monoid G]

/-- Trivial `ZMod p` coefficients as an object of `TopRep (ZMod p) G` in the universe of `G`.

The universe lift is forced by Mathlib's continuous-cohomology resolution. -/
noncomputable def trivialFp : TopRep (ZMod p) G :=
  TopRep.of (ContRepresentation.trivial (ZMod p) G (ULift.{u} (ZMod p)))

/-- The carrier of `trivialFp p G` is the universe lift of `ZMod p`. -/
@[simp]
theorem trivialFp_V : (trivialFp p G).V = ULift.{u} (ZMod p) := (rfl)

/-- The additive equivalence from the lifted carrier of `trivialFp p G` to `ZMod p`. -/
noncomputable def trivialFpEquiv : (trivialFp p G).V ≃+ ZMod p :=
  AddEquiv.ulift

/-- `trivialFpEquiv` sends a lifted element to its underlying value. -/
@[simp]
theorem trivialFpEquiv_apply (x : ULift.{u} (ZMod p)) :
    trivialFpEquiv p G (cast (trivialFp_V p G).symm x) = x.down :=
  (rfl)

/-- The inverse of `trivialFpEquiv` lifts a value. -/
@[simp]
theorem trivialFpEquiv_symm_apply (x : ZMod p) :
    (trivialFpEquiv p G).symm x = cast (trivialFp_V p G).symm (ULift.up x) :=
  (rfl)

/-- The lifted carrier of `trivialFp p G` has the discrete topology. -/
instance : DiscreteTopology (trivialFp p G).V :=
  inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod p)))

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

/-- Applying the discrete coefficient dictionary to the carrier of `trivialFp` recovers the
coefficient object itself. -/
@[simp]
theorem ofDiscreteModule_trivialFp :
    ofDiscreteModule (ZMod p) G (trivialFp p G).V = trivialFp p G :=
  ofDiscreteModule_eq_self (trivialFp p G)

/-- Every monoid element acts trivially on `trivialFp p G`. -/
@[simp]
theorem trivialFp_ρ_apply_apply (g : G) (x : (trivialFp p G).V) :
    (trivialFp p G).ρ g x = x :=
  ContRepresentation.trivial_apply g x

variable [TopologicalSpace G]

/-- The trivial `ZMod p` coefficient object is smooth discrete. -/
theorem isSmoothDiscrete_trivialFp : IsSmoothDiscrete (ZMod p) (trivialFp p G) :=
  isSmoothDiscrete_trivial (ZMod p) (ULift.{u} (ZMod p))

end Monoid

section Group

variable (p : ℕ) (G : Type u) [Group G]

/-- Restriction preserves the trivial `ZMod p` coefficient object on the nose. -/
@[simp]
theorem res_trivialFp (S : Subgroup G) :
    TopRep.res (S.subtype : S →* G) (trivialFp p G) = trivialFp p S :=
  res_trivial (ZMod p) G (ULift.{u} (ZMod p)) S.subtype

open CategoryTheory _root_.ContinuousCohomology

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Continuous cohomology with trivial `ZMod p` coefficients. -/
noncomputable abbrev cohomFp (n : ℕ) := continuousCohomology n (trivialFp p G)

/-- Restriction on cohomology with trivial `ZMod p` coefficients. -/
noncomputable def cohomFpResMap (S : Subgroup G) (n : ℕ) :
    cohomFp p G n ⟶ cohomFp p S n :=
  ContinuousCohomology.res S (trivialFp p G) n ≫
    eqToHom (congrArg (continuousCohomology n) (res_trivialFp p G S))

/-- The defining equation of restriction with trivial `ZMod p` coefficients. -/
theorem cohomFpResMap_def (S : Subgroup G) (n : ℕ) :
    cohomFpResMap p G S n = ContinuousCohomology.res S (trivialFp p G) n ≫
      eqToHom (congrArg (continuousCohomology n) (res_trivialFp p G S)) :=
  (rfl)

end Group

end TauCeti
