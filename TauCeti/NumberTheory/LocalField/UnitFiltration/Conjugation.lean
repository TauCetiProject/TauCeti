/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup

/-!
# Conjugation on ramification quotients

Let a group `G` act on a nonarchimedean local field `L`, preserving its ring of integers.
Conjugation by an element `σ` of inertia acts trivially on the depth-zero ramification quotient
`G_0 / G_1`, because `G_0 / G_1` embeds into the commutative group `𝓀[L]ˣ` via the tame character
`TauCeti.IsLocalRing.tameCharacter G 𝒪[L]`.

For the positive-depth conjugation formula and the `G`-equivariance of the tame character on
arbitrary discrete valuation rings, see
`TauCeti.RingTheory.DiscreteValuationRing.RamificationGroup`.

## Main results

* `TauCeti.ramificationGroupGradedConj_zero`: inertia acts trivially on `G_0/G_1`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Proposition 9.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField TauCeti.IsLocalRing

namespace TauCeti

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
variable {G : Type*} [Group G] [MulSemiringAction G L] [IsInvariantSubring G 𝒪[L]]

/-- Conjugation by inertia acts trivially on the tame quotient `G_0/G_1`. -/
@[simp]
theorem ramificationGroupGradedConj_zero
    (σ : ramificationGroup G 𝒪[L] 0)
    (τ : RamificationGroupGraded G 𝒪[L] 0) :
    ramificationGroupGradedConj G 𝒪[L] (σ : G) 0 τ = τ :=
  IsDiscreteValuationRing.ramificationGroupGradedConj_zero (FixedPoints.subalgebra ℤ 𝒪[L] G) σ τ

end TauCeti
