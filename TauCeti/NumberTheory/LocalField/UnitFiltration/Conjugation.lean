/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup
import TauCeti.RingTheory.LocalRing.Localization

/-!
# Conjugation on ramification quotients

Let a group `G` act on a nonarchimedean local field `L`, preserving its ring of integers.
Conjugation by an element `σ` of inertia acts trivially on the tame ramification quotient
`G_0 / G_1`, because `G_0 / G_1` embeds into `(𝓀[L])ˣ` via
`TauCeti.IsDiscreteValuationRing.tameCharacterGraded` and `(𝓀[L])ˣ` is commutative.

The general conjugation-equivariance formulas for the tame character and positive-depth residue
coordinates live in `TauCeti/RingTheory/DiscreteValuationRing/RamificationGroup.lean` under
`TauCeti.IsDiscreteValuationRing`.

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
    ramificationGroupGradedConj G 𝒪[L] (σ : G) 0 τ = τ := by
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible (R := 𝒪[L])
  apply IsDiscreteValuationRing.tameCharacterGraded_injective
    G (Localization.AtPrime ((maximalIdeal 𝒪[L]).under ℤ)) hπ
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    simp only [ramificationGroupGradedConj_mk, IsDiscreteValuationRing.tameCharacterGraded_mk]
    rw [MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_mul, map_inv,
      mul_comm (IsDiscreteValuationRing.tameCharacter G hπ σ)
        (IsDiscreteValuationRing.tameCharacter G hπ τ),
      mul_assoc, mul_inv_cancel, mul_one]

end TauCeti
