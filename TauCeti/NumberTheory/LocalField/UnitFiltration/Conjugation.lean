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
Here `theta_0` is the tame character `TauCeti.IsLocalRing.tameCharacter G 𝒪[L]`, and the
positive-depth maps `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField` are read in the
residue coordinate associated to a uniformizer. The general discrete-valuation-ring conjugation
formulas live in `TauCeti/RingTheory/DiscreteValuationRing/RamificationGroup.lean`
(`TauCeti.IsLocalRing.tameCharacter_conj`,
`TauCeti.IsLocalRing.tameCharacterGraded_ramificationGroupGradedConj`,
`TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_conj`, and
`TauCeti.IsDiscreteValuationRing.ramificationGroupGradedConj_zero`).

When `g` acts on the residue field as `x ↦ x ^ q`, as an arithmetic Frobenius does, equivariance
reads `theta_0(g σ g⁻¹) = theta_0(σ) ^ q`, the finite-level form of the Frobenius twist on tame
inertia.

## Main results

* `TauCeti.tameCharacter_conj_of_smul_eq_pow` and
  `TauCeti.tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow`: conjugation by an
  element acting on the residue field as the `q`-th power map raises the tame character to the
  `q`-th power.

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

/-- **The tame character twisted by a power map.** If `g ∈ G` acts on the residue field as the
`q`-th power map, then `theta_0(g σ g⁻¹) = theta_0(σ) ^ q` for every `σ ∈ G_0`. This applies with
`q` the cardinality of the residue field of a base field to any automorphism of a finite
extension inducing the arithmetic Frobenius on residue fields. -/
theorem tameCharacter_conj_of_smul_eq_pow {g : G} {q : ℕ} (hg : ∀ x : 𝓀[L], g • x = x ^ q)
    (σ : ramificationGroup G 𝒪[L] 0) :
    tameCharacter G 𝒪[L] (MulAut.conjNormal g σ) = tameCharacter G 𝒪[L] σ ^ q :=
  Units.ext (by rw [IsLocalRing.tameCharacter_conj, hg, Units.val_pow_eq_pow_val])

/-- The power-map twist of the tame character, read on the tame quotient `G_0/G_1`. -/
theorem tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow {g : G} {q : ℕ}
    (hg : ∀ x : 𝓀[L], g • x = x ^ q) (τ : RamificationGroupGraded G 𝒪[L] 0) :
    tameCharacterGraded G 𝒪[L] (ramificationGroupGradedConj G 𝒪[L] g 0 τ) =
      tameCharacterGraded G 𝒪[L] τ ^ q :=
  Units.ext (by
    rw [IsLocalRing.tameCharacterGraded_ramificationGroupGradedConj, hg, Units.val_pow_eq_pow_val])

end TauCeti
