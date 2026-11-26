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
formulas live in `TauCeti/RingTheory/DiscreteValuationRing/RamificationGroup.lean`.

When `g` acts on the residue field as `x ↦ x ^ q`, as an arithmetic Frobenius does, equivariance
reads `theta_0(g σ g⁻¹) = theta_0(σ) ^ q`, the finite-level form of the Frobenius twist on tame
inertia.

## Main results

* `TauCeti.ramificationGroupGradedConj_zero`: inertia acts trivially on
  `G_0/G_1`.
* `TauCeti.ramificationGroupGradedToResidueField_conj`: at depth `i > 0`, conjugation scales the
  residue coordinate by the `i`th power of the tame character.
* `TauCeti.tameCharacter_conj` and `TauCeti.tameCharacterGraded_ramificationGroupGradedConj`:
  the tame character is equivariant for conjugation by `G` and the action of `G` on the residue
  field.
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

/-- Conjugation by inertia acts trivially on the tame quotient `G_0/G_1`. -/
@[simp]
theorem ramificationGroupGradedConj_zero
    (σ : ramificationGroup G 𝒪[L] 0)
    (τ : RamificationGroupGraded G 𝒪[L] 0) :
    ramificationGroupGradedConj G 𝒪[L] (σ : G) 0 τ = τ := by
  apply IsLocalRing.tameCharacterGraded_injective (G := G) (FixedPoints.subalgebra ℤ 𝒪[L] G)
  apply Units.ext
  rw [IsLocalRing.tameCharacterGraded_ramificationGroupGradedConj]
  have hmem : (σ : G) ∈ MonoidHom.ker (MulSemiringAction.toRingAut G 𝓀[L]) := by
    rw [← ramificationGroup_zero_eq_ker_toRingAut]
    exact σ.property
  exact TauCeti.MulSemiringAction.mem_ker_toRingAut_iff.mp hmem _

/-- **The conjugation action formula on positive ramification quotients.** In the residue
coordinate `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField` determined by `π`,
conjugation by `σ ∈ G_0` acts on `G_i/G_{i+1}` as multiplication by `theta_0(σ)^i`, where
`theta_0` is the tame character. -/
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) {π : 𝒪[L]}
    (hπ : Irreducible π) (σ : ramificationGroup G 𝒪[L] 0)
    (τ : RamificationGroupGraded G 𝒪[L] ((n : ℤ) + 1)) :
    (ramificationGroupGradedToResidueField hπ n
        (ramificationGroupGradedConj G 𝒪[L] (σ : G) ((n : ℤ) + 1) τ)).toAdd =
      (tameCharacter G 𝒪[L] σ : 𝓀[L]) ^ (n + 1) *
        (ramificationGroupGradedToResidueField hπ n τ).toAdd :=
  IsLocalRing.ramificationGroupGradedToResidueField_conj n hπ σ τ

/-! ### Equivariance of the tame character -/

/-- **The tame character is equivariant.** For `g ∈ G` and `σ ∈ G_0`, the tame character of
`g σ g⁻¹` is the image of the tame character of `σ` under the automorphism of the residue field
induced by `g`: `theta_0(g σ g⁻¹) = g • theta_0(σ)`. -/
theorem tameCharacter_conj (g : G) (σ : ramificationGroup G 𝒪[L] 0) :
    (tameCharacter G 𝒪[L] (MulAut.conjNormal g σ) : 𝓀[L]) =
      g • (tameCharacter G 𝒪[L] σ : 𝓀[L]) :=
  IsLocalRing.tameCharacter_conj g σ

/-- **The tame character twisted by a power map.** If `g ∈ G` acts on the residue field as the
`q`-th power map, then `theta_0(g σ g⁻¹) = theta_0(σ) ^ q` for every `σ ∈ G_0`. This applies with
`q` the cardinality of the residue field of a base field to any automorphism of a finite
extension inducing the arithmetic Frobenius on residue fields. -/
theorem tameCharacter_conj_of_smul_eq_pow {g : G} {q : ℕ} (hg : ∀ x : 𝓀[L], g • x = x ^ q)
    (σ : ramificationGroup G 𝒪[L] 0) :
    tameCharacter G 𝒪[L] (MulAut.conjNormal g σ) = tameCharacter G 𝒪[L] σ ^ q :=
  Units.ext (by rw [TauCeti.tameCharacter_conj, hg, Units.val_pow_eq_pow_val])

/-- The equivariance of the tame character, read on the tame quotient `G_0/G_1`. -/
theorem tameCharacterGraded_ramificationGroupGradedConj (g : G)
    (τ : RamificationGroupGraded G 𝒪[L] 0) :
    (tameCharacterGraded G 𝒪[L] (ramificationGroupGradedConj G 𝒪[L] g 0 τ) : 𝓀[L]) =
      g • (tameCharacterGraded G 𝒪[L] τ : 𝓀[L]) :=
  IsLocalRing.tameCharacterGraded_ramificationGroupGradedConj g τ

/-- The power-map twist of the tame character, read on the tame quotient `G_0/G_1`. -/
theorem tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow {g : G} {q : ℕ}
    (hg : ∀ x : 𝓀[L], g • x = x ^ q) (τ : RamificationGroupGraded G 𝒪[L] 0) :
    tameCharacterGraded G 𝒪[L] (ramificationGroupGradedConj G 𝒪[L] g 0 τ) =
      tameCharacterGraded G 𝒪[L] τ ^ q :=
  Units.ext (by
    rw [TauCeti.tameCharacterGraded_ramificationGroupGradedConj, hg, Units.val_pow_eq_pow_val])

end TauCeti
