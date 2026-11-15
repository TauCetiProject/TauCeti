/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.Ideal.PrincipalUnitGroup
import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import TauCeti.RingTheory.Ideal.Operations

/-!
# The principal unit filtration of a local ring

For a commutative local ring `R` with maximal ideal `𝔪` and residue field `κ`, the subgroups
`U(R, i) = (𝔪 ^ i).principalUnitGroup` of `Rˣ` form a decreasing filtration starting at
`U(R, 0) = ⊤`. Because `𝔪` is the Jacobson radical of `R`, the general quotient equivalences of
`TauCeti/RingTheory/Ideal/PrincipalUnitGroup.lean` apply without side conditions on the ideal:

* at depth zero, `U(R, 0) / U(R, 1) ≃* κˣ` via reduction of units modulo `𝔪`;
* at positive depth `n + 1`, `U(R, n + 1) / U(R, n + 2)` is isomorphic via `u ↦ u - 1` to the
  additive group `𝔪 ^ (n + 1) / 𝔪 ^ (n + 2)` (written as the quotient of `𝔪 ^ (n + 1)` by
  `𝔪 • ⊤`, the presentation used by
  `TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer`).

## Main definitions

* `TauCeti.IsLocalRing.PrincipalUnitGroupGraded`: the `i`-th successive quotient
  `U(R, i) / U(R, i + 1)` of the principal unit filtration of `R`.
* `TauCeti.IsLocalRing.principalUnitGroupGradedZeroEquivResidueFieldUnits`: the depth-zero
  identification `U(R, 0) / U(R, 1) ≃* (ResidueField R)ˣ`.
* `TauCeti.IsLocalRing.principalUnitGroupGradedSuccEquivMaximalIdealGraded`: the positive-depth
  identification `U(R, n + 1) / U(R, n + 2) ≃* Multiplicative (𝔪 ^ (n + 1) / 𝔪 ^ (n + 2))`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
-/

public section
noncomputable section

open IsLocalRing

namespace TauCeti.IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The `i`-th successive quotient `U(R, i) / U(R, i + 1)` of the filtration of `Rˣ` by the
principal unit groups `(𝔪 ^ i).principalUnitGroup` of the powers of the maximal ideal. -/
abbrev PrincipalUnitGroupGraded (R : Type*) [CommRing R] [IsLocalRing R] (i : ℕ) :=
  (maximalIdeal R ^ i).principalUnitGroup ⧸
    (maximalIdeal R ^ (i + 1)).principalUnitGroup.subgroupOf
      (maximalIdeal R ^ i).principalUnitGroup

private def principalUnitGroupZeroToResidueFieldUnits :
    (maximalIdeal R ^ 0).principalUnitGroup →* (ResidueField R)ˣ :=
  (Units.map (residue R).toMonoidHom).comp (Subgroup.subtype _)

private theorem ker_principalUnitGroupZeroToResidueFieldUnits :
    (principalUnitGroupZeroToResidueFieldUnits (R := R)).ker =
      (maximalIdeal R ^ 1).principalUnitGroup.subgroupOf
        (maximalIdeal R ^ 0).principalUnitGroup := by
  ext u
  rw [principalUnitGroupZeroToResidueFieldUnits, MonoidHom.mem_ker, MonoidHom.comp_apply,
    Subgroup.coe_subtype, ← MonoidHom.mem_ker, ← Ideal.principalUnitGroup_ker, ker_residue,
    pow_one, Subgroup.mem_subgroupOf]

private theorem principalUnitGroupZeroToResidueFieldUnits_surjective :
    Function.Surjective (principalUnitGroupZeroToResidueFieldUnits (R := R)) := by
  intro v
  obtain ⟨u, rfl⟩ :=
    surjective_units_map_of_local_ringHom (residue R) residue_surjective inferInstance v
  exact ⟨⟨u, by simp⟩, rfl⟩

/-- The depth-zero graded piece `U(R, 0) / U(R, 1)` of the principal unit filtration of a local
ring `R` is canonically isomorphic to `(ResidueField R)ˣ`, via reduction of units modulo the
maximal ideal. -/
def principalUnitGroupGradedZeroEquivResidueFieldUnits :
    PrincipalUnitGroupGraded R 0 ≃* (ResidueField R)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq
      (ker_principalUnitGroupZeroToResidueFieldUnits (R := R)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (principalUnitGroupZeroToResidueFieldUnits_surjective (R := R)))

/-- On the class of `u ∈ U(R, 0)`, `principalUnitGroupGradedZeroEquivResidueFieldUnits` reduces the
underlying unit `u : Rˣ` modulo the maximal ideal. -/
@[simp]
theorem principalUnitGroupGradedZeroEquivResidueFieldUnits_mk
    (u : (maximalIdeal R ^ 0).principalUnitGroup) :
    principalUnitGroupGradedZeroEquivResidueFieldUnits (QuotientGroup.mk u) =
      Units.map (residue R).toMonoidHom (u : Rˣ) :=
  (MulEquiv.trans_apply ..).trans <|
    (congrArg _ (QuotientGroup.quotientMulEquivOfEq_mk ..)).trans
      (TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk ..)

private theorem comap_maximalIdeal_pow_succ_eq_smul_top (n : ℕ) :
    Submodule.comap (maximalIdeal R ^ (n + 1)).subtype (maximalIdeal R ^ (n + 2)) =
      maximalIdeal R • ⊤ := by
  rw [Ideal.smul_top_eq_comap_mul, ← pow_succ]

/-- At positive depth `n + 1`, the graded piece `U(R, n + 1) / U(R, n + 2)` of the principal unit
filtration of a local ring `R` is isomorphic via `1 + x ↦ x` to the additive group
`𝔪 ^ (n + 1) / 𝔪 ^ (n + 2)` (presented as `𝔪 ^ (n + 1) ⧸ (𝔪 • ⊤)`). -/
def principalUnitGroupGradedSuccEquivMaximalIdealGraded (n : ℕ) :
    PrincipalUnitGroupGraded R (n + 1) ≃*
      Multiplicative ((maximalIdeal R ^ (n + 1) : Ideal R) ⧸
        (maximalIdeal R • ⊤ : Submodule R (maximalIdeal R ^ (n + 1) : Ideal R))) :=
  (Ideal.principalUnitGroupPowQuotientEquiv (maximalIdeal_le_jacobson (⊥ : Ideal R)) n).trans
    (Submodule.quotEquivOfEq _ _
      (comap_maximalIdeal_pow_succ_eq_smul_top n)).toAddEquiv.toMultiplicative

/-- On the class of `u ∈ U(R, n + 1)`, `principalUnitGroupGradedSuccEquivMaximalIdealGraded` sends
`u` to the residue class of `u - 1` in `𝔪 ^ (n + 1) ⧸ (𝔪 • ⊤)`. -/
@[simp]
theorem principalUnitGroupGradedSuccEquivMaximalIdealGraded_mk (n : ℕ)
    (u : (maximalIdeal R ^ (n + 1)).principalUnitGroup) :
    principalUnitGroupGradedSuccEquivMaximalIdealGraded n (QuotientGroup.mk u) =
      Multiplicative.ofAdd (Submodule.Quotient.mk
        ⟨((u : Rˣ) : R) - 1, Ideal.mem_principalUnitGroup.mp u.2⟩) := by
  rw [principalUnitGroupGradedSuccEquivMaximalIdealGraded]
  refine (MulEquiv.trans_apply ..).trans ?_
  rw [Ideal.principalUnitGroupPowQuotientEquiv_mk]
  simp

end TauCeti.IsLocalRing
