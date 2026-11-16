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
# Graded quotients of the principal unit filtration of a local ring

For a commutative local ring `S` with maximal ideal `𝔪` and residue field `κ`, the principal unit
groups `U(S, i) = (𝔪 ^ i).principalUnitGroup` form a decreasing filtration of `Sˣ` (with
`U(S, 0) = Sˣ`). This file defines the successive quotients `PrincipalUnitGraded S i = U(S, i) /
U(S, i + 1)` and records their canonical identifications:
* at depth `0`, reduction of units modulo `𝔪` gives `U(S, 0) / U(S, 1) ≃* κˣ`;
* at positive depth `n + 1`, the map `1 + x ↦ x` gives an additive isomorphism
  `Additive (U(S, n + 1) / U(S, n + 2)) ≃+ 𝔪 ^ (n + 1) ⧸ 𝔪 ^ (n + 2)`.

## Main definitions

* `TauCeti.IsLocalRing.PrincipalUnitGraded S i`: the `i`-th successive quotient
  `U(S, i) / U(S, i + 1)` of the filtration of `Sˣ` by `(𝔪 ^ i).principalUnitGroup`.
* `TauCeti.IsLocalRing.principalUnitGradedZeroEquiv S`: the depth-zero identification
  `U(S, 0) / U(S, 1) ≃* (ResidueField S)ˣ`.
* `TauCeti.IsLocalRing.principalUnitGradedSuccEquivMaximalIdealGraded S n`: the positive-depth
  identification `Additive (U(S, n + 1) / U(S, n + 2)) ≃+ 𝔪 ^ (n + 1) ⧸ (𝔪 • ⊤)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
-/

public section

open IsLocalRing

namespace TauCeti.IsLocalRing

/-- The `i`-th successive quotient `U(S, i) / U(S, i + 1)` of the filtration of `Sˣ` by the
principal unit groups `(𝔪 ^ i).principalUnitGroup` of powers of the maximal ideal. At `i = 0`,
`(𝔪 ^ 0).principalUnitGroup = ⊤` is the full unit group `Sˣ`. -/
abbrev PrincipalUnitGraded (S : Type*) [CommRing S] [IsLocalRing S] (i : ℕ) :=
  (maximalIdeal S ^ i).principalUnitGroup ⧸
    (maximalIdeal S ^ (i + 1)).principalUnitGroup.subgroupOf
      (maximalIdeal S ^ i).principalUnitGroup

section Zero

variable {S : Type*} [CommRing S] [IsLocalRing S]

private noncomputable def principalUnitZeroToResidueUnits (S : Type*) [CommRing S] [IsLocalRing S] :
    (maximalIdeal S ^ 0).principalUnitGroup →* (ResidueField S)ˣ :=
  (Units.map (residue S).toMonoidHom).comp (maximalIdeal S ^ 0).principalUnitGroup.subtype

private theorem ker_principalUnitZeroToResidueUnits :
    (principalUnitZeroToResidueUnits S).ker =
      (maximalIdeal S ^ 1).principalUnitGroup.subgroupOf
        (maximalIdeal S ^ 0).principalUnitGroup := by
  ext u
  rw [principalUnitZeroToResidueUnits, MonoidHom.mem_ker, MonoidHom.comp_apply,
    Subgroup.coe_subtype, ← MonoidHom.mem_ker, ← Ideal.principalUnitGroup_ker,
    IsLocalRing.ker_residue, Subgroup.mem_subgroupOf, pow_one]

private theorem principalUnitZeroToResidueUnits_surjective :
    Function.Surjective (principalUnitZeroToResidueUnits S) := by
  have hres : Function.Surjective (Units.map (residue S).toMonoidHom) :=
    IsLocalRing.surjective_units_map_of_local_ringHom _ residue_surjective inferInstance
  intro v
  obtain ⟨u, rfl⟩ := hres v
  exact ⟨⟨u, by simp⟩, rfl⟩

variable (S) in
/-- At depth `0`, reduction of units modulo the maximal ideal identifies
`U(S, 0) / U(S, 1) = Sˣ / (1 + 𝔪)` with `(ResidueField S)ˣ`. -/
noncomputable def principalUnitGradedZeroEquiv :
    PrincipalUnitGraded S 0 ≃* (ResidueField S)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_principalUnitZeroToResidueUnits (S := S)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ principalUnitZeroToResidueUnits_surjective)

/-- Evaluating `principalUnitGradedZeroEquiv` on the class of a unit reduces it modulo the maximal
ideal. -/
@[simp]
theorem principalUnitGradedZeroEquiv_mk (u : (maximalIdeal S ^ 0).principalUnitGroup) :
    principalUnitGradedZeroEquiv S (QuotientGroup.mk u) =
      Units.map (residue S).toMonoidHom (u : Sˣ) :=
  (MulEquiv.trans_apply ..).trans <|
    (congrArg _ (QuotientGroup.quotientMulEquivOfEq_mk ..)).trans
      (TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk ..)

/-- The underlying residue-field value of `principalUnitGradedZeroEquiv S (QuotientGroup.mk u)` is
`residue S u`. -/
theorem coe_principalUnitGradedZeroEquiv_mk (u : (maximalIdeal S ^ 0).principalUnitGroup) :
    (principalUnitGradedZeroEquiv S (QuotientGroup.mk u) : ResidueField S) =
      residue S ((u : Sˣ) : S) := by
  simp

end Zero

section Succ

variable {S : Type*} [CommRing S] [IsLocalRing S]

variable (S) in
/-- At positive depth `n + 1`, the map `1 + x ↦ x` identifies `Additive (U(S, n + 1) / U(S, n + 2))`
with the maximal-ideal graded piece `𝔪 ^ (n + 1) ⧸ (𝔪 • ⊤)`. -/
noncomputable def principalUnitGradedSuccEquivMaximalIdealGraded (n : ℕ) :
    Additive (PrincipalUnitGraded S (n + 1)) ≃+
      (maximalIdeal S ^ (n + 1) : Ideal S) ⧸
        (maximalIdeal S • ⊤ : Submodule S (maximalIdeal S ^ (n + 1) : Ideal S)) :=
  (Ideal.principalUnitGroupPowQuotientEquiv
      (Ideal.jacobson_bot.trans (ringJacobson_eq_maximalIdeal S)).ge n).toAdditive.trans <|
    (AddEquiv.additiveMultiplicative _).trans
      (Submodule.quotEquivOfEq _ _ (by rw [Ideal.smul_top_eq_comap_mul, ← pow_succ])).toAddEquiv

/-- On a principal unit `u ∈ U(S, n + 1)`, `principalUnitGradedSuccEquivMaximalIdealGraded` sends
its class to the class of `u - 1` in `𝔪 ^ (n + 1) ⧸ (𝔪 • ⊤)`. -/
@[simp]
theorem principalUnitGradedSuccEquivMaximalIdealGraded_ofMul_mk (n : ℕ)
    (u : (maximalIdeal S ^ (n + 1)).principalUnitGroup) :
    principalUnitGradedSuccEquivMaximalIdealGraded S n (Additive.ofMul (QuotientGroup.mk u)) =
      Submodule.Quotient.mk ⟨((u : Sˣ) : S) - 1, Ideal.mem_principalUnitGroup.mp u.2⟩ := by
  rw [principalUnitGradedSuccEquivMaximalIdealGraded]
  simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
    Ideal.principalUnitGroupPowQuotientEquiv_mk, AddEquiv.additiveMultiplicative_apply,
    toAdd_ofAdd, LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply,
    Submodule.quotEquivOfEq_mk]

end Succ

end TauCeti.IsLocalRing
