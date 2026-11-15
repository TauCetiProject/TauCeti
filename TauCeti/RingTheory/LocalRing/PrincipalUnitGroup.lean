/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.Ideal.PrincipalUnitGroup
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Successive quotients of the principal unit filtration of a local ring

For a local ring `S` with maximal ideal `𝔪`, the subgroups `(𝔪 ^ i).principalUnitGroup` filter `Sˣ`:
at `i = 0` one recovers `Sˣ` itself (`Ideal.principalUnitGroup_top`), and at `i ≥ 1` one obtains
the congruence subgroups `1 + 𝔪 ^ i`. This file names the successive quotients of this filtration
and identifies them with residue-field data at depth `0` and with maximal-ideal graded pieces at
positive depth.

At depth `0`, reduction modulo `𝔪` identifies
`(𝔪 ^ 0).principalUnitGroup ⧸ (𝔪 ^ 1).principalUnitGroup` with `(ResidueField S)ˣ`. At depth
`n + 1`, `Ideal.principalUnitGroupPowQuotientEquiv` identifies
`(1 + 𝔪 ^ (n + 1)) ⧸ (1 + 𝔪 ^ (n + 2))` with the additive group `𝔪 ^ (n + 1) ⧸ 𝔪 • 𝔪 ^ (n + 1)`
via `u ↦ u - 1`. Over a discrete valuation ring, combining the positive-depth equivalence with a
choice of uniformizer identifies each positive graded piece with the additive residue field
(`TauCeti.principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer`).

## Main definitions

* `TauCeti.IsLocalRing.PrincipalUnitGroupGraded`: the `i`-th successive quotient of the filtration
  of `Sˣ` by `(maximalIdeal S ^ i).principalUnitGroup`.
* `TauCeti.IsLocalRing.principalUnitGroupGradedZeroEquivResidueFieldUnits`: the depth-`0`
  isomorphism `PrincipalUnitGroupGraded S 0 ≃* (ResidueField S)ˣ`.
* `TauCeti.IsLocalRing.principalUnitGroupGradedSuccEquivMaximalIdealGraded`: the positive-depth
  isomorphism `PrincipalUnitGroupGraded S (n + 1) ≃* Multiplicative (𝔪 ^ (n + 1) ⧸ 𝔪 • ⊤)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5–6.
-/

public section
noncomputable section

open IsLocalRing

namespace TauCeti

namespace IsLocalRing

variable (S : Type*) [CommRing S] [IsLocalRing S]

/-- The `i`-th successive quotient of the unit filtration `(maximalIdeal S ^ i).principalUnitGroup`
on a local ring `S`: `Sˣ ⧸ (1 + 𝔪)` at `i = 0`, and `(1 + 𝔪 ^ i) ⧸ (1 + 𝔪 ^ (i + 1))` for
`i ≥ 1`. -/
abbrev PrincipalUnitGroupGraded (i : ℕ) :=
  (maximalIdeal S ^ i).principalUnitGroup ⧸
    ((maximalIdeal S ^ (i + 1)).principalUnitGroup.subgroupOf
      (maximalIdeal S ^ i).principalUnitGroup)

/-- Every graded piece of the principal-unit filtration of a commutative local ring is
commutative. -/
instance instIsMulCommutativePrincipalUnitGroupGraded (i : ℕ) :
    IsMulCommutative (PrincipalUnitGroupGraded S i) :=
  IsMulCommutative.of_comm fun a b ↦ by
    induction a using QuotientGroup.induction_on with | _ u =>
    induction b using QuotientGroup.induction_on with | _ v =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mul_comm]

private def principalUnitGroupZeroToResidueFieldUnits :
    (maximalIdeal S ^ 0).principalUnitGroup →* (ResidueField S)ˣ :=
  (Units.map (residue S).toMonoidHom).comp (maximalIdeal S ^ 0).principalUnitGroup.subtype

private theorem ker_principalUnitGroupZeroToResidueFieldUnits :
    (principalUnitGroupZeroToResidueFieldUnits S).ker =
      ((maximalIdeal S ^ 1).principalUnitGroup).subgroupOf
        (maximalIdeal S ^ 0).principalUnitGroup := by
  ext u
  rw [MonoidHom.mem_ker, principalUnitGroupZeroToResidueFieldUnits, MonoidHom.comp_apply,
    Subgroup.coe_subtype, Units.ext_iff, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, Units.val_one, ← sub_eq_zero, ← map_one (residue S), ← map_sub,
    residue_eq_zero_iff, Subgroup.mem_subgroupOf, pow_one, Ideal.mem_principalUnitGroup]

private theorem principalUnitGroupZeroToResidueFieldUnits_surjective :
    Function.Surjective (principalUnitGroupZeroToResidueFieldUnits S) := by
  intro v
  obtain ⟨u, rfl⟩ :=
    surjective_units_map_of_local_ringHom (residue S) residue_surjective inferInstance v
  exact ⟨⟨u, by simp⟩, rfl⟩

/-- At depth `0`, the quotient `(𝔪 ^ 0).principalUnitGroup ⧸ (𝔪 ^ 1).principalUnitGroup` is
canonically isomorphic to `(ResidueField S)ˣ` via reduction modulo `𝔪` (compare
`Ideal.unitsQuotientPrincipalUnitGroupEquiv` on `Sˣ ⧸ (1 + 𝔪)`). -/
def principalUnitGroupGradedZeroEquivResidueFieldUnits :
    PrincipalUnitGroupGraded S 0 ≃* (ResidueField S)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq
      (ker_principalUnitGroupZeroToResidueFieldUnits S).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (principalUnitGroupZeroToResidueFieldUnits S)
      (principalUnitGroupZeroToResidueFieldUnits_surjective S))

/-- Evaluating `principalUnitGroupGradedZeroEquivResidueFieldUnits` on the class of a unit reduces
that unit modulo the maximal ideal. -/
@[simp]
theorem principalUnitGroupGradedZeroEquivResidueFieldUnits_mk
    (u : (maximalIdeal S ^ 0).principalUnitGroup) :
    principalUnitGroupGradedZeroEquivResidueFieldUnits S (QuotientGroup.mk u) =
      Units.map (residue S).toMonoidHom (u : Sˣ) := by
  simp only [principalUnitGroupGradedZeroEquivResidueFieldUnits, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk]
  rfl

private theorem comap_maximalIdeal_pow_succ_eq_smul_top (m : ℕ) :
    Submodule.comap (maximalIdeal S ^ m).subtype (maximalIdeal S ^ (m + 1)) =
      (maximalIdeal S • ⊤ : Submodule S ↥(maximalIdeal S ^ m)) := by
  ext x
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_smul_top_iff, smul_eq_mul,
    pow_succ']

/-- At positive depth `n + 1`, the quotient `(1 + 𝔪 ^ (n + 1)) ⧸ (1 + 𝔪 ^ (n + 2))` is isomorphic
to the multiplicative form of the graded piece `𝔪 ^ (n + 1) ⧸ 𝔪 • ⊤` via `u ↦ u - 1`. -/
def principalUnitGroupGradedSuccEquivMaximalIdealGraded (n : ℕ) :
    PrincipalUnitGroupGraded S (n + 1) ≃*
      Multiplicative
        (↥(maximalIdeal S ^ (n + 1)) ⧸
          (maximalIdeal S • ⊤ : Submodule S ↥(maximalIdeal S ^ (n + 1)))) :=
  (Ideal.principalUnitGroupPowQuotientEquiv
      (jacobson_eq_maximalIdeal (R := S) ⊥ bot_ne_top).ge n).trans
    (Submodule.quotEquivOfEq _ _
      (comap_maximalIdeal_pow_succ_eq_smul_top S (n + 1))).toMultiplicative

/-- Evaluating `principalUnitGroupGradedSuccEquivMaximalIdealGraded` on the class of `u` gives the
class of `u - 1` in `𝔪 ^ (n + 1) ⧸ 𝔪 • ⊤`. -/
@[simp]
theorem principalUnitGroupGradedSuccEquivMaximalIdealGraded_mk (n : ℕ)
    (u : (maximalIdeal S ^ (n + 1)).principalUnitGroup) :
    principalUnitGroupGradedSuccEquivMaximalIdealGraded S n (QuotientGroup.mk u) =
      .ofAdd (Submodule.Quotient.mk ⟨((u : Sˣ) : S) - 1, Ideal.mem_principalUnitGroup.mp u.2⟩) := by
  simp only [principalUnitGroupGradedSuccEquivMaximalIdealGraded, MulEquiv.trans_apply,
    Ideal.principalUnitGroupPowQuotientEquiv_mk]
  rfl

end IsLocalRing

end TauCeti
