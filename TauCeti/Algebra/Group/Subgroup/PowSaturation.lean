/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.Torsion
public import TauCeti.Algebra.Group.Submonoid.NSMulSaturation
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Positive-power saturation of subgroups

Given a subgroup `H` of a commutative group `G`, its *positive-power saturation* `H.powSaturation`
is the subgroup of elements `g : G` with `g ^ n ∈ H` for some `n > 0` (additively
`H.nsmulSaturation`). It is the least `PowSaturated` subgroup containing `H`, equals the pullback of
`CommGroup.torsion (G ⧸ H)` along `QuotientGroup.mk' H`, and induces a canonical isomorphism
`H.powSaturation ⧸ H.subgroupOf H.powSaturation ≃* CommGroup.torsion (G ⧸ H)`. Every element of
this quotient has finite order (`Subgroup.isMulTorsion_quotient_powSaturation`), and for finitely
generated `H.powSaturation`, this quotient is finite (`Subgroup.finite_quotient_powSaturation`).

## Main declarations

* `Subgroup.powSaturation`, `AddSubgroup.nsmulSaturation`,
  `Subgroup.powSaturation_le_iff_le`, `Subgroup.powSaturation_eq_comap_torsion`,
  `Subgroup.quotientPowSaturationEquivTorsion`,
  `Subgroup.isMulTorsion_quotient_powSaturation`, `Subgroup.finite_quotient_powSaturation`.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapter 2.
* W. Fulton, *Introduction to Toric Varieties*, §1.2.
-/

public section

namespace Subgroup

variable {G : Type*} [CommGroup G] (H : Subgroup G)

/-- The positive-power saturation of a subgroup `H` of a commutative group `G`, consisting of all
elements `g : G` with `g ^ n ∈ H` for some `n > 0`. -/
@[to_additive
/-- The positive-multiple saturation of an additive subgroup `H` of an abelian group `G`, consisting
of all elements `g : G` with `n • g ∈ H` for some `n > 0`. -/]
def powSaturation : Subgroup G where
  toSubmonoid := H.toSubmonoid.powSaturation
  inv_mem' {x} hx := by
    obtain ⟨n, hn, hxn⟩ := Submonoid.mem_powSaturation.1 hx
    exact Submonoid.mem_powSaturation.2 ⟨n, hn, inv_pow x n ▸ H.inv_mem hxn⟩

/-- The underlying submonoid of `H.powSaturation` is `H.toSubmonoid.powSaturation`. -/
@[to_additive (attr := simp)
/-- The underlying add-submonoid of `H.nsmulSaturation` is `H.toAddSubmonoid.nsmulSaturation`. -/]
theorem toSubmonoid_powSaturation :
    H.powSaturation.toSubmonoid = H.toSubmonoid.powSaturation := (rfl)

/-- An element belongs to `H.powSaturation` iff some positive power belongs to `H`. -/
@[to_additive (attr := simp)
/-- An element belongs to `H.nsmulSaturation` iff some positive multiple belongs to `H`. -/]
theorem mem_powSaturation {g : G} : g ∈ H.powSaturation ↔ ∃ n, 0 < n ∧ g ^ n ∈ H :=
  Submonoid.mem_powSaturation

/-- Every subgroup is contained in its positive-power saturation. -/
@[to_additive (attr := simp)
/-- Every additive subgroup is contained in its positive-multiple saturation. -/]
theorem le_powSaturation : H ≤ H.powSaturation := H.toSubmonoid.le_powSaturation

/-- The positive-power saturation of a subgroup is `PowSaturated`. -/
@[to_additive
/-- The positive-multiple saturation of an additive subgroup is `NSMulSaturated`. -/]
theorem powSaturated_powSaturation : H.powSaturation.PowSaturated :=
  H.toSubmonoid.powSaturated_powSaturation

/-- Positive-power saturation of subgroups is monotone. -/
@[to_additive (attr := gcongr)
/-- Positive-multiple saturation of additive subgroups is monotone. -/]
theorem powSaturation_mono {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) :
    H₁.powSaturation ≤ H₂.powSaturation := Submonoid.powSaturation_mono h

/-- `H.powSaturation` is the least `PowSaturated` subgroup containing `H`. -/
@[to_additive
/-- `H.nsmulSaturation` is the least `NSMulSaturated` additive subgroup containing `H`. -/]
theorem powSaturation_le_iff_le {H₁ H₂ : Subgroup G} (h : H₂.PowSaturated) :
    H₁.powSaturation ≤ H₂ ↔ H₁ ≤ H₂ :=
  Submonoid.powSaturation_le_iff_le h

/-- A `PowSaturated` subgroup equals its positive-power saturation. -/
@[to_additive (attr := simp)
/-- An `NSMulSaturated` additive subgroup equals its positive-multiple saturation. -/]
theorem powSaturation_eq_self (h : H.PowSaturated) : H.powSaturation = H :=
  le_antisymm ((powSaturation_le_iff_le h).2 le_rfl) H.le_powSaturation

/-- Positive-power saturation of subgroups is idempotent. -/
@[to_additive
/-- Positive-multiple saturation of additive subgroups is idempotent. -/]
theorem powSaturation_powSaturation : H.powSaturation.powSaturation = H.powSaturation :=
  H.powSaturation.powSaturation_eq_self H.powSaturated_powSaturation

/-- `H.powSaturation` is the pullback of the torsion subgroup of `G ⧸ H`. -/
@[to_additive
/-- `H.nsmulSaturation` is the pullback of the torsion subgroup of `G ⧸ H`. -/]
theorem powSaturation_eq_comap_torsion :
    H.powSaturation = (CommGroup.torsion (G ⧸ H)).comap (QuotientGroup.mk' H) := by
  ext g
  simp [mem_powSaturation, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one,
    ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]

/-- The saturation quotient `H.powSaturation ⧸ H.subgroupOf H.powSaturation` is canonically
isomorphic to `CommGroup.torsion (G ⧸ H)`. -/
@[to_additive
/-- The saturation quotient `H.nsmulSaturation ⧸ H.addSubgroupOf H.nsmulSaturation` is canonically
isomorphic to `AddCommGroup.torsion (G ⧸ H)`. -/]
noncomputable def quotientPowSaturationEquivTorsion :
    H.powSaturation ⧸ H.subgroupOf H.powSaturation ≃* CommGroup.torsion (G ⧸ H) :=
  (Subgroup.quotientSubgroupOfMulEquivMap H H.powSaturation).trans <|
    MulEquiv.subgroupCongr <| by
      rw [H.powSaturation_eq_comap_torsion]
      exact Subgroup.map_comap_eq_self
        (by rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective H)]; exact le_top)

/-- `quotientPowSaturationEquivTorsion` sends the class of `g : H.powSaturation` to the class of
`g` in `G ⧸ H`. -/
@[to_additive (attr := simp)
/-- `quotientNsmulSaturationEquivTorsion` sends the class of `g : H.nsmulSaturation` to the class
of `g` in `G ⧸ H`. -/]
theorem coe_quotientPowSaturationEquivTorsion_mk (g : H.powSaturation) :
    (H.quotientPowSaturationEquivTorsion (g : H.powSaturation ⧸ H.subgroupOf H.powSaturation) :
      G ⧸ H) = (g : G) := by
  simp [quotientPowSaturationEquivTorsion]

/-- The inverse of `quotientPowSaturationEquivTorsion` sends the torsion class of
`g : H.powSaturation` back to its class modulo `H.subgroupOf H.powSaturation`. -/
@[to_additive (attr := simp)
/-- The inverse of `quotientNsmulSaturationEquivTorsion` sends the torsion class of
`g : H.nsmulSaturation` back to its class modulo `H.addSubgroupOf H.nsmulSaturation`. -/]
theorem quotientPowSaturationEquivTorsion_symm_mk (g : H.powSaturation)
    (hg : (g : G ⧸ H) ∈ CommGroup.torsion (G ⧸ H)) :
    H.quotientPowSaturationEquivTorsion.symm ⟨(g : G ⧸ H), hg⟩ =
      (g : H.powSaturation ⧸ H.subgroupOf H.powSaturation) :=
  (MulEquiv.symm_apply_eq _).2 (Subtype.ext (H.coe_quotientPowSaturationEquivTorsion_mk g).symm)

/-- Every element of `H.powSaturation ⧸ H.subgroupOf H.powSaturation` has finite order. -/
@[to_additive
/-- Every element of `H.nsmulSaturation ⧸ H.addSubgroupOf H.nsmulSaturation` is torsion. -/]
theorem isMulTorsion_quotient_powSaturation :
    IsMulTorsion (H.powSaturation ⧸ H.subgroupOf H.powSaturation) := fun q ↦
  QuotientGroup.induction_on q fun x ↦
    have ⟨n, hn, hxn⟩ := (mem_powSaturation H).1 x.property
    isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

/-- When `H.powSaturation` is finitely generated, `H` has finite index in `H.powSaturation`. -/
@[to_additive
/-- When `H.nsmulSaturation` is FG, `H` has finite quotient in `H.nsmulSaturation`. -/]
theorem finite_quotient_powSaturation (hfg : H.powSaturation.FG) :
    Finite (H.powSaturation ⧸ H.subgroupOf H.powSaturation) :=
  have : Group.FG H.powSaturation := (Group.fg_iff_subgroup_fg H.powSaturation).2 hfg
  have : Group.FG (H.powSaturation ⧸ H.subgroupOf H.powSaturation) :=
    Group.fg_of_surjective (QuotientGroup.mk'_surjective _)
  CommGroup.finite_of_fg_isMulTorsion _ H.isMulTorsion_quotient_powSaturation

/-- The saturation quotient `H.powSaturation ⧸ H.subgroupOf H.powSaturation` is subsingleton iff
`H` equals its positive-power saturation. -/
@[to_additive
/-- The saturation quotient `H.nsmulSaturation ⧸ H.addSubgroupOf H.nsmulSaturation` is subsingleton
iff `H` equals its positive-multiple saturation. -/]
theorem subsingleton_quotient_powSaturation_iff :
    Subsingleton (H.powSaturation ⧸ H.subgroupOf H.powSaturation) ↔ H = H.powSaturation := by
  rw [QuotientGroup.subsingleton_iff, Subgroup.subgroupOf_eq_top]
  exact ⟨fun h ↦ le_antisymm H.le_powSaturation h, fun h ↦ h.ge⟩

end Subgroup
