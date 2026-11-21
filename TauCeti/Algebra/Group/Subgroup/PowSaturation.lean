/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import TauCeti.Algebra.Group.Submonoid.NSMulSaturation

/-!
# Positive-power saturation of subgroups

Given a subgroup `H` of a commutative group `G`, its *positive-power saturation* `H.powSaturation`
is the subgroup of elements `g : G` such that `g ^ n ∈ H` for some `n > 0` (additively
`H.nsmulSaturation`). Every element of the quotient `H.powSaturation ⧸ H.subgroupOf H.powSaturation`
has finite order (`Subgroup.isMulTorsion_quotient_powSaturation`), and when `H.powSaturation` is
finitely generated, this quotient is finite (`Subgroup.finite_quotient_powSaturation`).

## Main declarations

* `Subgroup.powSaturation`, `AddSubgroup.nsmulSaturation`: positive-power / positive-multiple
  saturation of a subgroup.
* `Subgroup.isMulTorsion_quotient_powSaturation`,
  `AddSubgroup.isAddTorsion_quotient_nsmulSaturation`: the saturation quotient is torsion.
* `Subgroup.finite_quotient_powSaturation`, `AddSubgroup.finite_quotient_nsmulSaturation`:
  finiteness of the saturation quotient when `H.powSaturation` is finitely generated.

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

/-- Every element of `H.powSaturation ⧸ H.subgroupOf H.powSaturation` has finite order. -/
@[to_additive
/-- Every element of `H.nsmulSaturation ⧸ H.addSubgroupOf H.nsmulSaturation` is torsion. -/]
theorem isMulTorsion_quotient_powSaturation :
    IsMulTorsion (H.powSaturation ⧸ H.subgroupOf H.powSaturation) :=
  fun q ↦ QuotientGroup.induction_on q fun x ↦ by
    obtain ⟨n, hn, hxn⟩ := (mem_powSaturation H).1 x.2
    exact isOfFinOrder_iff_pow_eq_one.2
      ⟨n, hn, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hxn⟩

/-- When `H.powSaturation` is finitely generated, `H` has finite index in `H.powSaturation`. -/
@[to_additive
/-- When `H.nsmulSaturation` is FG, `H` has finite quotient in `H.nsmulSaturation`. -/]
theorem finite_quotient_powSaturation (hfg : H.powSaturation.FG) :
    Finite (H.powSaturation ⧸ H.subgroupOf H.powSaturation) := by
  have : Group.FG H.powSaturation := (Group.fg_iff_subgroup_fg H.powSaturation).2 hfg
  have : Group.FG (H.powSaturation ⧸ H.subgroupOf H.powSaturation) :=
    Group.fg_of_surjective (QuotientGroup.mk'_surjective _)
  exact CommGroup.finite_of_fg_isMulTorsion _ H.isMulTorsion_quotient_powSaturation

end Subgroup
