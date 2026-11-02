/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Henselian
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# The units congruent to one modulo an ideal

For an ideal `I` of a ring `R`, the units `u` with `u - 1 ∈ I` form a subgroup of `Rˣ`, the
principal unit group of `I`. The name is borrowed from Mathlib's
`ValuationSubring.principalUnitGroup`, which for a valuation subring `A` of a field `K` is a
subgroup of `Kˣ`; under `ValuationSubring.unitGroupMulEquiv` it corresponds to this subgroup of
`Aˣ` for the maximal ideal of `A`. Here `I` is arbitrary. When `I` consists of topologically
nilpotent elements of a complete linearly topologized `ℚ`-algebra, the exponential is an
isomorphism from the additive group of `I` onto this group (`Ideal.expMulEquiv`).

The principal unit group of `I` is the kernel of reduction of units modulo `I`, and when `I` lies
in the Jacobson radical this reduction is surjective, so that `Rˣ ⧸ (1 + I) ≃ (R ⧸ I)ˣ`. For ideals
`J' ≤ J` with `J * J ≤ J'` and `J` in the Jacobson radical, the map `1 + x ↦ x` identifies
`(1 + J) ⧸ (1 + J')` with the additive group `J ⧸ J'`, because
`(1 + x)(1 + y) = 1 + (x + y) + x y` with `x y ∈ J'`. Without `J' ≤ J`, the same map identifies
`(1 + J) ⧸ ((1 + J) ∩ (1 + J'))` with `J ⧸ (J ∩ J')`; these are the quotients the API states, via
`Subgroup.subgroupOf` and `Submodule.comap J.subtype J'`. Applied to the powers of an ideal `I` in
the Jacobson radical, this gives the filtration of `1 + I` by the subgroups `1 + I ^ n`, whose
successive quotients are the additive groups `I ^ n ⧸ I ^ (n + 1)`.
When `I ^ n = 0` the filtration reaches the trivial group at step `n` (`principalUnitGroup_bot`),
so `1 + I` is an iterated extension of additive groups.

## Main definitions

* `Ideal.principalUnitGroup`: the units `u` with `u - 1 ∈ I`.
* `Ideal.unitsQuotientPrincipalUnitGroupEquiv`: for `I` in the Jacobson radical,
  `Rˣ ⧸ (1 + I) ≃* (R ⧸ I)ˣ`.
* `Ideal.principalUnitGroupToQuotient`: for `J * J ≤ J'`, the homomorphism `1 + x ↦ x mod J'`
  from `1 + J` to the additive group of `J ⧸ (J ∩ J')`, which is `J ⧸ J'` when `J' ≤ J`.
* `Ideal.principalUnitGroupQuotientEquiv`: for `J * J ≤ J'` and `J` in the Jacobson radical,
  `(1 + J) ⧸ ((1 + J) ∩ (1 + J')) ≃* J ⧸ (J ∩ J')`, which reads `(1 + J) ⧸ (1 + J') ≃* J ⧸ J'`
  when `J' ≤ J`.
* `Ideal.principalUnitGroupPowQuotientEquiv`: the successive quotients
  `(1 + I ^ (n + 1)) ⧸ (1 + I ^ (n + 2)) ≃* I ^ (n + 1) ⧸ I ^ (n + 2)` of the filtration by powers.

## Main results

* `Ideal.principalUnitGroup_ker`: the principal unit group of the kernel of a ring homomorphism
  is the kernel of the induced map on units.
* `Ideal.unitsMap_quotientMk_surjective`: reduction of units modulo an ideal in the Jacobson
  radical is surjective.
* `Ideal.principalUnitGroup_pow_antitone`: the subgroups `1 + I ^ n` decrease with `n`.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §2, for the filtration of the units of a local ring.
-/

public section

namespace Ideal

variable {R : Type*} [Ring R]

variable (I : Ideal R) in
/-- The principal unit group of an ideal `I`: the units `u` with `u - 1 ∈ I`. -/
def principalUnitGroup : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ I}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have huv : ((u * v : Rˣ) : R) - 1 = u * ((v : R) - 1) + ((u : R) - 1) := by
      rw [Units.val_mul, mul_sub, mul_one, sub_add_sub_cancel]
    rw [Set.mem_ofPred_eq, huv]
    exact add_mem (I.mul_mem_left _ hv) hu
  inv_mem' {u} hu := by
    have hu' : ((u⁻¹ : Rˣ) : R) - 1 = -(↑u⁻¹ * ((u : R) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [Set.mem_ofPred_eq, hu']
    exact neg_mem (I.mul_mem_left _ hu)

@[simp]
theorem mem_principalUnitGroup {I : Ideal R} {u : Rˣ} :
    u ∈ I.principalUnitGroup ↔ (u : R) - 1 ∈ I :=
  Iff.rfl

theorem principalUnitGroup_mono : Monotone (principalUnitGroup (R := R)) :=
  fun _ _ h _ hu ↦ h hu

@[simp]
theorem principalUnitGroup_top : (⊤ : Ideal R).principalUnitGroup = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ mem_principalUnitGroup.mpr Submodule.mem_top

@[simp]
theorem principalUnitGroup_bot : (⊥ : Ideal R).principalUnitGroup = ⊥ := by
  ext u
  rw [mem_principalUnitGroup, Submodule.mem_bot, sub_eq_zero, Subgroup.mem_bot, Units.val_eq_one]

/-- The principal unit group of the kernel of a ring homomorphism is the kernel of the induced
map on units. -/
theorem principalUnitGroup_ker {S : Type*} [Ring S] (f : R →+* S) :
    (RingHom.ker f).principalUnitGroup = (Units.map f.toMonoidHom).ker := by
  ext u
  simp [mem_principalUnitGroup, sub_eq_zero, Units.ext_iff]

section CommRing

variable {R : Type*} [CommRing R]

theorem principalUnitGroup_pow_antitone (I : Ideal R) :
    Antitone fun n : ℕ ↦ (I ^ n).principalUnitGroup :=
  fun _ _ h ↦ principalUnitGroup_mono (pow_le_pow_right h)

/-- The principal unit group of `I` is the kernel of reduction of units modulo `I`. -/
theorem principalUnitGroup_eq_ker_unitsMap (I : Ideal R) :
    I.principalUnitGroup = (Units.map (Quotient.mk I).toMonoidHom).ker := by
  rw [← principalUnitGroup_ker, mk_ker]

/-- Reduction of units modulo an ideal contained in the Jacobson radical is surjective. -/
theorem unitsMap_quotientMk_surjective {I : Ideal R} (hI : I ≤ jacobson ⊥) :
    Function.Surjective (Units.map (Quotient.mk I).toMonoidHom) :=
  IsLocalRing.surjective_units_map_of_local_ringHom _ Quotient.mk_surjective
    (isLocalHom_of_le_jacobson_bot I hI)

/-- For an ideal `I` contained in the Jacobson radical, the units of `R` modulo the principal
unit group of `I` are the units of `R ⧸ I`. -/
noncomputable def unitsQuotientPrincipalUnitGroupEquiv {I : Ideal R} (hI : I ≤ jacobson ⊥) :
    Rˣ ⧸ I.principalUnitGroup ≃* (R ⧸ I)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq I.principalUnitGroup_eq_ker_unitsMap).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (unitsMap_quotientMk_surjective hI))

@[simp]
theorem unitsQuotientPrincipalUnitGroupEquiv_mk {I : Ideal R} (hI : I ≤ jacobson ⊥) (u : Rˣ) :
    unitsQuotientPrincipalUnitGroupEquiv hI u = Units.map (Quotient.mk I).toMonoidHom u := by
  simp only [unitsQuotientPrincipalUnitGroupEquiv, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk]

/-- For ideals with `J * J ≤ J'`, the map `1 + x ↦ x mod J'` is a homomorphism from the principal
unit group of `J` to the additive group of `J ⧸ (J ∩ J')` (written `Submodule.comap J.subtype J'`;
this is `J ⧸ J'` when `J' ≤ J`): `(1 + x)(1 + y) = 1 + (x + y) + x y` with `x y ∈ J'`. -/
def principalUnitGroupToQuotient (J J' : Ideal R) (h : J * J ≤ J') :
    J.principalUnitGroup →* Multiplicative (J ⧸ Submodule.comap J.subtype J') where
  toFun u := .ofAdd (Submodule.Quotient.mk ⟨((u : Rˣ) : R) - 1, mem_principalUnitGroup.mp u.2⟩)
  map_one' := by
    rw [ofAdd_eq_one, Submodule.Quotient.mk_eq_zero]
    simp
  map_mul' u v := by
    rw [← ofAdd_add, ← Submodule.Quotient.mk_add]
    congr 1
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    convert h (mul_mem_mul (mem_principalUnitGroup.mp u.2) (mem_principalUnitGroup.mp v.2))
      using 1
    simp only [Subgroup.coe_mul, Units.val_mul, Submodule.coe_sub, Submodule.subtype_apply,
      Submodule.coe_add]
    ring

@[simp]
theorem principalUnitGroupToQuotient_apply {J J' : Ideal R} (h : J * J ≤ J')
    (u : J.principalUnitGroup) :
    principalUnitGroupToQuotient J J' h u =
      .ofAdd (Submodule.Quotient.mk ⟨((u : Rˣ) : R) - 1, mem_principalUnitGroup.mp u.2⟩) :=
  (rfl)

theorem ker_principalUnitGroupToQuotient {J J' : Ideal R} (h : J * J ≤ J') :
    (principalUnitGroupToQuotient J J' h).ker =
      J'.principalUnitGroup.subgroupOf J.principalUnitGroup := by
  ext u
  rw [MonoidHom.mem_ker, principalUnitGroupToQuotient_apply, ofAdd_eq_one,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Subgroup.mem_subgroupOf]
  simp

/-- When `J` lies in the Jacobson radical, every element of `J ⧸ (J ∩ J')` is the class of `u - 1`
for a principal unit `u` of `J`: if `x ∈ J`, then `1 + x` is a unit. -/
theorem principalUnitGroupToQuotient_surjective {J J' : Ideal R} (h : J * J ≤ J')
    (hJ : J ≤ jacobson ⊥) : Function.Surjective (principalUnitGroupToQuotient J J' h) := by
  intro q
  obtain ⟨⟨x, hx⟩, hq⟩ := Submodule.Quotient.mk_surjective _ q.toAdd
  have hunit : IsUnit (x * 1 + 1) := mem_jacobson_bot.mp (hJ hx) 1
  refine ⟨⟨hunit.unit, ?_⟩, ?_⟩
  · simpa [mem_principalUnitGroup] using hx
  · apply Multiplicative.toAdd.injective
    rw [principalUnitGroupToQuotient_apply, toAdd_ofAdd, ← hq]
    congr 2
    simp

/-- For ideals with `J * J ≤ J'` and `J` contained in the Jacobson radical, the quotient of the
principal unit group of `J` by its intersection with that of `J'` is the additive group
`J ⧸ (J ∩ J')`, by `1 + x ↦ x`. When `J' ≤ J` this is `(1 + J) ⧸ (1 + J') ≃* J ⧸ J'`. -/
noncomputable def principalUnitGroupQuotientEquiv {J J' : Ideal R} (h : J * J ≤ J')
    (hJ : J ≤ jacobson ⊥) :
    J.principalUnitGroup ⧸ J'.principalUnitGroup.subgroupOf J.principalUnitGroup ≃*
      Multiplicative (J ⧸ Submodule.comap J.subtype J') :=
  (QuotientGroup.quotientMulEquivOfEq (ker_principalUnitGroupToQuotient h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (principalUnitGroupToQuotient_surjective h hJ))

@[simp]
theorem principalUnitGroupQuotientEquiv_mk {J J' : Ideal R} (h : J * J ≤ J')
    (hJ : J ≤ jacobson ⊥) (u : J.principalUnitGroup) :
    principalUnitGroupQuotientEquiv h hJ u = principalUnitGroupToQuotient J J' h u := by
  simp only [principalUnitGroupQuotientEquiv, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk]

/-- The successive quotients of the filtration of the principal unit group of an ideal `I` in the
Jacobson radical by the principal unit groups of its powers:
`(1 + I ^ (n + 1)) ⧸ (1 + I ^ (n + 2)) ≃* I ^ (n + 1) ⧸ I ^ (n + 2)`, by `1 + x ↦ x`. -/
noncomputable def principalUnitGroupPowQuotientEquiv {I : Ideal R} (hI : I ≤ jacobson ⊥) (n : ℕ) :
    (I ^ (n + 1)).principalUnitGroup ⧸
        (I ^ (n + 2)).principalUnitGroup.subgroupOf (I ^ (n + 1)).principalUnitGroup ≃*
      Multiplicative (↥(I ^ (n + 1)) ⧸ Submodule.comap (I ^ (n + 1)).subtype (I ^ (n + 2))) :=
  principalUnitGroupQuotientEquiv (by rw [← pow_add]; exact pow_le_pow_right (by omega))
    ((pow_le_self n.succ_ne_zero).trans hI)

@[simp]
theorem principalUnitGroupPowQuotientEquiv_mk {I : Ideal R} (hI : I ≤ jacobson ⊥) (n : ℕ)
    (u : (I ^ (n + 1)).principalUnitGroup) :
    principalUnitGroupPowQuotientEquiv hI n u =
      .ofAdd (Submodule.Quotient.mk ⟨((u : Rˣ) : R) - 1, mem_principalUnitGroup.mp u.2⟩) :=
  principalUnitGroupQuotientEquiv_mk _ _ u

end CommRing

end Ideal
