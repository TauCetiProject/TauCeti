/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Ring
import TauCeti.RingTheory.LocalRing.Basic

/-!
# The unit filtration of a local ring and its graded pieces

For a commutative local ring `R` with maximal ideal `𝔪` and residue field `k`, the **unit
filtration** is the decreasing family of subgroups

`unitFiltration R n = {u : Rˣ | (u : R) - 1 ∈ 𝔪 ^ n}`

of `Rˣ`, with `U(R, 0) = Rˣ` and `U(R, n) = 1 + 𝔪 ^ n` for `n ≥ 1`. This file defines the
filtration directly on `Rˣ`, without a fraction field or completeness assumption, and identifies
its successive quotients `U(R, n) / U(R, n + 1)`:

* At depth zero, reduction modulo `𝔪` gives a canonical isomorphism
  `U(R, 0) / U(R, 1) ≃* kˣ`.
* At positive depth `n + 1`, subtracting one gives a canonical isomorphism
  `U(R, n + 1) / U(R, n + 2) ≃* Multiplicative (𝔪 ^ (n + 1) / 𝔪 ^ (n + 2))`.
* When `R` is a discrete valuation ring and `π` is a uniformizer, composing with
  `TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer` identifies the additive group of
  `U(R, n + 1) / U(R, n + 2)` with the residue field `k`, sending the class of `1 + y * π ^ (n + 1)`
  to the residue of `y`; replacing `π` by `π' = π * a` multiplies the coordinate relative to `π'`
  by the residue of `a ^ (n + 1)`.

## Main definitions

* `TauCeti.IsLocalRing.MaximalIdealGraded R n`: the `n`-th graded piece `𝔪 ^ n / 𝔪 ^ (n + 1)` of
  the maximal-ideal filtration.
* `TauCeti.IsLocalRing.unitFiltration R n`: the `n`-th step `{u : Rˣ | (u : R) - 1 ∈ 𝔪 ^ n}` of
  the unit filtration.
* `TauCeti.IsLocalRing.UnitFiltrationGraded R n`: the successive quotient
  `U(R, n) / U(R, n + 1)`.
* `TauCeti.IsLocalRing.unitFiltrationGradedZeroEquivResidueFieldUnits`: the canonical isomorphism
  `U(R, 0) / U(R, 1) ≃* (ResidueField R)ˣ`.
* `TauCeti.IsLocalRing.unitFiltrationGradedSuccEquivMaximalIdealGraded`: the canonical isomorphism
  `U(R, n + 1) / U(R, n + 2) ≃* Multiplicative (MaximalIdealGraded R (n + 1))`.
* `TauCeti.IsLocalRing.unitFiltrationGradedSuccEquivResidueFieldOfUniformizer`: over a discrete
  valuation ring, the additive isomorphism `Additive (U(R, n + 1) / U(R, n + 2)) ≃+ ResidueField R`
  determined by a uniformizer.

## Main results

* `TauCeti.IsLocalRing.unitFiltration_zero` and `TauCeti.IsLocalRing.unitFiltration_antitone`:
  the filtration starts at `⊤` and decreases.
* `TauCeti.IsLocalRing.unitFiltrationGradedZeroEquivResidueFieldUnits_mk`: the depth-zero
  equivalence reduces a unit modulo the maximal ideal.
* `TauCeti.IsLocalRing.unitFiltrationGradedSuccEquivMaximalIdealGraded_mk`: the positive-depth
  equivalence sends a class to the class of `u - 1`.
* `TauCeti.IsLocalRing.unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue`:
  if `u - 1 = y * π ^ (n + 1)`, the uniformizer coordinate of the class of `u` is `residue R y`.
* `TauCeti.IsLocalRing.unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_change`: changing
  the uniformizer scales the coordinate by the residue of the `(n + 1)`-st power of the change unit.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section
noncomputable section

open IsLocalRing

namespace TauCeti

namespace IsLocalRing

section LocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The `n`-th graded piece `𝔪 ^ n / 𝔪 ^ (n + 1)` of the maximal-ideal filtration of a commutative
local ring `R`, presented as the quotient of the `R`-module `maximalIdeal R ^ n` by
`maximalIdeal R • ⊤`. -/
abbrev MaximalIdealGraded (n : ℕ) :=
  (maximalIdeal R ^ n : Ideal R) ⧸
    (maximalIdeal R • ⊤ : Submodule R (maximalIdeal R ^ n : Ideal R))

/-- The `n`-th step of the **unit filtration** of a commutative local ring `R`: the subgroup of
units congruent to `1` modulo `𝔪 ^ n`. At `n = 0`, `𝔪 ^ 0 = ⊤`, so `unitFiltration R 0 = ⊤`. -/
def unitFiltration (n : ℕ) : Subgroup Rˣ where
  carrier := {u : Rˣ | (u : R) - 1 ∈ maximalIdeal R ^ n}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have hsplit : ((u * v : Rˣ) : R) - 1 = ((u : R) - 1) * (v : R) + ((v : R) - 1) := by
      rw [Units.val_mul]
      ring
    rw [Set.mem_ofPred_eq, hsplit]
    exact add_mem (Ideal.mul_mem_right (v : R) _ hu) hv
  inv_mem' {u} hu := by
    have hsplit : ((u⁻¹ : Rˣ) : R) - 1 = -(((u : R) - 1) * ((u⁻¹ : Rˣ) : R)) := by
      calc ((u⁻¹ : Rˣ) : R) - 1
          = ((u⁻¹ : Rˣ) : R) - (u : R) * ((u⁻¹ : Rˣ) : R) := by rw [Units.mul_inv]
        _ = -(((u : R) - 1) * ((u⁻¹ : Rˣ) : R)) := by ring
    rw [Set.mem_ofPred_eq, hsplit]
    exact neg_mem (Ideal.mul_mem_right _ _ hu)

variable {R} in
/-- Membership in the `n`-th step of the unit filtration is congruence to `1` modulo `𝔪 ^ n`. -/
@[simp]
theorem mem_unitFiltration_iff {n : ℕ} {u : Rˣ} :
    u ∈ unitFiltration R n ↔ (u : R) - 1 ∈ maximalIdeal R ^ n :=
  (Iff.rfl)

/-- The zeroth step of the unit filtration is the whole unit group `Rˣ`. -/
@[simp]
theorem unitFiltration_zero : unitFiltration R 0 = ⊤ := by
  ext u
  simp

/-- The unit filtration is decreasing. -/
theorem unitFiltration_antitone : Antitone (unitFiltration R) :=
  fun _ _ hmn _ hu ↦ Ideal.pow_le_pow_right hmn hu

/-- The `n`-th graded piece `U(R, n) / U(R, n + 1)` of the unit filtration of a local ring `R`. -/
abbrev UnitFiltrationGraded (n : ℕ) :=
  unitFiltration R n ⧸ (unitFiltration R (n + 1)).subgroupOf (unitFiltration R n)

/-! ### Depth zero -/

/-- Reduction of units of a local ring modulo the maximal ideal, restricted to `U(R, 0)`. -/
def unitFiltrationZeroToResidueFieldUnits :
    unitFiltration R 0 →* (ResidueField R)ˣ :=
  (Units.map (residue R).toMonoidHom).comp (unitFiltration R 0).subtype

variable {R} in
/-- Reduction on `U(R, 0)` applies `Units.map (residue R).toMonoidHom` to the underlying unit. -/
@[simp]
theorem unitFiltrationZeroToResidueFieldUnits_apply (u : unitFiltration R 0) :
    unitFiltrationZeroToResidueFieldUnits R u = Units.map (residue R).toMonoidHom (u : Rˣ) :=
  (rfl)

/-- The kernel of reduction `U(R, 0) → (ResidueField R)ˣ` is `U(R, 1)`. -/
theorem ker_unitFiltrationZeroToResidueFieldUnits :
    (unitFiltrationZeroToResidueFieldUnits R).ker =
      (unitFiltration R 1).subgroupOf (unitFiltration R 0) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_unitFiltration_iff, pow_one,
    unitFiltrationZeroToResidueFieldUnits_apply, Units.ext_iff, Units.coe_map, Units.val_one,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, ← sub_eq_zero, ← map_one (residue R),
    ← map_sub, residue_eq_zero_iff]

/-- Every unit of the residue field lifts to a unit of the local ring. -/
theorem unitFiltrationZeroToResidueFieldUnits_surjective :
    Function.Surjective (unitFiltrationZeroToResidueFieldUnits R) := by
  intro y
  obtain ⟨r, hr⟩ := residue_surjective (y : ResidueField R)
  have hu : IsUnit r := (residue_ne_zero_iff_isUnit r).mp (hr.symm ▸ y.ne_zero)
  refine ⟨⟨hu.unit, by simp⟩, Units.ext ?_⟩
  simpa using hr

/-- **Depth-zero graded piece of the unit filtration.** Reduction modulo the maximal ideal
identifies `U(R, 0) / U(R, 1)` with `(ResidueField R)ˣ`. -/
def unitFiltrationGradedZeroEquivResidueFieldUnits :
    UnitFiltrationGraded R 0 ≃* (ResidueField R)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_unitFiltrationZeroToResidueFieldUnits R).symm).trans <|
    QuotientGroup.quotientKerEquivOfSurjective _
      (unitFiltrationZeroToResidueFieldUnits_surjective R)

variable {R} in
/-- The depth-zero graded equivalence sends the class of a unit to its residue unit. -/
@[simp]
theorem unitFiltrationGradedZeroEquivResidueFieldUnits_mk (u : unitFiltration R 0) :
    unitFiltrationGradedZeroEquivResidueFieldUnits R (QuotientGroup.mk u) =
      Units.map (residue R).toMonoidHom (u : Rˣ) :=
  (rfl)

/-! ### Positive depth -/

variable {R} in
/-- The difference `u - 1` attached to `u ∈ U(R, n + 1)`, as an element of `𝔪 ^ (n + 1)`. -/
def unitFiltrationDifference (n : ℕ) (u : unitFiltration R (n + 1)) :
    (maximalIdeal R ^ (n + 1) : Ideal R) :=
  ⟨((u : Rˣ) : R) - 1, u.2⟩

variable {R} in
/-- The underlying ring element of `unitFiltrationDifference n u` is `u - 1`. -/
@[simp]
theorem coe_unitFiltrationDifference (n : ℕ) (u : unitFiltration R (n + 1)) :
    (unitFiltrationDifference n u : R) = ((u : Rˣ) : R) - 1 :=
  (rfl)

/-- Subtracting one modulo `𝔪 ^ (n + 2)` is a group homomorphism from `U(R, n + 1)` to
`Multiplicative (MaximalIdealGraded R (n + 1))`. -/
def unitFiltrationToMaximalIdealGraded (n : ℕ) :
    unitFiltration R (n + 1) →* Multiplicative (MaximalIdealGraded R (n + 1)) where
  toFun u := Multiplicative.ofAdd (Submodule.Quotient.mk (unitFiltrationDifference n u))
  map_one' := by
    have hdiff : unitFiltrationDifference n (1 : unitFiltration R (n + 1)) = 0 := by
      ext
      simp
    rw [hdiff, Submodule.Quotient.mk_zero, ofAdd_zero]
  map_mul' u v := by
    rw [← ofAdd_add, ← Submodule.Quotient.mk_add]
    refine congrArg Multiplicative.ofAdd ?_
    rw [Submodule.Quotient.eq,
      Submodule.mem_smul_top_iff (I := maximalIdeal R)
        (maximalIdeal R ^ (n + 1) : Submodule R R), smul_eq_mul]
    have hprod : (((u : Rˣ) : R) - 1) * (((v : Rˣ) : R) - 1) ∈
        maximalIdeal R * maximalIdeal R ^ (n + 1) := by
      rw [← pow_succ']
      exact Ideal.pow_le_pow_right (by omega : n + 2 ≤ (n + 1) + (n + 1)) <|
        by simpa only [← pow_add] using
          Ideal.mul_mem_mul (mem_unitFiltration_iff.mp u.2) (mem_unitFiltration_iff.mp v.2)
    convert hprod using 1
    simp only [Submodule.coe_sub, Submodule.coe_add, coe_unitFiltrationDifference,
      Subgroup.coe_mul, Units.val_mul]
    ring

variable {R} in
/-- The positive-depth homomorphism sends `u` to the class of `u - 1`. -/
@[simp]
theorem unitFiltrationToMaximalIdealGraded_apply (n : ℕ) (u : unitFiltration R (n + 1)) :
    unitFiltrationToMaximalIdealGraded R n u =
      Multiplicative.ofAdd (Submodule.Quotient.mk (unitFiltrationDifference n u)) :=
  (rfl)

/-- The kernel of `unitFiltrationToMaximalIdealGraded R n` is `U(R, n + 2)`. -/
theorem ker_unitFiltrationToMaximalIdealGraded (n : ℕ) :
    (unitFiltrationToMaximalIdealGraded R n).ker =
      (unitFiltration R (n + 2)).subgroupOf (unitFiltration R (n + 1)) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_unitFiltration_iff,
    unitFiltrationToMaximalIdealGraded_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff,
    Submodule.Quotient.mk_eq_zero,
    Submodule.mem_smul_top_iff (I := maximalIdeal R)
      (maximalIdeal R ^ (n + 1) : Submodule R R), smul_eq_mul, ← pow_succ',
    coe_unitFiltrationDifference]

/-- Every class in `𝔪 ^ (n + 1) / 𝔪 ^ (n + 2)` is the image of a unit `1 + a ∈ U(R, n + 1)`. -/
theorem unitFiltrationToMaximalIdealGraded_surjective (n : ℕ) :
    Function.Surjective (unitFiltrationToMaximalIdealGraded R n) := by
  intro x
  induction x using Multiplicative.rec with
  | ofAdd q =>
    induction q using Submodule.Quotient.induction_on with
    | _ a =>
      have ha1 : (a : R) ∈ maximalIdeal R := by
        simpa only [pow_one] using Ideal.pow_le_pow_right (Nat.succ_pos n) a.2
      have hunit : IsUnit (1 + (a : R)) :=
        TauCeti.isUnit_add_of_isUnit_of_not_isUnit isUnit_one ((mem_maximalIdeal (a : R)).mp ha1)
      have hmem : hunit.unit ∈ unitFiltration R (n + 1) := by
        rw [mem_unitFiltration_iff, IsUnit.unit_spec, add_sub_cancel_left]
        exact a.2
      refine ⟨⟨hunit.unit, hmem⟩, ?_⟩
      rw [unitFiltrationToMaximalIdealGraded_apply]
      refine congrArg Multiplicative.ofAdd (congrArg Submodule.Quotient.mk (Subtype.ext ?_))
      simp

/-- **Positive-depth graded pieces of the unit filtration.** Subtracting one identifies
`U(R, n + 1) / U(R, n + 2)` with the multiplicative copy of `𝔪 ^ (n + 1) / 𝔪 ^ (n + 2)`. -/
def unitFiltrationGradedSuccEquivMaximalIdealGraded (n : ℕ) :
    UnitFiltrationGraded R (n + 1) ≃* Multiplicative (MaximalIdealGraded R (n + 1)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_unitFiltrationToMaximalIdealGraded R n).symm).trans <|
    QuotientGroup.quotientKerEquivOfSurjective _
      (unitFiltrationToMaximalIdealGraded_surjective R n)

variable {R} in
/-- The positive-depth graded equivalence sends the class of `u` to the class of `u - 1`. -/
@[simp]
theorem unitFiltrationGradedSuccEquivMaximalIdealGraded_mk (n : ℕ)
    (u : unitFiltration R (n + 1)) :
    unitFiltrationGradedSuccEquivMaximalIdealGraded R n (QuotientGroup.mk u) =
      Multiplicative.ofAdd (Submodule.Quotient.mk (unitFiltrationDifference n u)) :=
  (rfl)

end LocalRing

section DiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **Uniformizer coordinates on positive-depth unit-filtration quotients.** Over a discrete
valuation ring `R`, fixing a uniformizer `π` identifies `Additive (U(R, n + 1) / U(R, n + 2))`
with the additive residue field `ResidueField R`, carrying the class of `1 + y * π ^ (n + 1)` to
the residue of `y`. -/
def unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (n : ℕ) (π : R)
    (hπ : Irreducible π) :
    Additive (UnitFiltrationGraded R (n + 1)) ≃+ ResidueField R :=
  (unitFiltrationGradedSuccEquivMaximalIdealGraded R n).toAdditive.trans <|
    (AddEquiv.additiveMultiplicative (MaximalIdealGraded R (n + 1))).trans <|
      (TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)).symm.toAddEquiv

/-- The uniformizer coordinate of the class of `u ∈ U(R, n + 1)` maps back to the class of `u - 1`
in `𝔪 ^ (n + 1) / 𝔪 ^ (n + 2)` under multiplication by `π ^ (n + 1)`. -/
@[simp]
theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk (n : ℕ) (π : R)
    (hπ : Irreducible π) (u : unitFiltration R (n + 1)) :
    TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)
        (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ
          (Additive.ofMul (QuotientGroup.mk u))) =
      Submodule.Quotient.mk (unitFiltrationDifference n u) := by
  rw [unitFiltrationGradedSuccEquivResidueFieldOfUniformizer]
  simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
    unitFiltrationGradedSuccEquivMaximalIdealGraded_mk]
  exact LinearEquiv.apply_symm_apply _ _

/-- If `u - 1 = y * π ^ (n + 1)`, then the uniformizer coordinate of the class of `u` is the
residue of `y`. -/
theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue (n : ℕ)
    (π : R) (hπ : Irreducible π) (u : unitFiltration R (n + 1)) (y : R)
    (huy : ((u : Rˣ) : R) - 1 = y * π ^ (n + 1)) :
    unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ
        (Additive.ofMul (QuotientGroup.mk u)) = residue R y := by
  apply (TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)).injective
  rw [unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk,
    TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext huy)

/-- Replacing `π` by `π' = π * a` scales the uniformizer coordinate relative to `π'` by the
residue of `a ^ (n + 1)`. -/
theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_change (n : ℕ) (π π' : R)
    (hπ : Irreducible π) (hπ' : Irreducible π')
    (x : Additive (UnitFiltrationGraded R (n + 1))) :
    unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ x =
      residue R (TauCeti.uniformizerChangeUnit π π' hπ hπ' : R) ^ (n + 1) *
        unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π' hπ' x :=
  TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer_symm_change π π' hπ hπ' (n + 1) _

end DiscreteValuationRing

end IsLocalRing

end TauCeti
