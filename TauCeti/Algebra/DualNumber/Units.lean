/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.Algebra.DualNumber.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Units of the dual numbers modulo scalars

Over a commutative ring `R`, a dual number `a + bε` is a unit exactly when `a` is, and then
`a + bε = a (1 + (b / a) ε)`. The infinitesimal units `1 + cε` multiply by adding the
coefficients `c` (`TauCeti.dualNumberUnit_mul`), so the map `a + bε ↦ b / a` is a homomorphism
from the units of `R[ε]` onto the additive group of `R` whose kernel is the group `Rˣ` of scalar
units. Hence

  `R[ε]ˣ ⧸ Rˣ ≃* R`,

written multiplicatively, with inverse `b ↦ 1 + bε`. This is the group `1 + tR` of principal
units of the truncated polynomial ring `R[t] ⧸ (t²)`, which measures, for instance, the units of
`R[t] ⧸ (t²)` that do not come from `R`.

## Main definitions

* `TauCeti.dualNumberUnitsQuotientEquiv R`: the isomorphism `R[ε]ˣ ⧸ Rˣ ≃* Multiplicative R`,
  `a + bε ↦ b / a`.

## Main results

* `TauCeti.isMulCommutative_units_dualNumber`: the units of `R[ε]` commute, so every subgroup of
  `R[ε]ˣ` is normal.
* `TauCeti.dualNumber_fst_mul_fst_inv`: the scalar part of the inverse of a unit of `R[ε]` is the
  inverse of its scalar part.
* `TauCeti.dualNumberUnitsQuotientEquiv_mk`: the class of a unit `u` goes to
  `u.snd * (u⁻¹).fst`, which is `b / a` for `u = a + bε`.
* `TauCeti.dualNumberUnitsQuotientEquiv_symm_apply`: the inverse sends `b` to the class of
  `1 + bε`.
-/

public section

open TrivSqZeroExt

namespace TauCeti

/-- The units of the dual numbers over a commutative semiring commute. Instance search does not
find this through the commutative semiring structure of `R[ε]` unaided, so it is recorded here; it
makes every subgroup of `R[ε]ˣ` normal. -/
instance isMulCommutative_units_dualNumber {R : Type*} [CommSemiring R] :
    IsMulCommutative (DualNumber R)ˣ :=
  CommMagma.to_isCommutative (G := (DualNumber R)ˣ)

/-- The scalar part of the inverse of a unit of `R[ε]` is the inverse of its scalar part. -/
theorem dualNumber_fst_mul_fst_inv {R : Type*} [Semiring R] (u : (DualNumber R)ˣ) :
    fst (u : DualNumber R) * fst ((u⁻¹ : (DualNumber R)ˣ) : DualNumber R) = 1 := by
  rw [← fst_mul, Units.mul_inv, fst_one]

variable (R : Type*) [CommRing R]

/-- The homomorphism `a + bε ↦ b / a` from the units of `R[ε]` to the additive group of `R`. -/
private def unitsSndMulFstInv : (DualNumber R)ˣ →* Multiplicative R where
  toFun u :=
    Multiplicative.ofAdd (snd (u : DualNumber R) * fst ((u⁻¹ : (DualNumber R)ˣ) : DualNumber R))
  map_one' := by simp
  map_mul' u v := by
    have hu := dualNumber_fst_mul_fst_inv u
    have hv := dualNumber_fst_mul_fst_inv v
    rw [← ofAdd_add, mul_inv_rev, Units.val_mul, Units.val_mul, DualNumber.snd_mul, fst_mul]
    congr 1
    linear_combination
      (snd (v : DualNumber R) * fst ((v⁻¹ : (DualNumber R)ˣ) : DualNumber R)) * hu +
        (snd (u : DualNumber R) * fst ((u⁻¹ : (DualNumber R)ˣ) : DualNumber R)) * hv

/-- The kernel of `a + bε ↦ b / a` is the group of scalar units. -/
private theorem ker_unitsSndMulFstInv :
    (unitsSndMulFstInv R).ker =
      (Units.map (algebraMap R (DualNumber R) : R →* DualNumber R)).range := by
  ext u
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro h
    have hsnd : snd (u : DualNumber R) = 0 := by
      have h' : snd (u : DualNumber R) * fst ((u⁻¹ : (DualNumber R)ˣ) : DualNumber R) = 0 :=
        congrArg Multiplicative.toAdd h
      simpa [mul_assoc, mul_comm (fst ((u⁻¹ : (DualNumber R)ˣ) : DualNumber R)),
        dualNumber_fst_mul_fst_inv] using congrArg (· * fst (u : DualNumber R)) h'
    refine ⟨Units.map (fstHom R R R : DualNumber R →* R) u, Units.ext ?_⟩
    ext
    · simp [algebraMap_eq_inl]
    · simp [algebraMap_eq_inl, hsnd]
  · rintro ⟨a, rfl⟩
    simp [unitsSndMulFstInv, algebraMap_eq_inl]

/-- `b ↦ 1 + bε` is a right inverse of `a + bε ↦ b / a`. -/
private theorem unitsSndMulFstInv_dualNumberUnit (b : Multiplicative R) :
    unitsSndMulFstInv R (dualNumberUnit b.toAdd) = b := by
  simp [unitsSndMulFstInv]

/-- **The units of the dual numbers modulo the scalar units are the additive group of `R`.** The
class of a unit `a + bε` goes to `b / a`, and the inverse sends `b` to the class of `1 + bε`. -/
noncomputable def dualNumberUnitsQuotientEquiv :
    (DualNumber R)ˣ ⧸ (Units.map (algebraMap R (DualNumber R) : R →* DualNumber R)).range ≃*
      Multiplicative R :=
  (QuotientGroup.quotientMulEquivOfEq (ker_unitsSndMulFstInv R).symm).trans
    (QuotientGroup.quotientKerEquivOfRightInverse _ _ (unitsSndMulFstInv_dualNumberUnit R))

/-- The class of a unit `u = a + bε` goes to `b / a`, written as `u.snd * (u⁻¹).fst`. -/
@[simp]
theorem dualNumberUnitsQuotientEquiv_mk (u : (DualNumber R)ˣ) :
    dualNumberUnitsQuotientEquiv R u = Multiplicative.ofAdd
      (snd (u : DualNumber R) * fst ((u⁻¹ : (DualNumber R)ˣ) : DualNumber R)) := by
  rw [dualNumberUnitsQuotientEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk,
    unitsSndMulFstInv, MonoidHom.coe_mk, OneHom.coe_mk]

/-- The inverse of `TauCeti.dualNumberUnitsQuotientEquiv` sends `b` to the class of `1 + bε`. -/
@[simp]
theorem dualNumberUnitsQuotientEquiv_symm_apply (b : Multiplicative R) :
    (dualNumberUnitsQuotientEquiv R).symm b = dualNumberUnit b.toAdd := by
  rw [MulEquiv.symm_apply_eq, dualNumberUnitsQuotientEquiv_mk]
  simp

end TauCeti
