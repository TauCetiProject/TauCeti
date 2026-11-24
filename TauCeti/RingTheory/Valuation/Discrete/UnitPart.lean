/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.Discrete.Order

/-!
# Unit parts for discrete valuations

For an integer-valued valuation `v` and a field unit `t` of order one, `v.unitPart t ht`
is the homomorphism sending `f` to `f * t ^ (-v.ord f)` in the unit subgroup of the
valuation ring. It retracts the inclusion of that subgroup and gives the unique
decomposition of a field unit into an integer power of `t` and a valuation-ring unit.

`v.unitPartUnits t ht` transports the same homomorphism to actual units of the valuation
ring using `ValuationSubring.unitGroupMulEquiv`. These units can be reduced to the residue
field when constructing tame symbols. Changing the parameter multiplies the unit part
by the corresponding negative power of the unit relating the parameters.

## References

* C. Weibel, *The K-book*, Lemma III.6.3 and the proof of Theorem III.7.3.
-/

public section

open scoped WithZero

namespace Valuation

variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)

/-- The unit part of a field unit relative to an order-one parameter, as a homomorphism
to the unit subgroup of the valuation ring. -/
noncomputable def unitPart (t : Fˣ) (ht : v.ord (t : F) = 1) :
    Fˣ →* v.valuationSubring.unitGroup where
  toFun f := ⟨f * t ^ (-v.ord (f : F)), by
    rw [mem_unitGroup_iff_ord_eq_zero, Units.val_mul, ord_units_mul]
    simp [Units.val_zpow_eq_zpow_val, ht]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' f g := Subtype.ext (by
    simp only [Units.val_mul, ord_units_mul, neg_add, zpow_add, Subgroup.coe_mul]
    ac_rfl)

/-- The field-unit value of the unit part. -/
@[simp]
theorem coe_unitPart (t : Fˣ) (ht : v.ord (t : F) = 1) (f : Fˣ) :
    (v.unitPart t ht f : Fˣ) = f * t ^ (-v.ord (f : F)) := (rfl)

/-- A field unit is its parameter power times its unit part. -/
theorem eq_zpow_mul_unitPart (t : Fˣ) (ht : v.ord (t : F) = 1) (f : Fˣ) :
    f = t ^ v.ord (f : F) * (v.unitPart t ht f : Fˣ) := by
  simp [mul_left_comm]

/-- The unit part is characterized by the parameter-power decomposition. -/
theorem unitPart_eq_iff (t : Fˣ) (ht : v.ord (t : F) = 1) (f : Fˣ)
    (u : v.valuationSubring.unitGroup) :
    v.unitPart t ht f = u ↔ f = t ^ v.ord (f : F) * (u : Fˣ) := by
  rw [← Subtype.coe_inj, coe_unitPart]
  simp [zpow_neg, mul_inv_eq_iff_eq_mul, mul_comm]

/-- The unit-part homomorphism retracts the valuation-ring unit subgroup. -/
@[simp]
theorem unitPart_coe (t : Fˣ) (ht : v.ord (t : F) = 1)
    (u : v.valuationSubring.unitGroup) : v.unitPart t ht (u : Fˣ) = u := by
  have hu := (v.mem_unitGroup_iff_ord_eq_zero (u : Fˣ)).mp u.property
  apply Subtype.ext
  simp [hu]

/-- The parameter has trivial unit part. -/
@[simp]
theorem unitPart_self (t : Fˣ) (ht : v.ord (t : F) = 1) : v.unitPart t ht t = 1 := by
  apply Subtype.ext
  simp [ht]

/-- Multiplying the parameter by a valuation-ring unit changes unit parts by its negative
order power. -/
theorem unitPart_mul_coe (t : Fˣ) (ht : v.ord (t : F) = 1)
    (u : v.valuationSubring.unitGroup) (f : Fˣ) :
    v.unitPart (t * (u : Fˣ)) ((v.ord_mul_coe_unitGroup (t : F) u).trans ht) f =
      v.unitPart t ht f * u ^ (-v.ord (f : F)) := by
  apply Subtype.ext
  simp [mul_zpow, mul_comm, mul_assoc]

/-- Unit parts as actual units of the valuation ring, for applying the residue map. -/
noncomputable def unitPartUnits (t : Fˣ) (ht : v.ord (t : F) = 1) :
    Fˣ →* v.valuationSubringˣ :=
  v.valuationSubring.unitGroupMulEquiv.toMonoidHom.comp (v.unitPart t ht)

/-- The ring-unit and subgroup versions of the unit part agree under the canonical equivalence. -/
theorem unitPartUnits_apply (t : Fˣ) (ht : v.ord (t : F) = 1) (f : Fˣ) :
    v.unitPartUnits t ht f = v.valuationSubring.unitGroupMulEquiv (v.unitPart t ht f) := (rfl)

/-- The field value of the ring-unit version of the unit part. -/
@[simp]
theorem coe_unitPartUnits (t : Fˣ) (ht : v.ord (t : F) = 1) (f : Fˣ) :
    ((v.unitPartUnits t ht f : v.valuationSubring) : F) =
      (f : F) * (t : F) ^ (-v.ord (f : F)) := by
  simp [unitPartUnits_apply, Units.val_zpow_eq_zpow_val]

/-- The ring-unit version is uniquely characterized by its field-value decomposition. -/
theorem unitPartUnits_eq_iff (t : Fˣ) (ht : v.ord (t : F) = 1) (f : Fˣ)
    (u : v.valuationSubringˣ) :
    v.unitPartUnits t ht f = u ↔
      (f : F) = (t : F) ^ v.ord (f : F) * (u : F) := by
  rw [Units.ext_iff, Subtype.ext_iff, coe_unitPartUnits]
  rw [zpow_neg, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ t.ne_zero), mul_comm]

/-- The ring-unit version retracts the natural embedding of valuation-ring units. -/
@[simp]
theorem unitPartUnits_coe (t : Fˣ) (ht : v.ord (t : F) = 1) (u : v.valuationSubringˣ) :
    v.unitPartUnits t ht (v.valuationSubring.unitGroupMulEquiv.symm u : Fˣ) = u := by
  simp [unitPartUnits_apply]

/-- The parameter has trivial ring-unit part. -/
@[simp]
theorem unitPartUnits_self (t : Fˣ) (ht : v.ord (t : F) = 1) :
    v.unitPartUnits t ht t = 1 := by
  simp [unitPartUnits_apply]

end Valuation
