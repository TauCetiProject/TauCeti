/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.Discrete.Order
import TauCeti.RingTheory.Valuation.UnitGroup

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

`v.unitPartResidue t ht` reduces the unit part to the residue field: it sends `f = t ^ i u`
to `ū`. These are the residue-field units through which the tame symbol and the residue maps of
Milnor K-theory are computed. Along a valuation extension `E / F`, the reduced unit part of `f ∈ Fˣ`
relative to an order-one `s ∈ Eˣ` is the image of that relative to `t` times `c ^ ord_v f`, where
`c` is the reduced unit part of `t` relative to `s` (`Valuation.unitPartResidue_map_algebraMap`).

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

/-- The **reduced unit part** `ū` of a field unit `f = t ^ ord_v f · u` relative to an order-one
parameter `t`: the residue of its unit part `u = v.unitPart t ht f`, a unit of the residue field
of the valuation ring. -/
noncomputable def unitPartResidue (t : Fˣ) (ht : v.ord (t : F) = 1) :
    Fˣ →* (IsLocalRing.ResidueField v.valuationSubring)ˣ :=
  v.valuationSubring.unitGroupToResidueFieldUnits.comp (v.unitPart t ht)

theorem unitPartResidue_apply (t : Fˣ) (ht : v.ord (t : F) = 1) (f : Fˣ) :
    v.unitPartResidue t ht f =
      v.valuationSubring.unitGroupToResidueFieldUnits (v.unitPart t ht f) :=
  (rfl)

/-- The reduced unit part of `f` is the residue of any element of the valuation ring whose value
is the unit part `f * t ^ (-ord_v f)`. -/
theorem coe_unitPartResidue_eq_residue (t : Fˣ) (ht : v.ord (t : F) = 1) {f : Fˣ}
    {x : v.valuationSubring} (hx : (x : F) = (v.unitPart t ht f : Fˣ)) :
    (v.unitPartResidue t ht f : IsLocalRing.ResidueField v.valuationSubring) =
      IsLocalRing.residue v.valuationSubring x := by
  rw [unitPartResidue_apply, ValuationSubring.coe_unitGroupToResidueFieldUnits_apply,
    ← IsLocalRing.residue_def]
  exact congrArg _ (Subtype.ext hx.symm)

/-- The reduced unit part of a unit of the valuation ring is its residue. -/
@[simp]
theorem unitPartResidue_coe (t : Fˣ) (ht : v.ord (t : F) = 1)
    (u : v.valuationSubring.unitGroup) :
    v.unitPartResidue t ht u = v.valuationSubring.unitGroupToResidueFieldUnits u := by
  rw [unitPartResidue_apply, unitPart_coe]

/-- The reduced unit part of a field unit of order zero is its residue. -/
theorem unitPartResidue_of_ord_eq_zero (t : Fˣ) (ht : v.ord (t : F) = 1) {f : Fˣ}
    (hf : v.ord (f : F) = 0) :
    v.unitPartResidue t ht f = v.valuationSubring.unitGroupToResidueFieldUnits
      ⟨f, (v.mem_unitGroup_iff_ord_eq_zero f).2 hf⟩ :=
  v.unitPartResidue_coe t ht ⟨f, _⟩

/-- **Reduced unit parts along a valuation extension.** Let `w` extend `v` along `E / F`, and let
`t ∈ Fˣ` and `s ∈ Eˣ` have order one. For `f ∈ Fˣ` the reduced unit part of `f` relative to `s` is
the image of its reduced unit part relative to `t` under the residue-field embedding `k_v → k_w`,
times `c ^ ord_v f`, where `c` is the reduced unit part of `t` relative to `s`. -/
theorem unitPartResidue_map_algebraMap {E : Type*} [Field E] [Algebra F E]
    (w : Valuation E ℤᵐ⁰) [v.HasExtension w] (t : Fˣ) (ht : v.ord (t : F) = 1) (s : Eˣ)
    (hs : w.ord (s : E) = 1) (f : Fˣ) :
    w.unitPartResidue s hs (Units.map (algebraMap F E : F →* E) f) =
      Units.map (algebraMap (IsLocalRing.ResidueField v.valuationSubring)
        (IsLocalRing.ResidueField w.valuationSubring) : _ →* _) (v.unitPartResidue t ht f) *
        w.unitPartResidue s hs (Units.map (algebraMap F E : F →* E) t) ^ v.ord (f : F) := by
  let u : w.valuationSubring.unitGroup :=
    ⟨_, (HasExtension.map_mem_unitGroup_iff v w).2 (v.unitPart t ht f).property⟩
  have hf : Units.map (algebraMap F E : F →* E) f =
      Units.map (algebraMap F E : F →* E) t ^ v.ord (f : F) * (u : Eˣ) := by
    conv_lhs => rw [v.eq_zpow_mul_unitPart t ht f]
    rw [map_mul, map_zpow]
  rw [hf, map_mul, map_zpow, mul_comm, unitPartResidue_coe]
  exact congrArg (· * _)
    (HasExtension.unitGroupToResidueFieldUnits_map v w (v.unitPart t ht f).property)

/-- A field unit of order zero has reduced unit part `1` exactly when it is a principal unit. -/
theorem unitPartResidue_eq_one_iff_of_ord_eq_zero (t : Fˣ) (ht : v.ord (t : F) = 1) {f : Fˣ}
    (hord : v.ord (f : F) = 0) :
    v.unitPartResidue t ht f = 1 ↔ f ∈ v.valuationSubring.principalUnitGroup := by
  rw [v.unitPartResidue_of_ord_eq_zero t ht hord, ← MonoidHom.mem_ker,
    ValuationSubring.ker_unitGroupToResidueFieldUnits, Subgroup.mem_comap]
  exact Iff.rfl

/-- If `r + s = 1` and `r` has positive order, then `s` has reduced unit part `1`. -/
theorem unitPartResidue_eq_one_of_add_eq_one (t : Fˣ) (ht : v.ord (t : F) = 1) {r s : Fˣ}
    (h : (r : F) + s = 1) (hr : 0 < v.ord (r : F)) : v.unitPartResidue t ht s = 1 := by
  rw [unitPartResidue_of_ord_eq_zero _ _ _ (v.ord_eq_zero_of_add_eq_one_of_ord_pos h hr)]
  exact v.unitGroupToResidueFieldUnits_eq_one_of_add_eq_one h hr

/-- The parameter has trivial reduced unit part. -/
@[simp]
theorem unitPartResidue_self (t : Fˣ) (ht : v.ord (t : F) = 1) : v.unitPartResidue t ht t = 1 := by
  rw [unitPartResidue_apply, unitPart_self, map_one]

/-- The reduced unit part of `-f` is `-ū`. -/
@[simp]
theorem unitPartResidue_neg (t : Fˣ) (ht : v.ord (t : F) = 1) (f : Fˣ) :
    v.unitPartResidue t ht (-f) = -v.unitPartResidue t ht f := by
  rw [← neg_one_mul, map_mul, ← neg_one_mul (v.unitPartResidue t ht f)]
  congr 1
  simpa using v.unitPartResidue_coe t ht ⟨-1, v.valuationSubring.neg_one_mem_unitGroup⟩

/-- Changing the parameter from `t` to `t' = c t` divides the reduced unit part of `f` by
`γ ^ ord_v f`, where `γ`, the residue of `c`, is the reduced unit part of `t'` relative to `t`. -/
theorem unitPartResidue_eq_mul_zpow (t : Fˣ) (ht : v.ord (t : F) = 1) (t' : Fˣ)
    (ht' : v.ord (t' : F) = 1) (f : Fˣ) :
    v.unitPartResidue t' ht' f =
      v.unitPartResidue t ht f * v.unitPartResidue t ht t' ^ (-v.ord (f : F)) := by
  rw [unitPartResidue_apply, ← v.unitPartResidue_coe t ht, coe_unitPart, map_mul, map_zpow]

end Valuation
