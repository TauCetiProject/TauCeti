/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Valuation
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic

import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.OddDefect
import TauCeti.NumberTheory.LocalField.UnitsDecomposition

/-!
# The quadratic norm quotient is detected on units

Let `a` have odd quadratic defect exponent. There is then a norm from `K(√a)` of every
normalized valuation. Consequently, every class in the quotient of `Kˣ` by the quadratic norm
subgroup has a representative in the depth-zero unit filtration `U(K, 0)`.

This identifies the full norm quotient with the quotient of `U(K, 0)` by the unit norms. In
particular, their indices agree. This is the reduction from the valuation part to the unit part in
the ramified cases of the quadratic norm-index theorem, especially for a unit radicand of odd
defect.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The map from depth-zero units to the quotient by the quadratic norm subgroup. -/
noncomputable def unitNormQuotientMap (a : Kˣ) :
    unitFiltration K 0 →* Kˣ ⧸ quadraticNormSubgroup (a : K) :=
  (QuotientGroup.mk' (quadraticNormSubgroup (a : K))).comp (unitFiltration K 0).subtype

@[simp]
theorem unitNormQuotientMap_apply (a : Kˣ) (u : unitFiltration K 0) :
    unitNormQuotientMap a u = (u : Kˣ) :=
  by simp [unitNormQuotientMap]

/-- The kernel of the unit-to-norm-quotient map consists exactly of the unit norms. -/
theorem ker_unitNormQuotientMap (a : Kˣ) :
    (unitNormQuotientMap a).ker =
      (quadraticNormSubgroup (a : K)).subgroupOf (unitFiltration K 0) := by
  ext u
  rw [MonoidHom.mem_ker, unitNormQuotientMap_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]

/-- If the quadratic defect exponent of `a` is odd, every norm coset has a representative in
`U(K, 0)`. -/
theorem unitNormQuotientMap_surjective_of_odd_defectExponent {a : Kˣ} {d : ℤ}
    (hd : defectExponent a = d) (hodd : Odd d) :
    Function.Surjective (unitNormQuotientMap a) := by
  intro q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (quadraticNormSubgroup (a : K)) q
  obtain ⟨c, hc, hcval⟩ :=
    exists_mem_quadraticNormSubgroup_toAdd_normalizedValuation_eq_of_odd_defectExponent
      hd hodd (normalizedValuation K b).toAdd
  have hunit : b * c⁻¹ ∈ unitFiltration K 0 := by
    rw [← ker_normalizedValuation, MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, hcval]
    exact sub_self _
  refine ⟨⟨b * c⁻¹, hunit⟩, ?_⟩
  rw [unitNormQuotientMap_apply]
  apply (QuotientGroup.mk'_eq_mk' (N := quadraticNormSubgroup (a : K))).2
  exact ⟨c, hc, by simp⟩

/-- For odd quadratic defect, quotienting the unit group by its unit norms gives the full
quadratic norm quotient. -/
noncomputable def unitNormQuotientEquivOfOddDefectExponent {a : Kˣ} {d : ℤ}
    (hd : defectExponent a = d) (hodd : Odd d) :
    (unitFiltration K 0) ⧸
        (quadraticNormSubgroup (a : K)).subgroupOf (unitFiltration K 0) ≃*
      Kˣ ⧸ quadraticNormSubgroup (a : K) :=
  let f := unitNormQuotientMap a
  let hf := unitNormQuotientMap_surjective_of_odd_defectExponent hd hodd
  (QuotientGroup.quotientMulEquivOfEq (ker_unitNormQuotientMap a).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The quotient equivalence sends the class of a depth-zero unit to the class of the same
element in the full quadratic norm quotient. -/
@[simp]
theorem unitNormQuotientEquivOfOddDefectExponent_mk {a : Kˣ} {d : ℤ}
    (hd : defectExponent a = d) (hodd : Odd d) (u : unitFiltration K 0) :
    unitNormQuotientEquivOfOddDefectExponent hd hodd u = (u : Kˣ) :=
  by
    unfold unitNormQuotientEquivOfOddDefectExponent
    rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
      TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk]
    exact unitNormQuotientMap_apply a u

/-- For odd quadratic defect, the index of the quadratic norm subgroup is already the index of
the unit norms inside `U(K, 0)`. -/
theorem index_subgroupOf_unitFiltration_eq_quadraticNormSubgroup_index_of_odd_defectExponent
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    ((quadraticNormSubgroup (a : K)).subgroupOf (unitFiltration K 0)).index =
      (quadraticNormSubgroup (a : K)).index :=
  Nat.card_congr (unitNormQuotientEquivOfOddDefectExponent hd hodd).toEquiv

end TauCeti
