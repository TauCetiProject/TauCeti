/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.DeepUnitIndex
public import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Two

import TauCeti.NumberTheory.LocalField.QuadraticForm.Ramification.Dictionary

/-!
# Deep units and unit norms over `ℚ₂(√2)`

In `K = ℚ₂(√2)` the residue field has two elements and `v_K(2) = 2`. So `U(K, 4) · (𝒪[K]ˣ)²` has
index `2 ^ 2 = 4` in `𝒪[K]ˣ` (`TauCeti.relIndex_unitFiltration_two_mul_dyadicLevel_sup_square`).

For the radicand `1 + √2`, of defect exponent `1`, every element of `U(K, 4)` is a norm from
`K(√(1 + √2))`, as is every square, but the unit norms have index two in `𝒪[K]ˣ`. So they strictly
contain `U(K, 4) · (𝒪[K]ˣ)²`. So for this radicand of odd defect, the containment of deep units in
the norms does not determine the unit norms. Over `ℚ₂` the corresponding subgroup
`U(ℚ₂, 2) · (ℤ₂ˣ)²` already has index two, and no such gap arises.

## Main results

* `TauCeti.DyadicSqrtTwo.relIndex_unitFiltration_four_sup_square`: `U(K, 4) · (𝒪[K]ˣ)²` has index
  four in `𝒪[K]ˣ`.
* `TauCeti.DyadicSqrtTwo.unitFiltration_four_sup_square_inf_lt_quadraticNormSubgroup_inf`: the
  unit norms from `K(√(1 + √2))` strictly contain it.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel

namespace TauCeti.DyadicSqrtTwo

/-- **The index of `U(K, 4) · (𝒪[K]ˣ)²` in `𝒪[K]ˣ` is four** for `K = ℚ₂(√2)`. -/
theorem relIndex_unitFiltration_four_sup_square :
    (unitFiltration DyadicSqrtTwo 4 ⊔ Subgroup.square DyadicSqrtTwoˣ).relIndex
        (unitFiltration DyadicSqrtTwo 0) = 4 := by
  have h := relIndex_unitFiltration_two_mul_dyadicLevel_sup_square (K := DyadicSqrtTwo) two_ne_zero
  rwa [dyadicLevel_eq_two, natCard_residueField] at h

/-- **The unit norms from `ℚ₂(√2)(√(1 + √2))` strictly contain `U(K, 4) · (𝒪[K]ˣ)²`.** The radicand
`1 + √2` is a unit of defect exponent one, and `2 ^ v_K(2) = 4 > 2`. -/
theorem unitFiltration_four_sup_square_inf_lt_quadraticNormSubgroup_inf :
    (unitFiltration DyadicSqrtTwo 4 ⊔ Subgroup.square DyadicSqrtTwoˣ) ⊓
        unitFiltration DyadicSqrtTwo 0 <
      quadraticNormSubgroup (1 + sqrtTwo) ⊓ unitFiltration DyadicSqrtTwo 0 := by
  have h2 : (2 : DyadicSqrtTwo) ≠ 0 := two_ne_zero
  have hπ1 := Valuation.integer.v_irreducible_lt_one (v := valuation DyadicSqrtTwo)
    irreducible_integerSqrtTwo
  rw [coe_integerSqrtTwo] at hπ1
  have hd := defectExponent_one_add_pow_odd h2 irreducible_integerSqrtTwo (k := 0)
    (by rw [← dyadicLevel_def, dyadicLevel_eq_two]; norm_num)
  have hne : (1 + sqrtTwo : DyadicSqrtTwo) ≠ 0 := fun h ↦ by
    simpa [h] using (valuation DyadicSqrtTwo).map_one_add_of_lt hπ1
  -- Name the unit `1 + √2` of the defect computation, where it appears as `1 + π ^ (2 * 0 + 1)`.
  have hpow : (1 + (integerSqrtTwo : DyadicSqrtTwo) ^ (2 * 0 + 1)) = 1 + sqrtTwo := by
    rw [coe_integerSqrtTwo, Nat.mul_zero, Nat.zero_add, pow_one]
  have ha : Units.mk0 (1 + (integerSqrtTwo : DyadicSqrtTwo) ^ (2 * 0 + 1)) (hpow ▸ hne) =
      Units.mk0 (1 + sqrtTwo) hne :=
    Units.ext (by rw [Units.val_mk0, Units.val_mk0, hpow])
  rw [ha] at hd
  have h := (unitFiltration_sup_square_inf_lt_quadraticNormSubgroup_inf_iff h2
    (a := Units.mk0 _ hne) ((valuation DyadicSqrtTwo).map_one_add_of_lt hπ1)
    (hd.trans (by norm_num))).mpr (by rw [dyadicLevel_eq_two, natCard_residueField]; norm_num)
  rwa [dyadicLevel_eq_two] at h

end TauCeti.DyadicSqrtTwo
