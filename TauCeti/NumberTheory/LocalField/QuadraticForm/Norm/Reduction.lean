/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Ramification.Dictionary

/-!
# Square-class normalization of quadratic radicands

Every nonsquare radicand can be multiplied by a square to have normalized valuation zero or
one. In the latter case it is a uniformizer. In the former case its defect is either maximal
or a positive odd integer below `2 v_K(2)`. This normalization applies to radicands of negative
valuation as well.

## Main results

* `TauCeti.exists_mul_sq_cases_of_not_isSquare`: the three-case normalization of a
  nonsquare radicand, with an explicit square-rescaling witness.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Multiplying a nonsquare by a square gives a nonsquare uniformizer or a unit whose defect
exponent is maximal or positive odd. The unit-defect alternatives are bounded by `v_K(2)`,
so at odd residue characteristic only the maximal-defect alternative remains. -/
theorem exists_mul_sq_cases_of_not_isSquare
    (h2 : (2 : K) ≠ 0) (a : Kˣ) (ha : ¬IsSquare a) :
    ∃ b c : Kˣ, b = a * c ^ 2 ∧ ¬IsSquare b ∧
      (IsUniformizer (K := K) b ∨ valuation K (b : K) = 1 ∧
        (defectExponent b = ((2 * natCastValuation K 2 h2 : ℕ) : ℤ) ∨
          ∃ k : ℕ, k < natCastValuation K 2 h2 ∧
            defectExponent b = ((2 * k + 1 : ℕ) : ℤ))) := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  let n : ℤ := (normalizedValuation K a).toAdd
  let c : Kˣ := π ^ (-(n / 2))
  let b : Kˣ := a * c ^ 2
  have hval : (normalizedValuation K b).toAdd = n % 2 := by
    have hc : (normalizedValuation K c).toAdd = -(n / 2) := by
      dsimp only [c]
      rw [normalizedValuation_zpow_of_eq_ofAdd_one ((isUniformizer_def π).mp hπ),
        toAdd_ofAdd]
    have hdiv : n % 2 + 2 * (n / 2) = n := Int.emod_add_mul_ediv n 2
    simp only [b, map_mul, map_pow, toAdd_mul, toAdd_pow, hc, nsmul_eq_mul]
    omega
  have hb : ¬IsSquare b := by
    intro h
    have hcancel : b * (c⁻¹) ^ 2 = a := by simp [b, mul_assoc]
    exact ha (hcancel ▸ h.mul (IsSquare.sq c⁻¹))
  refine ⟨b, c, rfl, hb, ?_⟩
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hmod with hzero | hone
  · right
    have hv : valuation K (b : K) = 1 :=
      (normalizedValuation_eq_one_iff b).mp (toAdd_eq_zero.mp (hval.trans hzero))
    exact ⟨hv, defectExponent_eq_two_mul_natCastValuation_or_odd h2 hv hb⟩
  · left
    apply (isUniformizer_def b).mpr
    apply Multiplicative.toAdd.injective
    simpa only [toAdd_ofAdd] using hval.trans hone

end TauCeti
