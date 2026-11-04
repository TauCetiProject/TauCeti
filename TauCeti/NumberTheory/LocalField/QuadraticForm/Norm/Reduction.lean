/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Index
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Ramification.Dictionary

/-!
# Reduction of the quadratic norm-index problem

Every nonsquare radicand can be multiplied by a square to have normalized valuation zero or
one. In the latter case it is a uniformizer. In the former case its defect is either maximal,
when the norm group is already known to have index two, or a positive odd integer below
`2 v_K(2)`.

Consequently, to prove the quadratic norm-index theorem directly from integral norm polynomials,
it suffices to count the unit norm classes for uniformizer radicands and for unit radicands of
odd defect. The reduction preserves the actual quadratic norm subgroup, not just its index,
and applies to radicands of negative valuation as well.

## Main results

* `TauCeti.exists_quadraticNormSubgroup_eq_cases_of_not_isSquare`: the three-case
  reduction of a nonsquare radicand.
* `TauCeti.forall_quadraticNormSubgroup_index_eq_two_iff`: the universal norm-index statement
  is equivalent to its two ramified cases; the unramified case needs no further input.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Multiplying a nonsquare by a square gives a nonsquare uniformizer or a unit whose defect
exponent is maximal or positive odd, without changing its quadratic norm subgroup. The
unit-defect alternatives are bounded by `v_K(2)`, so at odd residue characteristic only the
maximal-defect alternative remains. -/
theorem exists_quadraticNormSubgroup_eq_cases_of_not_isSquare
    (h2 : (2 : K) ≠ 0) (a : Kˣ) (ha : ¬IsSquare a) :
    ∃ b c : Kˣ, b = a * c ^ 2 ∧
      quadraticNormSubgroup (b : K) = quadraticNormSubgroup (a : K) ∧
      ¬IsSquare b ∧
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
  have hnorm : quadraticNormSubgroup (b : K) = quadraticNormSubgroup (a : K) := by
    -- The unit coercion of `a * c²` is the rescaled radicand in the norm-subgroup lemma.
    simpa only [b, Units.val_mul, Units.val_pow_eq_pow_val] using
      quadraticNormSubgroup_mul_sq (a : K) c
  have hb : ¬IsSquare b := by
    intro h
    have hcancel : b * (c⁻¹) ^ 2 = a := by simp [b, mul_assoc]
    exact ha (hcancel ▸ h.mul (IsSquare.sq c⁻¹))
  refine ⟨b, c, rfl, hnorm, hb, ?_⟩
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

/-- The quadratic norm-index theorem for all nonsquares reduces exactly to the uniformizer
case and the unit case of odd defect. Units of maximal defect are discharged by the
unramified norm criterion, without assuming any ramified norm-index theorem. -/
theorem forall_quadraticNormSubgroup_index_eq_two_iff (h2 : (2 : K) ≠ 0) :
    (∀ a : Kˣ, ¬IsSquare a → (quadraticNormSubgroup (a : K)).index = 2) ↔
      (∀ a : Kˣ, IsUniformizer (K := K) a → (quadraticNormSubgroup (a : K)).index = 2) ∧
      (∀ a : Kˣ, valuation K (a : K) = 1 → ∀ k : ℕ,
        k < natCastValuation K 2 h2 → defectExponent a = ((2 * k + 1 : ℕ) : ℤ) →
          (quadraticNormSubgroup (a : K)).index = 2) := by
  constructor
  · intro h
    exact ⟨fun a ha ↦ h a (not_isSquare_of_isUniformizer ha),
      fun a _ _ _ hd ↦ h a (not_isSquare_of_defectExponent_eq hd)⟩
  · rintro ⟨huniformizer, hodd⟩ a ha
    obtain ⟨b, _, _, hnorm, _, hb | ⟨hv, hmax | ⟨k, hk, hd⟩⟩⟩ :=
      exists_quadraticNormSubgroup_eq_cases_of_not_isSquare h2 a ha
    · rw [← hnorm]
      exact huniformizer b hb
    · rw [← hnorm]
      have hcriterion := (unramified_class_iff_even_defectExponent h2 hmax).mpr
        (even_two_mul (natCastValuation K 2 h2 : ℤ))
      exact quadraticNormSubgroup_index_eq_two_of_unramified_class hcriterion
    · rw [← hnorm]
      exact hodd b hv k hk hd

end TauCeti
