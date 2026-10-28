/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.PadicTwo
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Filtration
import TauCeti.NumberTheory.LocalField.Padic

/-!
# The conductor threshold for norms from `ℚ₂(i)`

The radicand `-1` has defect exponent one and `v₂(2) = 1`, so the depth-two principal units
are norms. The square classes `1` and `5` have explicit sum-of-two-squares representatives.
In depth one, `3` is a nonnorm. This verifies both sides of the conductor threshold in the
smallest ramified dyadic case.

## References

* The [QuadraticFormInvariants roadmap, Layer 6B](https://github.com/TauCetiProject/TauCetiRoadmap/blob/6d197422/TauCetiRoadmap/QuadraticFormInvariants/README.md),
  for the prescribed dyadic norm controls.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A, for the defect and norm computation.
* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1, for the dyadic Hilbert symbol.

-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

/-- The depth-two principal units of `ℚ₂` are norms for radicand `-1`. -/
theorem unitFiltration_two_le_quadraticNormSubgroup_neg_one_padicTwo :
    unitFiltration ℚ_[2] 2 ≤ quadraticNormSubgroup (-1 : ℚ_[2]) := by
  have hd : defectExponent (-1 : ℚ_[2]ˣ) = 1 :=
    defectExponent_of_serreEps_eq_one_padicTwo (u := -1) (by simp) serreEps_neg_one
  have h := unitFiltration_le_quadraticNormSubgroup_of_defectExponent_eq
    (K := ℚ_[2]) two_ne_zero (a := -1) (by simp) (d := 1) hd
  norm_num [dyadicLevel_def, Padic.natCastValuation_self] at h ⊢
  exact h

/-- The unit norm class `1` has the representative `1 = 1² + 0²`. -/
theorem exists_eq_sq_add_sq_one_padicTwo :
    ∃ x y : ℚ_[2], (1 : ℚ_[2]) = x ^ 2 + y ^ 2 :=
  ⟨1, 0, by norm_num⟩

/-- The unit norm class `5` has the representative `5 = 1² + 2²`. -/
theorem exists_eq_sq_add_sq_five_padicTwo :
    ∃ x y : ℚ_[2], (5 : ℚ_[2]) = x ^ 2 + y ^ 2 :=
  ⟨1, 2, by norm_num⟩

/-- `3` is a depth-one principal unit which is not a norm from `ℚ₂(i)`. -/
theorem three_mem_unitFiltration_one_not_mem_quadraticNormSubgroup_neg_one_padicTwo :
    let b : ℚ_[2]ˣ := Units.mk0 3 (by norm_num)
    b ∈ unitFiltration ℚ_[2] 1 ∧ b ∉ quadraticNormSubgroup (-1 : ℚ_[2]) := by
  dsimp only
  constructor
  · rw [mem_unitFiltration_succ_valuation 0 _ _ (Padic.irreducible_natCast_self 2)]
    have hcoe : ((2 : 𝒪[ℚ_[2]]) : ℚ_[2]) = 2 :=
      map_ofNat (Subring.subtype 𝒪[ℚ_[2]]) 2
    norm_num [hcoe]
  · have h : hilbertSymbol (-1 : ℚ_[2]ˣ) (Units.mk0 3 (by norm_num)) = -1 := by
      apply Units.ext
      have hc : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
      have hv := coe_hilbertSymbol_neg_one_natCast_padicTwo (n := 3) (by decide)
      simpa only [Nat.cast_ofNat, Units.val_neg, Units.val_one] using hv.trans hc
    intro hb
    have hh := (hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup
      (-1 : ℚ_[2]ˣ) (Units.mk0 3 (by norm_num))).mpr
      (by simpa only [Units.val_neg, Units.val_one] using hb)
    rw [h] at hh
    norm_num at hh

end TauCeti
