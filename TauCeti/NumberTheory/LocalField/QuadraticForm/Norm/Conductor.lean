/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Sharpness
import TauCeti.NumberTheory.LocalField.QuadraticForm.OddValuation
import TauCeti.NumberTheory.LocalField.QuadraticForm.Ramification.Dictionary

/-!
# Quadratic norm conductors for arbitrary radicands

The least depth at which all principal units are norms is determined by the quadratic
defect, including for radicands of negative valuation. For a nonsquare `a` with finite
defect exponent `d`, put `r = d - v_K(a)`. If `d` is even, the extension is unramified
and all units are norms. Otherwise the least depth is `2 v_K(2) - r + 1`.

For odd-valuation radicands, `r = 0`. The unramified quadratic class supplies a non-norm
at depth `2 v_K(2)`, while the local square theorem supplies the upper bound. For
even-valuation radicands, square rescaling reduces to the sharp unit-radicand criterion
of `Norm.Sharpness`. Thus the threshold depends on the relative defect `d - v_K(a)`,
not on the unnormalized exponent `d`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For an odd-valuation radicand, the unramified class is a non-norm already at depth
`2 v_K(2)`. This includes the depth-zero obstruction in odd residue characteristic. -/
theorem not_unitFiltration_le_quadraticNormSubgroup_of_odd (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : Odd (normalizedValuation K a).toAdd) :
    ¬unitFiltration K (2 * dyadicLevel K h2) ≤ quadraticNormSubgroup (a : K) := by
  obtain ⟨Δ, -, hΔ0, hΔ1, hΔ⟩ := exists_unramified_class h2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  have hmem : Δ ∈ unitFiltration K (2 * dyadicLevel K h2) := by
    rw [mem_unitFiltration_iff_valuation_le hπ]
    exact ⟨(normalizedValuation_eq_one_iff Δ).mp (toAdd_eq_zero.mp hΔ0),
      by simpa only [valuation_four_eq_pow h2 hπ, dyadicLevel_def] using hΔ1⟩
  intro h
  have hsign := hilbertSymbol_eq_neg_one_of_unramified_class_of_odd h2 hΔ ha
  have hone := (hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a Δ).mpr (h hmem)
  exact (by decide : (1 : ℤˣ) ≠ -1) (hone.symm.trans hsign)

/-- For any odd-valuation radicand, all units of depth `n` are norms exactly when
`n > 2 v_K(2)`. No normalization of the radicand is required. -/
theorem unitFiltration_le_quadraticNormSubgroup_iff_of_odd (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : Odd (normalizedValuation K a).toAdd) {n : ℕ} :
    unitFiltration K n ≤ quadraticNormSubgroup (a : K) ↔ 2 * dyadicLevel K h2 < n := by
  refine ⟨fun h => ?_, fun h => (unitFiltration_antitone h).trans
    ((unitFiltration_le_square h2).trans (square_le_quadraticNormSubgroup _))⟩
  by_contra! hn
  exact not_unitFiltration_le_quadraticNormSubgroup_of_odd h2 ha
    ((unitFiltration_antitone hn).trans h)

/-- The exact principal-unit norm threshold for every nonsquare radicand, including those
of negative valuation. The even-defect case is unramified. In the ramified case the relative
defect `d - v_K(a)` is nonnegative, and all depth-`n` units are norms exactly when
`n > 2 v_K(2) - (d - v_K(a))`. -/
theorem unitFiltration_le_quadraticNormSubgroup_iff (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) {n : ℕ} :
    unitFiltration K n ≤ quadraticNormSubgroup (a : K) ↔
      Even d ∨ 2 * dyadicLevel K h2 - (d - (normalizedValuation K a).toAdd).toNat < n := by
  by_cases he : Even d
  · simp only [he, true_or, iff_true]
    intro b hb
    have hb0 := (unitFiltration_antitone (Nat.zero_le n)) hb
    have hv : (normalizedValuation K b).toAdd = 0 := by
      rw [(normalizedValuation_eq_one_iff b).mpr ((mem_unitFiltration_zero b).mp hb0)]
      rfl
    apply (hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a b).mp
    apply (hilbertSymbol_eq_one_iff a b).mpr
    exact ((unramified_class_iff_even_defectExponent h2 hd).mpr he b).mpr
      (by simp [hv])
  simp only [he, false_or]
  rcases Int.even_or_odd (normalizedValuation K a).toAdd with hv | hv
  · obtain ⟨k, hk⟩ := hv
    obtain ⟨c, hc⟩ := normalizedValuation_surjective (K := K) (Multiplicative.ofAdd (-k))
    let b := a * c ^ 2
    have hbval : (normalizedValuation K b).toAdd = 0 := by
      simp only [b, map_mul, map_pow, toAdd_mul, toAdd_pow, hc, toAdd_ofAdd, nsmul_eq_mul]
      omega
    have hbunit : valuation K (b : K) = 1 :=
      (normalizedValuation_eq_one_iff b).mp (toAdd_eq_zero.mp hbval)
    have hbd : defectExponent b = ((d - (normalizedValuation K a).toAdd : ℤ) : WithTop ℤ) := by
      rw [defectExponent_mul_sq, hd, hc, toAdd_ofAdd, ← WithTop.coe_add]
      congr 1
      omega
    have hr : 0 ≤ d - (normalizedValuation K a).toAdd := by
      have h := toAdd_normalizedValuation_le_defectExponent b
      rw [hbval, hbd, WithTop.coe_le_coe] at h
      exact h
    have hdn : defectExponent b =
        (((d - (normalizedValuation K a).toAdd).toNat : ℕ) : ℤ) := by
      simpa only [Int.toNat_of_nonneg hr] using hbd
    have hodd : Odd (d - (normalizedValuation K a).toAdd).toNat := by
      rw [← Int.odd_natCast, Int.toNat_of_nonneg hr]
      exact (Int.not_even_iff_odd.mp he).sub_even ⟨k, hk⟩
    have h := unitFiltration_le_quadraticNormSubgroup_iff_of_odd_defectExponent
      h2 hbunit hdn hodd (n := n)
    simpa only [b, Units.val_mul, Units.val_pow_eq_pow_val,
      quadraticNormSubgroup_mul_sq] using h
  · have hdval : d = (normalizedValuation K a).toAdd :=
      WithTop.coe_injective (hd.symm.trans (defectExponent_of_odd hv))
    simpa only [hdval, sub_self, Int.toNat_zero, Nat.sub_zero] using
      unitFiltration_le_quadraticNormSubgroup_iff_of_odd h2 hv (n := n)

end TauCeti
