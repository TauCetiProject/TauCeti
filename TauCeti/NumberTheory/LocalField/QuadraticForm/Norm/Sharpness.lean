/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Filtration
import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity

import TauCeti.NumberTheory.LocalField.QuadraticForm.UnramifiedClass
import TauCeti.RingTheory.Finite.ArtinSchreier

/-!
# The sharp depth of quadratic unit norms

For a unit `a` of odd quadratic defect exponent `d`, the principal units of depth
`2 v_K(2) - d + 1` are norms from `K(√a)`, but those of depth `2 v_K(2) - d` are not all norms.
Together with the containment theorem, this determines the exact depth at which the unit
filtration enters the quadratic norm subgroup, over any nonarchimedean local field with `2 ≠ 0`.

The non-norm is constructed from an optimal square approximation of `a` and a principal-unit
representative of the unramified quadratic class. Bimultiplicativity, the Steinberg relation,
and the unramified norm criterion detect its negative Hilbert symbol.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A, especially 63:11–13.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

-- This is the obstruction calculation for the candidate `(Δ s² - a) / (s² - a)`.
private theorem sharpnessCandidate_not_mem (h2 : (2 : K) ≠ 0) (a Δ s y z : Kˣ)
    (ha : valuation K (a : K) = 1) (hD : valuation K ((Δ * s ^ 2 : Kˣ) : K) = 1)
    (hy : (y : K) = (s : K) ^ 2 - a) (hz : (z : K) = (Δ * s ^ 2 : Kˣ) - a)
    (hzodd : ¬Even (normalizedValuation K z).toAdd)
    (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd) :
    z / y ∉ quadraticNormSubgroup (a : K) := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  let D := Δ * s ^ 2
  have hΔz : hilbertSymbol Δ z = -1 := by rw [hilbertSymbol_unramified hΔ]; simp [hzodd]
  have hΔa : hilbertSymbol Δ a = 1 := by
    rw [hilbertSymbol_unramified hΔ, (normalizedValuation_eq_one_iff a).mpr ha]
    simp
  have hΔD : hilbertSymbol Δ D = 1 := by
    rw [hilbertSymbol_unramified hΔ, (normalizedValuation_eq_one_iff D).mpr hD]
    simp
  have hDz : hilbertSymbol D z = -1 := by simpa [D] using hΔz
  have hDa : hilbertSymbol D a = 1 := by simpa [D] using hΔa
  have hDD : hilbertSymbol D D = 1 := by simpa [D] using hΔD
  -- Steinberg for `a / D` compares the candidate to the unramified symbol.
  have hnorm : hilbertSymbol (a / D) (z / D) = 1 := by
    apply (hilbertSymbol_eq_one_iff _ _).mpr
    refine ⟨1, 1, ?_⟩
    simp only [Units.val_div_eq_div_val, hz, one_pow, mul_one]
    field_simp
    rfl
  have haz : hilbertSymbol a z = -1 := by
    have hinv (u v : Kˣ) : hilbertSymbol u⁻¹ v = hilbertSymbol u v := by
      simpa only [zpow_neg_one, Int.units_inv_eq_self] using
        hilbertSymbol_zpow_left h2 u v (-1)
    have hinv' (u v : Kˣ) : hilbertSymbol u v⁻¹ = hilbertSymbol u v := by
      rw [hilbertSymbol_comm, hinv, hilbertSymbol_comm]
    simp only [div_eq_mul_inv, hilbertSymbol_mul_left h2, hilbertSymbol_mul_right h2,
      hinv, hinv', hDz, hDa, hDD, hilbertSymbol_comm a D, mul_one] at hnorm
    simpa only [mul_neg_one, neg_eq_iff_eq_neg] using hnorm
  have hay : hilbertSymbol a y = 1 :=
    (hilbertSymbol_eq_one_iff _ _).mpr ⟨s, 1, by simpa using hy⟩
  intro h
  have hb := (hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup a (z / y)).mpr h
  rw [← div_mul_cancel z y, hilbertSymbol_mul_right h2, hb, hay, mul_one] at haz
  norm_num at haz

-- The two numerator terms have the same valuation; their quotient is the desired deep unit.
private theorem sharpnessCandidate_mem (h2 : (2 : K) ≠ 0) (a Δ s y z : Kˣ)
    {π : 𝒪[K]} (hπ : Irreducible π) {d : ℕ} (hdle : d ≤ 2 * natCastValuation K 2 h2)
    (hs : valuation K ((s : K) ^ 2) = 1)
    (hy : (y : K) = (s : K) ^ 2 - a) (hz : (z : K) = (Δ * s ^ 2 : Kˣ) - a)
    (hyv : valuation K (y : K) = valuation K (π : K) ^ d)
    (hzv : valuation K (z : K) = valuation K (π : K) ^ d)
    (hη : valuation K ((Δ : K) - 1) ≤
      valuation K (π : K) ^ (2 * natCastValuation K 2 h2)) :
    z / y ∈ unitFiltration K (2 * dyadicLevel K h2 - d) := by
  have hp0 : valuation K (π : K) ≠ 0 := by simpa using hπ.ne_zero
  rw [mem_unitFiltration_iff_valuation_le hπ]
  refine ⟨?_, ?_⟩
  · simp only [Units.val_div_eq_div_val, map_div₀, hzv, hyv]
    exact div_self (pow_ne_zero _ hp0)
  · have hb1 : ((z / y : Kˣ) : K) - 1 = ((Δ : K) - 1) * (s : K) ^ 2 / y := by
      rw [Units.val_div_eq_div_val, div_sub_one y.ne_zero, hz, hy]
      push_cast
      congr 1
      ring
    rw [hb1, map_div₀, map_mul, hs, mul_one, hyv, dyadicLevel_def, pow_sub₀ _ hp0 hdle]
    exact div_le_div_of_nonneg_right hη zero_le

private theorem exists_sharpnessCandidate (h2 : (2 : K) ≠ 0) {a : Kˣ}
    (ha : valuation K (a : K) = 1) {d : ℕ} (hd : defectExponent a = (d : ℤ))
    (hodd : Odd d) {π : 𝒪[K]} (hπ : Irreducible π) (Δ : Kˣ)
    (hΔv : valuation K (Δ : K) = 1)
    (hη : valuation K ((Δ : K) - 1) ≤
      valuation K (π : K) ^ (2 * natCastValuation K 2 h2))
    (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd) :
    ∃ b : Kˣ, b ∈ unitFiltration K (2 * dyadicLevel K h2 - d) ∧
      b ∉ quadraticNormSubgroup (a : K) := by
  have hnsq := not_isSquare_of_defectExponent_eq hd
  have hdle : d ≤ 2 * natCastValuation K 2 h2 := by
    have h := defectExponent_le_two_mul_natCastValuation h2 ha hnsq
    rw [hd, WithTop.coe_le_coe] at h
    exact_mod_cast h
  have hdlt : d < 2 * natCastValuation K 2 h2 := by obtain ⟨k, hk⟩ := hodd; omega
  have hp : valuation K (π : K) < 1 := Valuation.integer.v_irreducible_lt_one hπ
  have hp0 : valuation K (π : K) ≠ 0 := by simpa using hπ.ne_zero
  -- Retain an optimal square approximation and its unit square root.
  obtain ⟨ξ, x, hx, hxd⟩ := exists_defectExponent_eq hnsq
  rw [hd, WithTop.coe_inj] at hxd
  have hxv : valuation K (x : K) = valuation K (π : K) ^ d := by
    simpa only [zpow_natCast, Units.val_mk0] using
      (toAdd_normalizedValuation_eq_iff_valuation_eq_zpow
        (normalizedValuation_irreducible hπ) (d : ℤ) x).mp hxd
  have hξEq : ξ ^ 2 = (a : K) - x := by rw [hx]; ring
  have hξv : valuation K (ξ ^ 2) = 1 := by
    rw [hξEq,
      Valuation.map_sub_eq_of_lt_left _ (ha ▸ (hxv ▸ pow_lt_one₀ zero_le hp hodd.pos.ne')), ha]
  have hξ0 : ξ ≠ 0 := by intro h; simp [h] at hξv
  let s : Kˣ := Units.mk0 ξ hξ0
  let D : Kˣ := Δ * s ^ 2
  have hDv : valuation K (D : K) = 1 := by
    simpa only [D, Units.val_mul, Units.val_pow_eq_pow_val, s, Units.val_mk0,
      map_mul, hΔv, one_mul] using hξv
  let y : Kˣ := -x
  have hy : (y : K) = ξ ^ 2 - a := by simp [y, hx]
  have hyv : valuation K (y : K) = valuation K (π : K) ^ d := by simpa [y] using hxv
  -- The unramified correction is strictly deeper than the optimal approximation.
  have hsmall : valuation K (((Δ : K) - 1) * ξ ^ 2) < valuation K (y : K) := by
    rw [map_mul, hξv, mul_one, hyv]
    exact hη.trans_lt (pow_lt_pow_right_of_lt_one₀ hp0.bot_lt hp hdlt)
  have hzEq : (D : K) - a = (y : K) - (-(((Δ : K) - 1) * ξ ^ 2)) := by
    simp [D, hy, s]
    ring
  have hzv : valuation K ((D : K) - a) = valuation K (π : K) ^ d := by
    rw [hzEq,
      Valuation.map_sub_eq_of_lt_left _ (by simpa using hsmall), hyv]
  have hz0 : (D : K) - a ≠ 0 := by
    intro h
    exact pow_ne_zero _ hp0 (by simpa [h] using hzv.symm)
  let z : Kˣ := Units.mk0 _ hz0
  -- Its odd numerator order detects the obstruction through the unramified class.
  have hzodd : ¬Even (normalizedValuation K z).toAdd := by
    have hval : (normalizedValuation K z).toAdd = d := by
      apply (toAdd_normalizedValuation_eq_iff_valuation_eq_zpow
        (normalizedValuation_irreducible hπ) (d : ℤ) z).mpr
      simpa [z, zpow_natCast] using hzv
    rw [hval]
    exact Int.not_even_iff_odd.mpr (by exact_mod_cast hodd)
  exact ⟨z / y, sharpnessCandidate_mem h2 a Δ s y z hπ hdle hξv hy rfl hyv hzv hη,
    sharpnessCandidate_not_mem h2 a Δ s y z ha hDv hy rfl hzodd hΔ⟩

/-- The depth immediately preceding the quadratic norm filtration contains a non-norm when
the defining unit has odd defect exponent. -/
theorem not_unitFiltration_le_quadraticNormSubgroup_of_odd_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} (ha : valuation K (a : K) = 1) {d : ℕ}
    (hd : defectExponent a = (d : ℤ)) (hodd : Odd d) :
    ¬unitFiltration K (2 * dyadicLevel K h2 - d) ≤ quadraticNormSubgroup (a : K) := by
  classical
  have he : 0 < natCastValuation K 2 h2 := by
    have h := defectExponent_le_two_mul_natCastValuation h2 ha
      (not_isSquare_of_defectExponent_eq hd)
    rw [hd, WithTop.coe_le_coe] at h
    have hdpos := hodd.pos
    omega
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  -- Retain the principal-unit representative from the explicit unramified norm criterion.
  obtain ⟨r, hr⟩ := exists_not_mem_range_sq_add_self (𝓀[K])
  obtain ⟨c, rfl⟩ := residue_surjective r
  have hc : ∀ t : 𝓀[K], t ^ 2 + t ≠ residue 𝒪[K] c := fun t ht => hr ⟨t, ht⟩
  have hΔv := valuation_one_add_four_mul h2 he c
  have hΔ0 : (1 + 4 * (c : K)) ≠ 0 := by intro h; simp [h] at hΔv
  let Δ : Kˣ := Units.mk0 _ hΔ0
  have hη : valuation K ((Δ : K) - 1) ≤
      valuation K (π : K) ^ (2 * natCastValuation K 2 h2) := by
    simp only [Δ, Units.val_mk0, add_sub_cancel_left, map_mul, valuation_four_eq_pow h2 hπ]
    simpa using mul_le_mul' (le_refl (valuation K (π : K) ^
      (2 * natCastValuation K 2 h2))) ((Valuation.mem_integer_iff _ _).mp c.2)
  obtain ⟨b, hb, hbnorm⟩ := exists_sharpnessCandidate h2 ha hd hodd hπ Δ hΔv hη
    (exists_eq_sq_sub_one_add_four_mul_mul_sq_iff_even h2 hc)
  exact fun h => hbnorm (h hb)

/-- For a unit of odd defect exponent `d`, all principal units of depth `n` are quadratic
norms exactly when `n > 2 v_K(2) - d`. -/
theorem unitFiltration_le_quadraticNormSubgroup_iff_of_odd_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} (ha : valuation K (a : K) = 1) {d n : ℕ}
    (hd : defectExponent a = (d : ℤ)) (hodd : Odd d) :
    unitFiltration K n ≤ quadraticNormSubgroup (a : K) ↔ 2 * dyadicLevel K h2 - d < n := by
  refine ⟨fun h => ?_, fun h => (unitFiltration_antitone h).trans
    (unitFiltration_le_quadraticNormSubgroup_of_defectExponent_eq h2 ha hd)⟩
  by_contra! hn
  exact not_unitFiltration_le_quadraticNormSubgroup_of_odd_defectExponent h2 ha hd hodd
    ((unitFiltration_antitone hn).trans h)

end TauCeti
