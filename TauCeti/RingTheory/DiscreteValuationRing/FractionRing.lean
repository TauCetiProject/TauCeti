/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Fraction fields of discrete valuation rings

This file relates the two natural descriptions of the fraction field of a discrete valuation
ring. Besides being the localization at all non-zero elements, it is the localization away from
any uniformizer. This is what makes the induced map of spectra a principal open immersion.

Every nonzero element of the fraction field is a unit of the ring times an integer power of a
uniformizer (`IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible`). This file
also records two consequences for the images of units of the ring.

## Main results

* `Irreducible.isLocalizationAway_fractionRing`: the fraction field is the localization away from
  any uniformizer.
* `Irreducible.eq_zero_of_zpow_eq_algebraMap`: an integer power of a uniformizer is the image of a
  unit only for the exponent zero.
* `TauCeti.IsDiscreteValuationRing.exists_algebraMap_eq_of_pow_eq_algebraMap`: an element some
  nonzero power of which is the image of a unit is itself the image of a unit.
-/

public section

/-- The fraction field of a discrete valuation ring is the localization away from any
uniformizer. Here uniformizers are expressed using Mathlib's equivalent `Irreducible` predicate.
-/
lemma Irreducible.isLocalizationAway_fractionRing {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommSemiring K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K :=
  (IsLocalization.iff_of_le_of_exists_dvd _ _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero) fun _ hx ↦
      have ⟨n, hn⟩ :=
        IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hx) hϖ
      ⟨ϖ ^ n, pow_mem (Submonoid.mem_powers ϖ) n, hn.dvd⟩).mpr inferInstance

section Field

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- An integer power of the image of a uniformizer in the fraction field is the image of a unit
only for the exponent zero. -/
theorem Irreducible.eq_zero_of_zpow_eq_algebraMap {ϖ : R} (hϖ : Irreducible ϖ) {j : ℤ} {v : Rˣ}
    (h : algebraMap R K ϖ ^ j = algebraMap R K v) : j = 0 := by
  have key (m : ℕ) (w : Rˣ) (hw : algebraMap R K ϖ ^ m = algebraMap R K w) : m = 0 := by
    rw [← map_pow] at hw
    have hunit : IsUnit (ϖ ^ m) := IsFractionRing.injective R K hw ▸ w.isUnit
    by_contra hm
    exact hϖ.not_isUnit ((isUnit_pow_iff hm).mp hunit)
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · exact_mod_cast key m v (by simpa using h)
  · have hm : algebraMap R K ϖ ^ m = algebraMap R K (v⁻¹ : Rˣ) := by
      rw [zpow_neg, zpow_natCast] at h
      rw [map_units_inv, ← h, inv_inv]
    simp [key m v⁻¹ hm]

/-- An element of the fraction field of a discrete valuation ring, some nonzero power of which is
the image of a unit, is itself the image of a unit. -/
theorem TauCeti.IsDiscreteValuationRing.exists_algebraMap_eq_of_pow_eq_algebraMap [IsDomain R]
    [IsDiscreteValuationRing R] {n : ℕ} (hn : n ≠ 0) {x : K} {w : Rˣ}
    (h : x ^ n = algebraMap R K w) : ∃ v : Rˣ, algebraMap R K v = x := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible R
  have hx : x ≠ 0 := by
    rintro rfl
    exact (w.isUnit.map (algebraMap R K)).ne_zero (by rw [← h, zero_pow hn])
  obtain ⟨j, v, rfl⟩ :=
    _root_.IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hx
  -- `(v ϖʲ)ⁿ = w`, so `ϖ ^ (n j)` is the image of the unit `w v⁻ⁿ`
  have hj : algebraMap R K ϖ ^ ((n : ℤ) * j) = algebraMap R K ↑(w * v⁻¹ ^ n) := by
    have hv : algebraMap R K v ≠ 0 := (v.isUnit.map _).ne_zero
    have hpow : (algebraMap R K ϖ ^ j) ^ n = algebraMap R K ϖ ^ ((n : ℤ) * j) := by
      rw [mul_comm, zpow_mul, zpow_natCast]
    rw [Units.smul_def, Algebra.smul_def, mul_pow, hpow] at h
    simp [← h, map_units_inv]
    field_simp
  have hnj : (n : ℤ) * j = 0 := hϖ.eq_zero_of_zpow_eq_algebraMap hj
  refine ⟨v, ?_⟩
  rw [show j = 0 by simpa [hn] using hnj, zpow_zero, Units.smul_def, Algebra.smul_def, mul_one]

end Field
