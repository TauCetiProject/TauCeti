/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Data.Int.Log

/-!
# Rounding a bound to a finite-place value

For a finite place `v` and `t > 0`, `v.floorValue t` is the largest value of `v` on
nonzero field elements that is at most `t`. Thus a condition `v x ≤ t` can be replaced
by `v x ≤ v.floorValue t` without changing the set it defines. The rounded bound is
attained, and differs from `t` by a factor strictly smaller than the norm of the prime.
These facts allow volume and covolume estimates with real bounds to account for the
discreteness of finite-place values.

The construction uses Mathlib's integer logarithm and the surjectivity of the adic
valuation. The mathematical setting is Bombieri–Gubler, *Heights in Diophantine
Geometry*, §7.5 and Appendix C.2. Real bounds need not themselves be values of a place.
-/

public section

noncomputable section

namespace NumberField.FinitePlace

open IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- Every nonzero finite-place value is an integer power of the norm of its prime. -/
theorem apply_eq_absNorm_zpow (v : FinitePlace K) {x : K} (hx : x ≠ 0) :
    v x = (v.maximalIdeal.asIdeal.absNorm : ℝ) ^
      WithZero.log (v.maximalIdeal.valuation K x) := by
  rw [← norm_embedding_eq, norm_embedding, HeightOneSpectrum.adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _ ((v.maximalIdeal.valuation K).ne_zero_iff.mpr hx),
    NNReal.coe_zpow, NNReal.coe_natCast]

/-- Every integer power of the prime norm occurs as a nonzero finite-place value. -/
theorem exists_ne_zero_apply_eq_absNorm_zpow (v : FinitePlace K) (n : ℤ) :
    ∃ x : K, x ≠ 0 ∧ v x = (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ n := by
  obtain ⟨x, hx⟩ := v.maximalIdeal.valuation_surjective K (WithZero.exp n)
  have hx0 : x ≠ 0 := (v.maximalIdeal.valuation K).ne_zero_iff.mp (by
    rw [hx]
    exact WithZero.exp_ne_zero)
  refine ⟨x, hx0, ?_⟩
  rw [v.apply_eq_absNorm_zpow hx0, hx, WithZero.log_exp]

/-- The largest finite-place value below a positive real bound. It is zero at nonpositive
bounds. -/
def floorValue (v : FinitePlace K) (t : ℝ) : ℝ :=
  if 0 < t then
    (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Int.log v.maximalIdeal.asIdeal.absNorm t
  else 0

/-- For a positive bound, the value floor is given by the integer logarithm. -/
theorem floorValue_of_pos (v : FinitePlace K) {t : ℝ} (ht : 0 < t) :
    v.floorValue t =
      (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Int.log v.maximalIdeal.asIdeal.absNorm t := by
  simp [floorValue, ht]

/-- The value floor is zero at a nonpositive bound. -/
@[simp]
theorem floorValue_of_nonpos (v : FinitePlace K) {t : ℝ} (ht : t ≤ 0) :
    v.floorValue t = 0 := by
  simp [floorValue, not_lt.mpr ht]

/-- Value floors are nonnegative, including at nonpositive bounds. -/
theorem floorValue_nonneg (v : FinitePlace K) (t : ℝ) : 0 ≤ v.floorValue t := by
  unfold floorValue
  split_ifs
  · exact zpow_nonneg (Nat.cast_nonneg _) _
  · exact le_rfl

/-- The value floor of a positive bound is positive. -/
theorem floorValue_pos (v : FinitePlace K) {t : ℝ} (ht : 0 < t) :
    0 < v.floorValue t := by
  rw [v.floorValue_of_pos ht]
  exact zpow_pos (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.maximalIdeal).pos) _

/-- Rounding a nonnegative bound never increases it. -/
theorem floorValue_le (v : FinitePlace K) {t : ℝ} (ht : 0 ≤ t) : v.floorValue t ≤ t := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  · rw [v.floorValue_of_pos ht]
    exact Int.zpow_log_le_self (HeightOneSpectrum.one_lt_absNorm v.maximalIdeal) ht

/-- The original positive bound is strictly less than the next possible finite-place value. -/
theorem lt_absNorm_mul_floorValue (v : FinitePlace K) {t : ℝ} (ht : 0 < t) :
    t < (v.maximalIdeal.asIdeal.absNorm : ℝ) * v.floorValue t := by
  have hN : (v.maximalIdeal.asIdeal.absNorm : ℝ) ≠ 0 := by
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.maximalIdeal).ne_zero
  rw [v.floorValue_of_pos ht, mul_comm]
  simpa only [zpow_add₀ hN, zpow_one] using Int.lt_zpow_succ_log_self
    (R := ℝ) (HeightOneSpectrum.one_lt_absNorm v.maximalIdeal) t

/-- Replacing a positive bound by its value floor leaves every local inequality unchanged,
including the inequality at zero. -/
theorem apply_le_iff_le_floorValue (v : FinitePlace K) {t : ℝ} (ht : 0 < t) (x : K) :
    v x ≤ t ↔ v x ≤ v.floorValue t := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.trans (v.floorValue_le ht.le)⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using v.floorValue_nonneg t
  rw [v.apply_eq_absNorm_zpow hx, v.floorValue_of_pos ht]
  exact zpow_le_zpow_right₀
    (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.maximalIdeal).le)
    ((Int.zpow_le_iff_le_log (HeightOneSpectrum.one_lt_absNorm v.maximalIdeal) ht).mp
      ((v.apply_eq_absNorm_zpow hx) ▸ h))

/-- The value floor of a positive bound is attained by a nonzero element. -/
theorem exists_apply_eq_floorValue (v : FinitePlace K) {t : ℝ} (ht : 0 < t) :
    ∃ x : K, x ≠ 0 ∧ v x = v.floorValue t := by
  rw [v.floorValue_of_pos ht]
  exact v.exists_ne_zero_apply_eq_absNorm_zpow _

/-- At a positive bound, the value floor is exactly the greatest nonzero value below it. -/
theorem isGreatest_floorValue (v : FinitePlace K) {t : ℝ} (ht : 0 < t) :
    IsGreatest {s : ℝ | ∃ x : K, x ≠ 0 ∧ v x = s ∧ s ≤ t} (v.floorValue t) := by
  obtain ⟨x, hx, hxt⟩ := v.exists_apply_eq_floorValue ht
  refine ⟨⟨x, hx, hxt, v.floorValue_le ht.le⟩, ?_⟩
  rintro s ⟨y, _, rfl, hy⟩
  exact (v.apply_le_iff_le_floorValue ht y).mp hy

/-- Rounding a value already attained by the place leaves it unchanged. -/
@[simp]
theorem floorValue_apply (v : FinitePlace K) (x : K) : v.floorValue (v x) = v x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have ht := (pos_iff (w := v)).mpr hx
  exact le_antisymm (v.floorValue_le ht.le)
    ((v.apply_le_iff_le_floorValue ht x).mp le_rfl)

/-- One is already a finite-place value. -/
@[simp]
theorem floorValue_one (v : FinitePlace K) : v.floorValue 1 = 1 := by
  simpa using v.floorValue_apply 1

/-- Value floors are monotone even across the nonpositive boundary. -/
theorem floorValue_mono (v : FinitePlace K) : Monotone v.floorValue := by
  intro s t hst
  by_cases hs : 0 < s
  · obtain ⟨x, _, hx⟩ := v.exists_apply_eq_floorValue hs
    rw [← hx]
    exact (v.apply_le_iff_le_floorValue (hs.trans_le hst) x).mp
      (hx.le.trans ((v.floorValue_le hs.le).trans hst))
  · rw [v.floorValue_of_nonpos (le_of_not_gt hs)]
    exact v.floorValue_nonneg t

/-- In particular, rounding is idempotent. -/
@[simp]
theorem floorValue_floorValue (v : FinitePlace K) (t : ℝ) :
    v.floorValue (v.floorValue t) = v.floorValue t := by
  by_cases ht : 0 < t
  · obtain ⟨x, _, hx⟩ := v.exists_apply_eq_floorValue ht
    rw [← hx, v.floorValue_apply]
  · simp [v.floorValue_of_nonpos (le_of_not_gt ht)]

-- At a prime of norm two, a bound of 3/2 defines the same local condition as a bound of one.
-- Thus real bounds cannot be substituted for their value floors in exact covolume formulas.
example (v : FinitePlace K) (hv : v.maximalIdeal.asIdeal.absNorm = 2) :
    v.floorValue (3 / 2) = 1 := by
  rw [v.floorValue_of_pos (by norm_num), hv]
  have hf : ⌊(3 / 2 : ℝ)⌋₊ = 1 := (Nat.floor_eq_iff (by norm_num)).mpr (by norm_num)
  norm_num [Int.log, hf, Nat.log_of_lt]

end NumberField.FinitePlace
