/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Ranks
import TauCeti.NumberTheory.NumberField.Cyclotomic.RootDiscr
import TauCeti.NumberTheory.NumberField.Discriminant.Basic

/-!
# Root-discriminant bounds at the prime-sum scale

A number field containing a primitive root of order `q₁(s)` contains the dyadic
cyclotomic field of order `2 ^ (s + 1)`, whose root discriminant `2 ^ s` gives the
lower bound `x^11` at the ranks used in the prime sums.

For a quadratic base of absolute discriminant `d`, the root discriminant of the cyclotomic
host of level `q₁ s` is at most `x^12` at the separated scales. The factor from the base
field is bounded by `d`, and the margin between `x^11` and `x^12` absorbs it together
with the initial modulus and the logarithmic factor in the tower level.

The target scale is that of `New.Data.rootDiscr_mem_Icc` in
`grh/src/New/Derivatives/Field/ChosenPlaces.lean` of lsernau/grh-lean (`72fead1`). Neither bound
needs estimates at individual infinite places: the lower bound uses the dyadic subfield and
the upper bound uses the compositum formula.
-/

public section

open NumberField Real

namespace TauCeti.OneSidedBound.Parameters

/-- At prime-sum scale `x`, the dyadic subfield alone forces the root discriminant
of the host to be at least `x ^ 11`. -/
theorem pow_le_rootDiscr (P : Parameters) {E : Type*} [Field E] [NumberField E]
    {s x m : ℕ} {ζ : E} (hζ : IsPrimitiveRoot ζ (P.q₁ s))
    (hm : x ≤ m ^ 2) (hs : m ^ 22 ≤ 2 ^ s) :
    (x : ℝ) ^ 11 ≤ rootDiscr E := by
  obtain ⟨a, ha⟩ := P.two_pow_succ_dvd_q₁ s
  have hζ' : IsPrimitiveRoot (ζ ^ a) (2 ^ (s + 1)) :=
    hζ.pow (P.q₁_pos s) (ha.trans (Nat.mul_comm _ _))
  have hdisc : (2 : ℝ) ^ s ≤ rootDiscr E := by
    have hexp : (s : ℝ) + 1 - ((2 : ℝ) - 1)⁻¹ = s := by norm_num
    simpa only [Nat.cast_ofNat, hexp, Real.rpow_natCast] using hζ'.rpow_le_rootDiscr Nat.prime_two
  have hx : x ^ 11 ≤ 2 ^ s := calc
    x ^ 11 ≤ (m ^ 2) ^ 11 := Nat.pow_le_pow_left hm _
    _ ≤ 2 ^ s := by rwa [← pow_mul]
  exact (by exact_mod_cast hx : (x : ℝ) ^ 11 ≤ 2 ^ s).trans hdisc

/-- The cyclotomic level times the base discriminant fits into the upper scale `x^12`. -/
theorem d_mul_q₁_le_pow_twelve (P : Parameters) {s : ℕ} {x : ℝ}
    (hlog : 10 ^ 14 * max (P.q₀ : ℝ) P.d ≤ log x)
    (hdyadic : (2 : ℝ) ^ s ≤ 2 ^ 22 * x ^ 11) : (P.d : ℝ) * P.q₁ s ≤ x ^ 12 := by
  have hodd : Odd (11 : ℕ) := by decide
  have hx : 0 < x := hodd.pow_pos_iff.mp
    (pos_of_mul_pos_right ((by positivity : (0 : ℝ) < 2 ^ s).trans_le hdyadic) (by positivity))
  have hd₁ : (1 : ℝ) ≤ P.d := by exact_mod_cast P.prime_d.one_le
  have hQ := (mul_le_mul_of_nonneg_left (le_max_left (P.q₀ : ℝ) (P.d : ℝ))
    (by norm_num : 0 ≤ (10 : ℝ) ^ 14)).trans hlog
  have hD := (mul_le_mul_of_nonneg_left (le_max_right (P.q₀ : ℝ) (P.d : ℝ))
    (by norm_num : 0 ≤ (10 : ℝ) ^ 14)).trans hlog
  have hlog₆ : 6 ≤ log x := by linarith
  have hlog₁ : 1 ≤ log x := by linarith
  have hs := towerExponent_le hlog₆ hdyadic
  have hL : l₀ s ≤ 81 * (s + 1) := by
    rcases eq_or_ne s 0 with rfl | hs₀
    · norm_num [l₀_def]
    · exact (l₀_le hs₀).trans (by omega)
  have hL' : (l₀ s : ℝ) ≤ (81 * 33) * log x := by
    have h := Nat.cast_le (α := ℝ).mpr hL
    push_cast at h
    linarith
  have hlog₀ : 0 ≤ log x := zero_le_one.trans hlog₁
  have hx₄ : log x ^ 4 / 24 ≤ x := by
    have h := Real.pow_div_factorial_le_exp (log x) hlog₀ 4
    norm_num [Real.exp_log hx, Nat.factorial] at h
    exact h
  have hbudget : (P.d : ℝ) * P.q₀ * (3 * (81 * 33) * (2 : ℝ) ^ 22) * log x ≤ x := by
    calc
      _ ≤ (log x / 10 ^ 14) * (log x / 10 ^ 14) *
          (3 * (81 * 33) * (2 : ℝ) ^ 22) * log x := by gcongr <;> linarith
      _ = (3 * (81 * 33) * 2 ^ 22 / (10 : ℝ) ^ 28) * log x ^ 3 := by ring
      _ ≤ log x ^ 3 / 24 := by
        rw [div_eq_inv_mul (log x ^ 3)]
        exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hlog₀ _)
      _ ≤ log x ^ 4 / 24 :=
        div_le_div_of_nonneg_right (pow_le_pow_right₀ hlog₁ (by decide)) (by norm_num)
      _ ≤ x := hx₄
  rw [q₁_def, towerDeg_def]
  push_cast
  calc
    _ ≤ (P.d : ℝ) * (P.q₀ * (3 * ((81 * 33) * log x) * (2 ^ 22 * x ^ 11))) := by gcongr
    _ = ((P.d : ℝ) * P.q₀ * (3 * (81 * 33) * (2 : ℝ) ^ 22) * log x) * x ^ 11 := by ring
    _ ≤ x ^ 12 := by simpa only [← pow_succ' x 11] using
      mul_le_mul_of_nonneg_right hbudget (pow_nonneg hx.le 11)

/-- At the prime-sum scale `x`, the cyclotomic host has root discriminant at most `x^12`.
The logarithmic separation follows from `1 < b`, `(log b)^100 ≤ x`, and
`log (log b) ≥ 10^12 * max q₀ d`. -/
theorem rootDiscr_le_pow_twelve (P : Parameters) (K E : Type*) [Field K] [Field E]
    [NumberField K] [NumberField E] [Algebra K E]
    {s : ℕ} [IsCyclotomicExtension {P.q₁ s} K E] (hK : (discr K).natAbs = P.d) {x : ℝ}
    (hlog : 10 ^ 14 * max (P.q₀ : ℝ) P.d ≤ log x)
    (hdyadic : (2 : ℝ) ^ s ≤ 2 ^ 22 * x ^ 11) : rootDiscr E ≤ x ^ 12 := by
  have hq : (discr K).natAbs.Coprime (P.q₁ s) := hK ▸ (P.coprime_q₁_d s).symm
  have hbase : rootDiscr K ≤ P.d := hK ▸ TauCeti.NumberField.rootDiscr_le_natAbs_discr K
  rw [IsCyclotomicExtension.rootDiscr_eq_mul_of_coprime_level K E (P.q₁ s) hq]
  have : NeZero (P.q₁ s : ℚ) := ⟨Nat.cast_ne_zero.mpr (P.q₁_pos s).ne'⟩
  have : IsCyclotomicExtension {P.q₁ s} ℚ (CyclotomicField (P.q₁ s) ℚ) :=
    CyclotomicField.isCyclotomicExtension (P.q₁ s) ℚ
  have hc := IsCyclotomicExtension.Rat.rootDiscr_le (P.q₁ s) (CyclotomicField (P.q₁ s) ℚ)
  exact (mul_le_mul hbase hc (by rw [rootDiscr_def]; positivity) (Nat.cast_nonneg _)).trans
    (P.d_mul_q₁_le_pow_twelve hlog hdyadic)

end TauCeti.OneSidedBound.Parameters
