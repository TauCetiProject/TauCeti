/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Exponential
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.Unimodality

/-!
# Localization of the Gamma kernel

The kernel `u^k exp (-a u) / k!` in the Taylor coefficients of a Laplace transform is
concentrated near `k / a`. For a fixed ratio `λ > 1` and a sufficiently large `U`, one
can choose a degree `k` at least `U` for which the kernel outside `[U, λ U]` is bounded
by `a⁻ᵏ q^k`, with `q < 1` depending only on `λ`. The pointwise estimate lets one bound
the contribution outside the window against an integrable function, without requiring a
pointwise growth bound on that function.
-/

public section

open Set Real
open scoped Nat

namespace TauCeti

/-- The Gamma kernel, in the coordinate `t = a u / k`, is bounded by
`a⁻ᵏ (t exp (1 - t))^k`. For `k = 0` the bound is `1`. -/
theorem pow_mul_exp_neg_mul_div_factorial_le_profile {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u)
    (k : ℕ) :
    u ^ k * exp (-a * u) / (k ! : ℝ) ≤
      (a ^ k)⁻¹ * (a * u / k * exp (1 - a * u / k)) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using exp_le_one_iff.mpr (by nlinarith [mul_nonneg ha.le hu] : -a * u ≤ 0)
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  let t : ℝ := a * u / k
  have ht : t * k = a * u := div_mul_cancel₀ _ hkR.ne'
  have hexp : exp (1 - t) ^ k * exp (-(k : ℝ)) = exp (-a * u) := by
    rw [← exp_natCast_mul, ← exp_add]
    congr 1
    linear_combination -ht
  have hpow : t ^ k * (k : ℝ) ^ k = a ^ k * u ^ k := by
    rw [← mul_pow, ht, mul_pow]
  -- Separate the value at the mode from the factor that depends on the rescaled coordinate.
  have hmode : (k : ℝ) ^ k * exp (-(k : ℝ)) / (k ! : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    simpa using pow_mul_exp_neg_mul_le (a := 1) one_pos hkR.le k
  calc
    _ = (a ^ k)⁻¹ * (t * exp (1 - t)) ^ k * ((k : ℝ) ^ k * exp (-(k : ℝ)) / (k ! : ℝ)) := by
      symm
      rw [mul_pow]
      calc
        _ = (a ^ k)⁻¹ * (t ^ k * (k : ℝ) ^ k) * (exp (1 - t) ^ k * exp (-(k : ℝ))) /
            (k ! : ℝ) := by ring
        _ = _ := by rw [hpow, hexp, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]
    _ ≤ (a ^ k)⁻¹ * (t * exp (1 - t)) ^ k := mul_le_of_le_one_right (by positivity) hmode

/-- Outside the window `[U, λ U]`, the Gamma kernel of degree `⌈a √λ U⌉` is exponentially small
in that degree. Here `q` is the larger of the two profile values at `1 / √λ` and `λ^(1/4)`;
the lower bound on `U` leaves enough room to round the degree up. -/
theorem pow_mul_exp_neg_mul_div_factorial_le_off_window {a L U : ℝ} (hL : 1 < L)
    (ha : 1 ≤ a * √L) (hU : (a * √L * (√(√L) - 1))⁻¹ ≤ U) :
    let profile := fun t : ℝ ↦ t * exp (1 - t)
    let k := ⌈a * √L * U⌉₊
    let q := max (profile (√L)⁻¹) (profile (√(√L)))
    0 < q ∧ q < 1 ∧ U ≤ (k : ℝ) ∧
      ∀ u ≥ 0, u ∉ Icc U (L * U) →
        u ^ k * exp (-a * u) / (k ! : ℝ) ≤ (a ^ k)⁻¹ * q ^ k := by
  dsimp only
  set s := √L
  set r := √s
  set k := ⌈a * s * U⌉₊
  let profile := fun t : ℝ ↦ t * exp (1 - t)
  have hs : 1 < s := by simpa [s] using sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hL
  have hr : 1 < r := by simpa [r] using sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hs
  have ha₀ : 0 < a := pos_of_mul_pos_left (zero_lt_one.trans_le ha) (by positivity)
  have hsInv : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
  have hU₀ : 0 < U := (inv_pos.mpr (mul_pos (zero_lt_one.trans_le ha) (sub_pos.mpr hr))).trans_le hU
  have hbase : a * s * U ≤ (k : ℝ) := Nat.le_ceil _
  have hkU : U ≤ (k : ℝ) := (le_mul_of_one_le_left hU₀.le ha).trans hbase
  have hk₀ : (0 : ℝ) < k := hU₀.trans_le hkU
  -- The cutoff leaves room for the ceiling between `a √L U` and `a L^(3/4) U`.
  have hkUpper : (k : ℝ) ≤ a * s * U * r := by
    have hden : 0 < a * s * (r - 1) := mul_pos (zero_lt_one.trans_le ha) (sub_pos.mpr hr)
    have hroom := (inv_le_iff_one_le_mul₀ hden).mp hU
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ a * s * U)).le.trans (by nlinarith [hroom])
  refine ⟨lt_max_of_lt_left (by positivity : 0 < profile s⁻¹),
    max_lt (mul_exp_one_sub_lt_one hsInv.ne) (mul_exp_one_sub_lt_one hr.ne'), hkU, ?_⟩
  intro u hu hout
  let t := a * u / (k : ℝ)
  have ht : 0 ≤ t := by positivity
  have htail : profile t ≤ max (profile s⁻¹) (profile r) := by
    rcases not_and_or.mp (fun h ↦ hout (mem_Icc.mpr h)) with hl | hh
    · have ht' : t ≤ s⁻¹ := by
        dsimp only [t]
        rw [div_le_iff₀ hk₀, ← div_eq_inv_mul, le_div_iff₀ (by positivity : 0 < s)]
        have hlow : u ≤ U := le_of_not_ge hl
        calc
          a * u * s ≤ a * U * s := by gcongr
          _ = a * s * U := by ring
          _ ≤ k := hbase
      exact (strictMonoOn_mul_exp_one_sub.monotoneOn (ht'.trans hsInv.le) hsInv.le ht').trans
        (le_max_left ..)
    · have ht' : r ≤ t := by
        dsimp only [t]
        rw [le_div_iff₀ hk₀]
        calc
          r * (k : ℝ) ≤ r * (a * s * U * r) := by gcongr
          _ = a * (L * U) := by
            have hrs : r ^ 2 = s := sq_sqrt (by positivity)
            have hsL : s ^ 2 = L := sq_sqrt (by linarith)
            linear_combination hrs * (a * s * U) + hsL * (a * U)
          _ ≤ a * u := mul_le_mul_of_nonneg_left (le_of_not_ge hh) ha₀.le
      exact (strictAntiOn_mul_exp_one_sub.antitoneOn hr.le (hr.le.trans ht') ht').trans
        (le_max_right ..)
  exact (pow_mul_exp_neg_mul_div_factorial_le_profile ha₀ hu k).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg ht (exp_pos _).le) htail k) (by positivity))

end TauCeti
