/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Choosing the Perron height for a conductor-uniform prime sum

In a truncated explicit formula, increasing the height `T` improves the truncation error but
worsens the zero-free region through `log (q * (T + 2))`. Choosing
`T = max (exp (sqrt (log x))) q` gives a saving with denominator `sqrt (log x) + log q`.
The height also controls the endpoint error in a dyadic decomposition of the prime sum.

For the prime number theorem with the exceptional term, see Iwaniec–Kowalski,
*Analytic Number Theory*, Theorem 5.27.
-/

public section

open Real

namespace TauCeti

/-- The logarithmic prefactor at the original cutoff is bounded by the fourth power of the
logarithmic conductor, times a polynomial in the exponent available for the saving. -/
private theorem log_prefactor_le {u L : ℝ} (hu : 1 ≤ u) (hL : 0 ≤ L) :
    (u + L) ^ 2 ≤ 64 * u ^ 4 * (1 + L / (√L + u)) ^ 4 := by
  let r := L / (√L + u)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hs : √L ≤ u + 2 * r := by
    by_cases h : √L ≤ u
    · linarith
    · have hm : (√L + u) * √L ≤ 2 * L := by
        nlinarith [Real.sq_sqrt hL,
          mul_nonneg (Real.sqrt_nonneg L) (sub_nonneg.mpr (le_of_not_ge h))]
      have h' : √L ≤ 2 * r := by
        dsimp [r]
        rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
        simpa only [mul_comm] using hm
      linarith
  have hs' : √L ≤ 2 * (u * (1 + r)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) hr]
  have hsq : L ≤ (2 * (u * (1 + r))) ^ 2 :=
    (Real.sq_sqrt hL) ▸ pow_le_pow_left₀ (Real.sqrt_nonneg _) hs' 2
  have hu' : u ≤ (2 * (u * (1 + r))) ^ 2 := by
    refine (le_self_pow₀ hu (by decide : 2 ≠ 0)).trans (pow_le_pow_left₀ (by linarith) ?_ 2)
    nlinarith [mul_nonneg (show 0 ≤ u by linarith) hr]
  have hlog : u + L ≤ 2 * (2 * (u * (1 + r))) ^ 2 := by linarith
  calc
    (u + L) ^ 2 ≤ (2 * (2 * (u * (1 + r))) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hlog _
    _ = 64 * u ^ 4 * (1 + r) ^ 4 := by ring

/-- At the selected height, the logarithmic height lies between `2` and `log x / 2`. -/
private theorem perron_log_height_mem_Icc {L u : ℝ} (hL : 4 ≤ L) (huL : u ≤ L / 2) :
    max (√L) u ∈ Set.Icc (2 : ℝ) (L / 2) :=
  ⟨(Real.le_sqrt_of_sq_le (by linarith : (2 : ℝ) ^ 2 ≤ L)).trans (le_max_left _ _),
    max_le (Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [sq_nonneg (L - 4)]⟩) huL⟩

/-- The zero-free-region term at the selected height has the same logarithmic prefactor as
truncated Perron, and a decay rate of at least `a / 3` in the mixed conductor scale. -/
private theorem perron_zero_error_at_height {a L u : ℝ} (ha : 0 ≤ a) (hL : 4 ≤ L)
    (hu : 0 ≤ u) (huL : u ≤ L / 2) :
    let r := L / (√L + u)
    let ell := u + log (exp (max (√L) u) + 2)
    ell ^ 2 * (exp L * exp (-a * L / ell)) ≤
      (u + L) ^ 2 * (exp L * exp (-(a / 3) * r)) := by
  let w := max (√L) u
  intro r ell
  obtain ⟨hw, hwL⟩ := perron_log_height_mem_Icc hL huL
  have hwexp : 2 ≤ exp w := by linarith [Real.add_one_le_exp w]
  have hlog : log (exp w + 2) ≤ w + 1 := by
    calc
      log (exp w + 2) ≤ log (exp w * exp 1) := by
        apply Real.log_le_log (by positivity)
        have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp 1) (exp_pos w).le
        linarith only [h, hwexp]
      _ = w + 1 := by rw [← Real.exp_add, Real.log_exp]
  have he₀ : 0 < ell := by
    dsimp [ell]
    exact add_pos_of_nonneg_of_pos hu (Real.log_pos (by linarith))
  have he : ell ≤ 3 * (√L + u) := by
    have : w ≤ √L + u := max_le (by linarith) (by linarith [Real.sqrt_nonneg L])
    dsimp only [ell]
    linarith [Real.sqrt_nonneg L]
  have he' : ell ≤ u + L := by dsimp only [ell]; linarith
  have hwin : (a / 3) * r ≤ a * L / ell := by
    calc
      (a / 3) * r = (a * L) / (3 * (√L + u)) := by
        dsimp [r]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) he₀ he
  rw [neg_mul, neg_div, neg_mul]
  gcongr

/-- The saving from the zero-free region and the three other errors at the selected height,
prior to absorbing logarithmic factors. -/
private theorem perron_error_at_height {a L u : ℝ} (ha : 0 ≤ a) (hL : 4 ≤ L)
    (hu : 0 ≤ u) (huL : u ≤ L / 2) :
    let w := max (√L) u
    let r := L / (√L + u)
    let b := min (a / 3) 1
    let ell := u + log (exp w + 2)
    ell ^ 2 * (exp L * exp (-a * L / ell)) +
        (exp L / exp w) * (u + L) ^ 2 + exp w + L * (u + L) ^ 2 ≤
      5 * (u + L) ^ 2 * (exp L * exp (-b * r)) := by
  intro w r b ell
  have hL₀ : 0 ≤ L := by linarith
  have hwL : w ≤ L / 2 := (perron_log_height_mem_Icc hL huL).2
  have hden : 0 < √L + u := add_pos_of_pos_of_nonneg (Real.sqrt_pos_of_pos (by linarith)) hu
  have hr : 0 ≤ r := div_nonneg hL₀ hden.le
  have hrw : r ≤ w := by
    apply (div_le_iff₀ hden).mpr
    calc
      L = √L ^ 2 := (Real.sq_sqrt hL₀).symm
      _ ≤ w * (√L + u) := by
        rw [pow_two]
        exact mul_le_mul (le_max_left _ _) (le_add_of_nonneg_right (by linarith))
          (Real.sqrt_nonneg _) (by positivity)
  have hbr : b * r ≤ w := (mul_le_of_le_one_left hr (min_le_right _ _)).trans hrw
  have hzero : ell ^ 2 * (exp L * exp (-a * L / ell)) ≤
      (u + L) ^ 2 * (exp L * exp (-b * r)) := by
    refine (perron_zero_error_at_height ha hL hu huL).trans ?_
    gcongr
    exact min_le_left (a / 3) 1
  have hcut : exp L / exp w ≤ exp L * exp (-b * r) := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (exp_pos L).le
  have hend : exp w ≤ exp L * exp (-b * r) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hdyad : L ≤ 2 * (exp L * exp (-b * r)) := by
    rw [← Real.exp_add]
    linarith [Real.add_one_le_exp (L / 2), Real.exp_le_exp.mpr
      (show L / 2 ≤ L + -b * r by linarith)]
  have hB : 1 ≤ (u + L) ^ 2 := one_le_pow₀ (by linarith)
  let E := exp L * exp (-b * r)
  let B := (u + L) ^ 2
  have hcut' := mul_le_mul_of_nonneg_right hcut (sq_nonneg (u + L))
  have hend' : exp w ≤ B * E := hend.trans (le_mul_of_one_le_left (by positivity) hB)
  have hdyad' := mul_le_mul_of_nonneg_right hdyad (sq_nonneg (u + L))
  refine (add_le_add (add_le_add (add_le_add hzero hcut') hend') hdyad').trans ?_
  exact (le_of_eq (by ring) : B * E + E * B + B * E + (2 * E) * B ≤ 5 * B * E)

/-- For any fixed positive zero-free-region constant `a`, there is a single constant `C`
bounding the sum of the zero-free-region, truncation and dyadic errors at the height
`max (exp (√(log x))) q`, which lies between `max 2 q` and `√x`. The decay rate is
`min (a / 3) 1 / 2`, and the logarithmic prefactor is `(log q) ^ 4`. -/
theorem exists_perronHeight_mixedExponentialError {a : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∀ {q x : ℝ}, exp 1 ≤ q → exp 4 ≤ x → q ≤ √x →
      let T := max (exp (√(log x))) q
      let ell := log (q * (T + 2))
      T ∈ Set.Icc (max 2 q) (√x) ∧
        ell ^ 2 * (x * exp (-a * log x / ell)) + x / T * log (q * x) ^ 2 +
            T + log x * log (q * x) ^ 2 ≤
          C * x * (log q) ^ 4 * exp (-(min (a / 3) 1 / 2) * (log x / (√(log x) + log q))) := by
  let b := min (a / 3) 1 / 2
  have hb : 0 < b := half_pos (lt_min (by positivity) zero_lt_one)
  refine ⟨320 * ((4 : ℕ).factorial * exp b / b ^ 4), by positivity, ?_⟩
  intro q x hq hx hqx
  have hq₀ : 0 < q := (exp_pos _).trans_le hq
  have hx₀ : 0 < x := (exp_pos _).trans_le hx
  have hu : 1 ≤ log q := (Real.le_log_iff_exp_le hq₀).mpr hq
  have hL : 4 ≤ log x := (Real.le_log_iff_exp_le hx₀).mpr hx
  have huL : log q ≤ log x / 2 := by
    rw [← Real.log_sqrt hx₀.le]
    exact Real.log_le_log hq₀ hqx
  let L := log x
  let u := log q
  let w := max (√L) u
  let r := L / (√L + u)
  have hT : max (exp (√L)) q = exp w := by
    rw [show exp w = max (exp (√L)) (exp u) from Real.exp_monotone.map_max, Real.exp_log hq₀]
  dsimp only
  rw [hT]
  refine ⟨⟨max_le ?_ ?_, ?_⟩, ?_⟩
  · have hw : 2 ≤ w := (perron_log_height_mem_Icc hL huL).1
    linarith [Real.add_one_le_exp w]
  · rw [← Real.exp_log hq₀]
    exact Real.exp_le_exp.mpr (le_max_right _ _)
  · rw [← Real.exp_log (Real.sqrt_pos_of_pos hx₀), Real.log_sqrt hx₀.le]
    exact Real.exp_le_exp.mpr (perron_log_height_mem_Icc hL huL).2
  have h := perron_error_at_height ha.le hL (zero_le_one.trans hu) huL
  simp only [Real.exp_log hx₀] at h
  rw [Real.log_mul hq₀.ne' hx₀.ne', Real.log_mul hq₀.ne' (by positivity : exp w + 2 ≠ 0)]
  refine h.trans ?_
  have hr : 0 ≤ r := by dsimp [r, L, u]; positivity
  have hpoly : (u + L) ^ 2 ≤ 64 * u ^ 4 * (1 + r) ^ 4 :=
    log_prefactor_le hu (by linarith : 0 ≤ L)
  have hb' : min (a / 3) 1 = b + b := by dsimp [b]; ring
  calc
    5 * (log q + log x) ^ 2 * (x * exp (-(min (a / 3) 1) * r)) ≤
        5 * (64 * u ^ 4 * (1 + r) ^ 4) * (x * exp (-(min (a / 3) 1) * r)) := by
      gcongr
    _ = 320 * (x * u ^ 4) * ((1 + r) ^ 4 * exp (-(b + b) * r)) := by rw [hb']; ring
    _ ≤ 320 * (x * u ^ 4) * (((4 : ℕ).factorial * exp b / b ^ 4) * exp (-b * r)) :=
      mul_le_mul_of_nonneg_left (one_add_pow_mul_exp_neg_add_mul_le (t := r) hb
        (by linarith) 4) (by positivity)
    _ = _ := by ring

end TauCeti
