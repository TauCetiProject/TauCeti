/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Oscillatory trigonometric integrals over arbitrary intervals

High-frequency oscillations average out over every interval: the integral of `cos (k * x + c)`
over `[a, b]` is at most `2 / k` in absolute value (`TauCeti.abs_integral_cos_mul_add_le`).
Consequently the integral of `sin (k * x + c) ^ 2` over `[a, b]` is at least `(b - a) / 2 - 1 / k`
(`TauCeti.integral_sin_mul_add_sq_ge`), and two oscillations of frequencies `m` and `n` are
asymptotically orthogonal on any nondegenerate interval: for `n` large compared with `m`, the
integral of `(sin (m * x + c) - sin (n * x + c)) ^ 2` over `[a, b]` is at least `(b - a) / 4`
(`TauCeti.eventually_integral_sin_sub_sin_sq_ge`).

Over a quarter period the two squares balance exactly: with `k = π / (2 (b - a))`, both
`sin (k (x - a)) ^ 2` and `cos (k (x - a)) ^ 2` integrate to `(b - a) / 2` over `[a, b]`
(`TauCeti.integral_sin_sq_and_integral_cos_sq_quarter_period`).

For power-damped oscillations `t ^ α * cos (c * t ^ p + φ)` on positive intervals `[x, R]`
(`c ≠ 0`, `0 < p`), `TauCeti.integral_rpow_mul_cos_add` records finite-interval integration by
parts.
-/

public section

open Filter MeasureTheory Real
open scoped Interval

namespace TauCeti

/-- The integral of `cos (k * x + c)` over any interval is at most `2 / k` in absolute value. -/
theorem abs_integral_cos_mul_add_le {k : ℝ} (hk : 0 < k) (a b c : ℝ) :
    |∫ x in a..b, cos (k * x + c)| ≤ 2 / k := by
  rw [intervalIntegral.integral_comp_mul_add (fun x => cos x) hk.ne' c, integral_cos,
    smul_eq_mul, abs_mul, abs_inv, abs_of_pos hk, inv_mul_eq_div]
  gcongr
  calc |sin (k * b + c) - sin (k * a + c)| ≤ |sin (k * b + c)| + |sin (k * a + c)| :=
        abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (abs_sin_le_one _) (abs_sin_le_one _)
    _ = 2 := by norm_num

/-- The integral of `sin (k * x + c) ^ 2` over `[a, b]` is at least `(b - a) / 2 - 1 / k`. -/
theorem integral_sin_mul_add_sq_ge {k : ℝ} (hk : 0 < k) {a b : ℝ} (c : ℝ) :
    (b - a) / 2 - 1 / k ≤ ∫ x in a..b, sin (k * x + c) ^ 2 := by
  have hpt : ∀ x, sin (k * x + c) ^ 2 = 1 / 2 - cos ((2 * k) * x + 2 * c) / 2 := by
    intro x
    rw [sin_sq_eq_half_sub, show (2 * k) * x + 2 * c = 2 * (k * x + c) by ring]
  simp_rw [hpt]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const, intervalIntegral.integral_div, smul_eq_mul]
  have h := abs_integral_cos_mul_add_le (by positivity : 0 < 2 * k) a b (2 * c)
  have h' := (abs_le.1 h).2
  have : 2 / (2 * k) = 1 / k := by field_simp
  have : 0 < 1 / k := by positivity
  linarith

/-- Two oscillations `sin (m * x + c)` and `sin (n * x + c)` stay a definite `L²` distance apart
on a nondegenerate interval `[a, b]`: for all sufficiently large `n`, the integral of the square
of their difference is at least `(b - a) / 4`. -/
theorem eventually_integral_sin_sub_sin_sq_ge {a b : ℝ} (hab : a < b) (c : ℝ) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (b - a) / 4 ≤ ∫ x in a..b, (sin (m * x + c) - sin (n * x + c)) ^ 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (20 / (b - a))
  filter_upwards [eventually_ge_atTop (m + N + 1)] with n hn
  have hnm : (N : ℝ) + 1 ≤ (n : ℝ) - m := by
    have : ((m + N + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this
    linarith
  have hba : 0 < b - a := sub_pos.2 hab
  have hd : 0 < (n : ℝ) - m := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hn0 : 0 < (n : ℝ) := by linarith
  -- Pointwise lower bound after discarding `sin (m * x + c) ^ 2 ≥ 0`.
  have hpt : ∀ x, 1 / 2 - cos ((2 * n) * x + 2 * c) / 2 - cos ((n - m) * x + 0) +
      cos ((n + m) * x + 2 * c) ≤ (sin (m * x + c) - sin (n * x + c)) ^ 2 := by
    intro x
    have h1 : cos ((2 * n) * x + 2 * c) = 1 - 2 * sin (n * x + c) ^ 2 := by
      rw [show (2 * n) * x + 2 * c = 2 * (n * x + c) by ring, cos_two_mul, cos_sq']
      ring
    have h2 : cos ((n - m) * x + 0) = cos (n * x + c) * cos (m * x + c) +
        sin (n * x + c) * sin (m * x + c) := by
      rw [show ((n : ℝ) - m) * x + 0 = (n * x + c) - (m * x + c) by ring, cos_sub]
    have h3 : cos ((n + m) * x + 2 * c) = cos (n * x + c) * cos (m * x + c) -
        sin (n * x + c) * sin (m * x + c) := by
      rw [show ((n : ℝ) + m) * x + 2 * c = (n * x + c) + (m * x + c) by ring, cos_add]
    rw [h1, h2, h3]
    nlinarith [sq_nonneg (sin (m * x + c))]
  have hint : ∫ x in a..b, (1 / 2 - cos ((2 * n) * x + 2 * c) / 2 - cos ((n - m) * x + 0) +
      cos ((n + m) * x + 2 * c)) = (b - a) / 2 - (∫ x in a..b, cos ((2 * n) * x + 2 * c)) / 2 -
        (∫ x in a..b, cos ((n - m) * x + 0)) + ∫ x in a..b, cos ((n + m) * x + 2 * c) := by
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_sub intervalIntegrable_const
        (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const, intervalIntegral.integral_div, smul_eq_mul]
    ring
  have hmono := intervalIntegral.integral_mono_on hab.le
    (Continuous.intervalIntegrable (μ := volume) (by fun_prop) a b)
    (Continuous.intervalIntegrable (μ := volume) (by fun_prop) a b) (fun x _ => hpt x)
  rw [hint] at hmono
  have e1 := (abs_le.1 (abs_integral_cos_mul_add_le (by positivity : 0 < 2 * (n : ℝ)) a b
    (2 * c))).2
  have e2 := (abs_le.1 (abs_integral_cos_mul_add_le hd a b 0)).2
  have e3 := (abs_le.1 (abs_integral_cos_mul_add_le (by positivity : 0 < (n : ℝ) + m) a b
    (2 * c))).1
  have b1 : 2 / (2 * (n : ℝ)) ≤ 1 / ((n : ℝ) - m) := by
    rw [div_le_div_iff₀ (by positivity) hd]; linarith
  have b3 : 2 / ((n : ℝ) + m) ≤ 2 / ((n : ℝ) - m) :=
    div_le_div_of_nonneg_left (by norm_num) hd (by linarith)
  have b4 : 5 / ((n : ℝ) - m) ≤ (b - a) / 4 := by
    rw [div_le_div_iff₀ hd (by norm_num)]
    have : 20 / (b - a) < (n : ℝ) - m := by linarith
    rw [div_lt_iff₀ hba] at this
    nlinarith
  have : 5 / ((n : ℝ) - m) = 1 / ((n : ℝ) - m) / 2 + 2 / ((n : ℝ) - m) + 2 / ((n : ℝ) - m) +
      1 / ((n : ℝ) - m) / 2 := by ring
  have : 0 < 1 / ((n : ℝ) - m) := by positivity
  linarith

/-- Finite-interval integration by parts for power-weighted oscillatory cosines
`t ^ α * cos (c * t ^ p + φ)` on `[x, R]` with `0 < x`, `0 < R`, `c ≠ 0`, and `0 < p`. -/
theorem integral_rpow_mul_cos_add {c p α φ x R : ℝ}
    (hc : c ≠ 0) (hp : 0 < p) (hx : 0 < x) (hR : 0 < R) :
    ∫ t in x..R, t ^ α * cos (c * t ^ p + φ) =
      (c * p)⁻¹ * R ^ (α - p + 1) * sin (c * R ^ p + φ) -
        (c * p)⁻¹ * x ^ (α - p + 1) * sin (c * x ^ p + φ) -
        ((α - p + 1) / (c * p)) *
          ∫ t in x..R, t ^ (α - p) * cos (c * t ^ p + (φ - π / 2)) := by
  let u : ℝ → ℝ := fun t ↦ (c * p)⁻¹ * t ^ (α - p + 1)
  let u' : ℝ → ℝ := fun t ↦ ((α - p + 1) / (c * p)) * t ^ (α - p)
  let v : ℝ → ℝ := fun t ↦ sin (c * t ^ p + φ)
  let v' : ℝ → ℝ := fun t ↦ cos (c * t ^ p + φ) * (c * (p * t ^ (p - 1)))
  have hpos : ∀ t ∈ [[x, R]], 0 < t := fun _ ht ↦ (lt_min hx hR).trans_le ht.1
  have hrp (q : ℝ) : ContinuousOn (fun t : ℝ ↦ t ^ q) [[x, R]] :=
    ContinuousOn.rpow_const continuousOn_id fun t ht ↦ Or.inl (hpos t ht).ne'
  have hu : ∀ t ∈ [[x, R]], HasDerivAt u (u' t) t := fun t ht ↦ by
    have hexp : α - p + 1 - 1 = α - p := by ring
    refine ((hasDerivAt_rpow_const (p := α - p + 1)
      (Or.inl (hpos t ht).ne')).const_mul (c * p)⁻¹).congr_deriv ?_
    dsimp [u']; rw [hexp]; ring
  have hv : ∀ t ∈ [[x, R]], HasDerivAt v (v' t) t := fun t ht ↦
    ((((hasDerivAt_rpow_const (p := p)
      (Or.inl (hpos t ht).ne')).const_mul c).add_const φ).sin).congr_deriv rfl
  have hu'_cont : ContinuousOn u' [[x, R]] := continuousOn_const.mul (hrp _)
  have hv'_cont : ContinuousOn v' [[x, R]] :=
    (continuous_cos.comp_continuousOn ((continuousOn_const.mul (hrp p)).add
      continuousOn_const)).mul (continuousOn_const.mul (continuousOn_const.mul (hrp _)))
  have hcongr : ∫ t in x..R, t ^ α * cos (c * t ^ p + φ) = ∫ t in x..R, u t * v' t := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    dsimp [u, v']
    have hexp : (α - p + 1) + (p - 1) = α := by ring
    calc
      t ^ α * cos (c * t ^ p + φ)
          = ((c * p)⁻¹ * (c * p)) * (t ^ (α - p + 1) * t ^ (p - 1)) * cos (c * t ^ p + φ) := by
            rw [inv_mul_cancel₀ (mul_ne_zero hc hp.ne'), one_mul, ← rpow_add (hpos t ht), hexp]
      _ = (c * p)⁻¹ * t ^ (α - p + 1) * (cos (c * t ^ p + φ) * (c * (p * t ^ (p - 1)))) := by
          ring
  have huv : (fun t ↦ u' t * v t) = fun t ↦ ((α - p + 1) / (c * p)) *
      (t ^ (α - p) * cos (c * t ^ p + (φ - π / 2))) := by
    ext t; dsimp [u', v]; rw [← add_sub_assoc, cos_sub_pi_div_two]; ring
  rw [hcongr, intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    hu'_cont.intervalIntegrable hv'_cont.intervalIntegrable, huv,
    intervalIntegral.integral_const_mul]

/-- **`sin²` and `cos²` over a quarter period.** With `k = π / (2 (b - a))`, the squares of
`sin (k (x - a))` and `cos (k (x - a))` both integrate to `(b - a) / 2` over `[a, b]`. -/
theorem integral_sin_sq_and_integral_cos_sq_quarter_period {a b : ℝ} (hab : a < b) :
    ∫ x in a..b, sin (π / (2 * (b - a)) * (x - a)) ^ 2 = (b - a) / 2 ∧
      ∫ x in a..b, cos (π / (2 * (b - a)) * (x - a)) ^ 2 = (b - a) / 2 := by
  set k := π / (2 * (b - a)) with hk
  have hk0 : k ≠ 0 := (div_pos pi_pos (by linarith)).ne'
  have hkb : k * b - k * a = π / 2 := by
    rw [hk]
    field_simp
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_comp_mul_sub (fun y ↦ sin y ^ 2) hk0,
    intervalIntegral.integral_comp_mul_sub (fun y ↦ cos y ^ 2) hk0, sub_self, hkb,
    integral_sin_sq, integral_cos_sq]
  constructor <;>
  · simp only [sin_zero, cos_zero, sin_pi_div_two, cos_pi_div_two, smul_eq_mul]
    field_simp
    linarith

end TauCeti
