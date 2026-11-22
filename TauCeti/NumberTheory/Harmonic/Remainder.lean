/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.Analysis.SpecialFunctions.Log.OneAddInv

/-!
# Explicit bounds for the harmonic remainder

For a real number `X`, the *harmonic remainder* is
`R₁(X) = Σ_{1 ≤ n ≤ X} 1/n - log X - γ`, where `γ` is the Euler–Mascheroni constant. The sum
runs over the natural numbers in `[1, ⌊X⌋]`, so it is empty for `X < 1`. This file proves the
explicit bounds for `R₁` used throughout explicit multiplicative number theory, whenever a
harmonic sum `Σ_{m ≤ t} 1/m` with a real cutoff `t` has to be replaced by `log t + γ` with an
error stated numerically.

At the integers, `R₁(n) = harmonic n - log n - γ` lies between `1 / (2n + 2/5)` and `1 / (2n)`
for every `n ≥ 1`. Both bounds come from telescoping: `R₁(n) - R₁(n + 1) = log (1 + 1/n) - 1/(n+1)`
is compared with the corresponding differences of the two bounds by the series for
`log (1 + 1/n)`, and `R₁(n) → 0`. On each interval `[N, N + 1)`, `R₁(X) = R₁(N) - log (X / N)`
decreases from `R₁(N)` towards `R₁(N + 1) - 1/(N + 1)`, so the bounds at the integers control
`X R₁(X)` for real `X ≥ 1`: it lies in `[-6/11, 1/2]`. The constant `6/11` is
`1 - 2 / (2 · 2 + 2/5)`, the value of the lower integer bound at `N + 1 = 2`. For `0 < X < 1`
the remainder is `-log X - γ` and is bounded by elementary inequalities for the logarithm.

## Main definitions

* `TauCeti.harmonicRemainder X`: the harmonic remainder `R₁(X)`.

## Main results

* `TauCeti.harmonic_sub_log_sub_eulerMascheroniConstant_le`: `R₁(n) ≤ 1 / (2n)`.
* `TauCeti.inv_two_mul_add_le_harmonic_sub_log_sub_eulerMascheroniConstant`:
  `1 / (2n + 2/5) ≤ R₁(n)` for `n ≥ 1`.
* `TauCeti.eulerMascheroniConstant_gt_d5`: `0.57721 < γ`.
* `TauCeti.harmonicRemainder_le`: `R₁(X) ≤ 1 / (2X)` for every real `X > 0`.
* `TauCeti.abs_harmonicRemainder_le`: `|R₁(X)| ≤ 6 / (11 X)` for every real `X ≥ 1`.
* `TauCeti.abs_harmonicRemainder_le_eulerMascheroniConstant_div`: `|R₁(X)| ≤ γ / X` for every
  real `X > 0`.
* `TauCeti.abs_harmonicRemainder_le_rpow`: `|R₁(t)| ≤ 0.9105 t^{-1/3}` for every real `t > 0`.
  The constant cannot be lowered below `3 e^{-1-γ/3} = 0.910471…`, the maximum of
  `(-log t - γ) t^{1/3}` on `(0, 1)`.

## References

* P. Akhilesh, O. Ramaré, *Explicit averages of non-negative multiplicative functions: going
  beyond the main term*, Colloq. Math. 147 (2017), Lemma 2.1 (the bounds `γ / X` and
  `6 / (11 X)`).
* O. Ramaré, *On Šnirel'man's constant*, Ann. Scuola Norm. Sup. Pisa 22 (1995), Lemma 3.3 (the
  bound `0.9105 t^{-1/3}`).
* C.-P. Chen, *Inequalities for the Euler–Mascheroni constant*, Appl. Math. Lett. 23 (2010)
  (the lower bound `1 / (2n + 2/5)`).
-/

public section

open Filter Finset Real
open scoped Topology

namespace TauCeti

/-- The harmonic remainder `R₁(X) = Σ_{1 ≤ n ≤ X} 1/n - log X - γ` at a real number `X`. The
harmonic sum is `harmonic ⌊X⌋₊`, which is empty for `X < 1`. -/
noncomputable def harmonicRemainder (X : ℝ) : ℝ :=
  harmonic ⌊X⌋₊ - log X - eulerMascheroniConstant

/-- Unfolding lemma for `harmonicRemainder`. -/
theorem harmonicRemainder_def (X : ℝ) :
    harmonicRemainder X = harmonic ⌊X⌋₊ - log X - eulerMascheroniConstant := (rfl)

/-- The harmonic remainder written with the sum over `Finset.Icc 1 ⌊X⌋₊`. -/
theorem harmonicRemainder_eq_sum_Icc (X : ℝ) :
    harmonicRemainder X = ∑ n ∈ Icc 1 ⌊X⌋₊, (n : ℝ)⁻¹ - log X - eulerMascheroniConstant := by
  rw [harmonicRemainder_def, harmonic_eq_sum_Icc]
  push_cast
  rfl

@[simp]
theorem harmonicRemainder_natCast (n : ℕ) :
    harmonicRemainder n = harmonic n - log n - eulerMascheroniConstant := by
  rw [harmonicRemainder_def, Nat.floor_natCast]

/-- Below `1` the harmonic sum is empty. -/
theorem harmonicRemainder_of_lt_one {X : ℝ} (hX : X < 1) :
    harmonicRemainder X = -log X - eulerMascheroniConstant := by
  rw [harmonicRemainder_def, Nat.floor_eq_zero.mpr hX, harmonic_zero, Rat.cast_zero, zero_sub]

@[simp]
theorem harmonicRemainder_one : harmonicRemainder 1 = 1 - eulerMascheroniConstant := by
  simpa using harmonicRemainder_natCast 1

/-- On `[N, N + 1)` with `N = ⌊X⌋₊ ≥ 1`, the harmonic remainder is its value at `N` minus
`log (X / N)`. -/
theorem harmonicRemainder_eq_harmonicRemainder_floor_sub_log {X : ℝ} (hX : 1 ≤ X) :
    harmonicRemainder X = harmonicRemainder ⌊X⌋₊ - log (X / ⌊X⌋₊) := by
  have hN : (0 : ℝ) < ⌊X⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hX
  rw [harmonicRemainder_natCast, harmonicRemainder_def, log_div (by positivity) hN.ne']
  ring

/-! ### Bounds at the integers -/

/-- The harmonic remainder at the integers tends to zero. -/
private theorem tendsto_harmonic_sub_log_sub_eulerMascheroniConstant :
    Tendsto (fun n : ℕ ↦ (harmonic n : ℝ) - log n - eulerMascheroniConstant) atTop (𝓝 0) := by
  simpa using tendsto_harmonic_sub_log.sub_const eulerMascheroniConstant

/-- Telescoping comparison: if `f` and `g` tend to zero and every decrement of `f` from `n ≥ m`
is at most the corresponding decrement of `g`, then `f m ≤ g m`. -/
private theorem le_of_sub_succ_le {f g : ℕ → ℝ} {m : ℕ} (hf : Tendsto f atTop (𝓝 0))
    (hg : Tendsto g atTop (𝓝 0)) (h : ∀ n, m ≤ n → f n - f (n + 1) ≤ g n - g (n + 1)) :
    f m ≤ g m := by
  have hanti : Antitone fun k ↦ g (k + m) - f (k + m) := antitone_nat_of_succ_le fun k ↦ by
    have := h (k + m) (Nat.le_add_left m k)
    rw [Nat.add_right_comm]
    linarith
  have hlim : Tendsto (fun k ↦ g (k + m) - f (k + m)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (hg.sub hf).comp (tendsto_add_atTop_nat m)
  simpa using hanti.le_of_tendsto hlim 0

/-- The decrement of the harmonic remainder between consecutive positive integers. -/
private theorem harmonic_sub_log_sub_succ {n : ℕ} (hn : n ≠ 0) :
    ((harmonic n : ℝ) - log n - eulerMascheroniConstant) -
        ((harmonic (n + 1) : ℝ) - log ↑(n + 1) - eulerMascheroniConstant) =
      log (1 + (n : ℝ)⁻¹) - ((n : ℝ) + 1)⁻¹ := by
  have hn' : (0 : ℝ) < n := by positivity
  have h1 : 1 + (n : ℝ)⁻¹ = (n + 1) / n := by field_simp
  rw [harmonic_succ, h1, log_div (by positivity) hn'.ne']
  push_cast
  ring

/-- Upper bound for the harmonic remainder at the integers:
`harmonic n - log n - γ ≤ 1 / (2n)`. At `n = 0` both sides read `-γ ≤ 0`. -/
theorem harmonic_sub_log_sub_eulerMascheroniConstant_le (n : ℕ) :
    (harmonic n : ℝ) - log n - eulerMascheroniConstant ≤ 1 / (2 * n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using one_half_lt_eulerMascheroniConstant.le.trans' (by norm_num)
  refine le_of_sub_succ_le (g := fun n : ℕ ↦ 1 / (2 * (n : ℝ)))
    tendsto_harmonic_sub_log_sub_eulerMascheroniConstant ?_ fun k hk ↦ ?_
  · simp only [one_div]
    exact (tendsto_natCast_atTop_atTop.const_mul_atTop (two_pos : (0 : ℝ) < 2)).inv_tendsto_atTop
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hn.bot_lt.trans_le hk
    rw [harmonic_sub_log_sub_succ (by omega)]
    have h := log_one_add_inv_le hk'
    have he : 1 / (2 * (k : ℝ)) - 1 / (2 * ↑(k + 1)) =
        (2 * k + 1) / (2 * k * (k + 1)) - ((k : ℝ) + 1)⁻¹ := by
      push_cast
      field_simp
      ring
    rw [he]
    linarith

/-- Lower bound for the harmonic remainder at the positive integers:
`1 / (2n + 2/5) ≤ harmonic n - log n - γ`. -/
theorem inv_two_mul_add_le_harmonic_sub_log_sub_eulerMascheroniConstant {n : ℕ} (hn : n ≠ 0) :
    1 / (2 * n + 2 / 5) ≤ (harmonic n : ℝ) - log n - eulerMascheroniConstant := by
  refine le_of_sub_succ_le (f := fun n : ℕ ↦ 1 / (2 * (n : ℝ) + 2 / 5)) ?_
    tendsto_harmonic_sub_log_sub_eulerMascheroniConstant fun k hk ↦ ?_
  · simp only [one_div]
    exact ((tendsto_natCast_atTop_atTop.const_mul_atTop (two_pos : (0 : ℝ) < 2)).atTop_add
      tendsto_const_nhds).inv_tendsto_atTop
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hn.bot_lt.trans_le hk
    rw [harmonic_sub_log_sub_succ (by omega)]
    have h := two_div_add_two_div_le_log_one_add_inv (zero_lt_one.trans_le hk')
    refine le_trans ?_ (sub_le_sub_right h _)
    -- the difference of the two sides is
    -- `(40k³ + 24k² - 7k - 15) / (6 (5k + 1) (5k + 6) (2k + 1)³ (k + 1))`
    have he : 2 / (2 * (k : ℝ) + 1) + 2 / (3 * (2 * k + 1) ^ 3) - ((k : ℝ) + 1)⁻¹ -
        (1 / (2 * (k : ℝ) + 2 / 5) - 1 / (2 * ↑(k + 1) + 2 / 5)) =
        (40 * k ^ 3 + 24 * k ^ 2 - 7 * k - 15) /
          (6 * (5 * k + 1) * (5 * k + 6) * (2 * k + 1) ^ 3 * (k + 1)) := by
      push_cast
      field_simp
      ring
    have hN : 0 ≤ (40 * (k : ℝ) ^ 3 + 24 * k ^ 2 - 7 * k - 15) := by nlinarith
    have := div_nonneg hN (show (0 : ℝ) ≤ 6 * (5 * k + 1) * (5 * k + 6) * (2 * k + 1) ^ 3 * (k + 1)
      by positivity)
    rw [← he] at this
    linarith

/-- A decimal lower bound for the Euler–Mascheroni constant: `0.57721 < γ`. It follows from
`harmonic 128 - log 128 - γ ≤ 1 / 256`. -/
theorem eulerMascheroniConstant_gt_d5 : 0.57721 < eulerMascheroniConstant := by
  have h := harmonic_sub_log_sub_eulerMascheroniConstant_le 128
  have hlog : log ((128 : ℕ) : ℝ) = 7 * log 2 := by
    rw [show ((128 : ℕ) : ℝ) = 2 ^ 7 by norm_num, log_pow]
    norm_num
  have hH : (((57721 / 100000 + 1 / 256 + 7 * (6931471808 / 10000000000) : ℚ)) : ℝ) <
      harmonic 128 := by
    exact_mod_cast (show (57721 / 100000 + 1 / 256 + 7 * (6931471808 / 10000000000) : ℚ) <
        harmonic 128 by
      rw [harmonic]
      norm_num [Finset.sum_range_succ])
  push_cast at hH
  rw [hlog] at h
  norm_num at h
  linarith [log_two_lt_d9]

/-! ### Bounds at real arguments -/

/-- For `X > 0`, `-log X ≤ 1 / (2X) + log 2 - 1`: the bound `log y ≤ y - 1` at `y = 1 / (2X)`. -/
private theorem neg_log_le {X : ℝ} (hX : 0 < X) : -log X ≤ 1 / (2 * X) + log 2 - 1 := by
  have h := log_le_sub_one_of_pos (show 0 < 1 / (2 * X) by positivity)
  rw [one_div, log_inv, log_mul two_ne_zero hX.ne'] at h
  rw [one_div]
  linarith

/-- For `X ≥ 1` with `N = ⌊X⌋₊`, `X R₁(X) ≤ N R₁(N)`. -/
private theorem mul_harmonicRemainder_le_floor_mul {X : ℝ} (hX : 1 ≤ X) :
    X * harmonicRemainder X ≤ ⌊X⌋₊ * harmonicRemainder ⌊X⌋₊ := by
  set N := ⌊X⌋₊
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.floor_pos.mpr hX
  have hNX : (N : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hr : harmonicRemainder N ≤ 1 := by
    rw [harmonicRemainder_natCast]
    refine (harmonic_sub_log_sub_eulerMascheroniConstant_le N).trans ?_
    rw [div_le_one (by positivity)]
    linarith [show (1 : ℝ) ≤ N by exact_mod_cast Nat.floor_pos.mpr hX]
  -- `log (X / N) ≥ 1 - N / X`
  have hlog : 1 - N / X ≤ log (X / N) := by
    have := one_sub_inv_le_log_of_pos (show 0 < X / N by positivity)
    rwa [inv_div] at this
  rw [harmonicRemainder_eq_harmonicRemainder_floor_sub_log hX]
  have hX0 : 0 < X := by linarith
  have h1 : X * log (X / N) ≥ X - N := by
    have := mul_le_mul_of_nonneg_left hlog hX0.le
    rwa [mul_sub, mul_one, mul_div_cancel₀ _ hX0.ne'] at this
  nlinarith

/-- For `X ≥ 1` with `N = ⌊X⌋₊`, `-X R₁(X) ≤ 1 - (N + 1) R₁(N + 1)`: the infimum of `R₁` on
`[N, N + 1)` is its left limit at `N + 1`. -/
private theorem neg_mul_harmonicRemainder_le {X : ℝ} (hX : 1 ≤ X) :
    -(X * harmonicRemainder X) ≤ 1 - (⌊X⌋₊ + 1) * harmonicRemainder (⌊X⌋₊ + 1 : ℕ) := by
  rw [harmonicRemainder_eq_harmonicRemainder_floor_sub_log hX]
  set N := ⌊X⌋₊
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.floor_pos.mpr hX
  have hXN : X < N + 1 := Nat.lt_floor_add_one X
  -- At the right end, `(N + 1) (log ((N + 1) / N) - R₁(N)) = 1 - (N + 1) R₁(N + 1)`.
  have hend : ((N : ℝ) + 1) * (log ((N + 1) / N) - harmonicRemainder N) =
      1 - (N + 1) * harmonicRemainder (N + 1 : ℕ) := by
    rw [harmonicRemainder_natCast, harmonicRemainder_natCast, harmonic_succ,
      log_div (by positivity) hN.ne']
    push_cast
    field_simp
    ring
  rw [← hend, neg_mul_eq_mul_neg, neg_sub]
  rcases le_or_gt (log (X / N) - harmonicRemainder N) 0 with h | h
  · -- the right-hand side is `1 - (N + 1) R₁(N + 1) ≥ 1 / 2`
    have hr := harmonic_sub_log_sub_eulerMascheroniConstant_le (N + 1)
    rw [← harmonicRemainder_natCast, le_div_iff₀ (by positivity)] at hr
    have hr' : ((N : ℝ) + 1) * harmonicRemainder (N + 1 : ℕ) ≤ 1 / 2 := by
      push_cast at hr ⊢
      linarith
    nlinarith [zero_lt_one.trans_le hX]
  · have hlog : log (X / N) ≤ log ((N + 1) / N) :=
      log_le_log (by positivity) (div_le_div_of_nonneg_right hXN.le hN.le)
    exact mul_le_mul hXN.le (by linarith) h.le (by positivity)

/-- The one-sided bound `R₁(X) ≤ 1 / (2X)` for every real `X > 0`. At `X = 0` both sides read
`-γ ≤ 0`. -/
theorem harmonicRemainder_le {X : ℝ} (hX : 0 ≤ X) : harmonicRemainder X ≤ 1 / (2 * X) := by
  rcases hX.eq_or_lt with rfl | hX
  · simpa [harmonicRemainder_def] using one_half_lt_eulerMascheroniConstant.le.trans' (by norm_num)
  rcases lt_or_ge X 1 with hX1 | hX1
  · rw [harmonicRemainder_of_lt_one hX1]
    linarith [neg_log_le hX, log_two_lt_d9, eulerMascheroniConstant_gt_d5]
  · have h := mul_harmonicRemainder_le_floor_mul hX1
    have hN : (⌊X⌋₊ : ℝ) * harmonicRemainder ⌊X⌋₊ ≤ 1 / 2 := by
      have hN0 : (0 : ℝ) < ⌊X⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hX1
      have := harmonic_sub_log_sub_eulerMascheroniConstant_le ⌊X⌋₊
      rw [harmonicRemainder_natCast]
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    rw [le_div_iff₀ (by positivity)]
    linarith

/-- The one-sided bound `-6 / (11 X) ≤ R₁(X)` for every real `X ≥ 1`. -/
theorem neg_six_div_le_harmonicRemainder {X : ℝ} (hX : 1 ≤ X) :
    -(6 / (11 * X)) ≤ harmonicRemainder X := by
  have h := neg_mul_harmonicRemainder_le hX
  have hM : 5 / 11 ≤ ((⌊X⌋₊ : ℝ) + 1) * harmonicRemainder (⌊X⌋₊ + 1 : ℕ) := by
    have h1 : (1 : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hX
    have := inv_two_mul_add_le_harmonic_sub_log_sub_eulerMascheroniConstant
      (Nat.succ_ne_zero ⌊X⌋₊)
    rw [harmonicRemainder_natCast]
    push_cast at this ⊢
    rw [div_le_iff₀ (by positivity)] at this
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  rw [neg_le, le_div_iff₀ (by positivity)]
  linarith

/-- Akhilesh–Ramaré: `|R₁(X)| ≤ 6 / (11 X)` for every real `X ≥ 1`. -/
theorem abs_harmonicRemainder_le {X : ℝ} (hX : 1 ≤ X) :
    |harmonicRemainder X| ≤ 6 / (11 * X) := by
  have hX0 : 0 < X := by linarith
  refine abs_le.mpr ⟨neg_six_div_le_harmonicRemainder hX, (harmonicRemainder_le hX0.le).trans ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- Akhilesh–Ramaré: `|R₁(X)| ≤ γ / X` for every real `X > 0`. -/
theorem abs_harmonicRemainder_le_eulerMascheroniConstant_div {X : ℝ} (hX : 0 < X) :
    |harmonicRemainder X| ≤ eulerMascheroniConstant / X := by
  have hγ := eulerMascheroniConstant_gt_d5
  rcases lt_or_ge X 1 with hX1 | hX1
  · rw [harmonicRemainder_of_lt_one hX1, abs_le]
    have hlog : log X < 0 := log_neg hX hX1
    have hγX : eulerMascheroniConstant ≤ eulerMascheroniConstant / X := by
      rw [le_div_iff₀ hX]
      nlinarith
    refine ⟨by linarith, ?_⟩
    have h := neg_log_le hX
    have h2 : 1 / (2 * X) ≤ eulerMascheroniConstant / X := by
      rw [div_le_div_iff₀ (by positivity) hX]
      nlinarith
    linarith [log_two_lt_d9]
  · refine (abs_harmonicRemainder_le hX1).trans ?_
    rw [div_le_div_iff₀ (by positivity) hX]
    nlinarith

/-- `3 / 0.9105 ≤ exp (1 + γ / 3)`, the numerical inequality behind the constant `0.9105`. -/
private theorem three_div_le_exp : 3 / 0.9105 ≤ exp (1 + eulerMascheroniConstant / 3) := by
  have hγ := eulerMascheroniConstant_gt_d5
  set x := eulerMascheroniConstant / 3
  have hx : 0.57721 / 3 ≤ x := by simp only [x]; linarith
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hexp := sum_le_exp_of_nonneg hx0 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hexp
  rw [exp_add]
  have hp : (1 : ℝ) + 0.57721 / 3 + (0.57721 / 3) ^ 2 / 2 + (0.57721 / 3) ^ 3 / 6 +
      (0.57721 / 3) ^ 4 / 24 ≤ exp x := by
    have hc : (0 : ℝ) ≤ 0.57721 / 3 := by norm_num
    have h2 := pow_le_pow_left₀ hc hx 2
    have h3 := pow_le_pow_left₀ hc hx 3
    have h4 := pow_le_pow_left₀ hc hx 4
    linarith
  have he := exp_one_gt_d9
  calc (3 : ℝ) / 0.9105
      ≤ 2.7182818283 * (1 + 0.57721 / 3 + (0.57721 / 3) ^ 2 / 2 + (0.57721 / 3) ^ 3 / 6 +
          (0.57721 / 3) ^ 4 / 24) := by norm_num
    _ ≤ exp 1 * exp x := mul_le_mul he.le hp (by norm_num) (exp_pos 1).le

/-- Ramaré's cube-root form: `|R₁(t)| ≤ 0.9105 t^{-1/3}` for every real `t > 0`, that is,
`Σ_{n ≤ t} 1/n = log t + γ + O*(0.9105 t^{-1/3})`. -/
theorem abs_harmonicRemainder_le_rpow {t : ℝ} (ht : 0 < t) :
    |harmonicRemainder t| ≤ 0.9105 * t ^ (-(1 / 3 : ℝ)) := by
  rcases lt_or_ge t 1 with ht1 | ht1
  · set u := t ^ (-(1 / 3 : ℝ))
    have hu0 : 0 < u := rpow_pos_of_pos ht _
    have hu1 : 1 ≤ u := one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1.le (by norm_num)
    have hlogu : log u = -(1 / 3) * log t := log_rpow ht _
    -- `log u ≤ u / c - 1 + log c` at `c = 3 / 0.9105`
    have hc : (0 : ℝ) < 3 / 0.9105 := by norm_num
    have hlog := log_le_sub_one_of_pos (div_pos hu0 hc)
    rw [log_div hu0.ne' hc.ne'] at hlog
    have hlc : log (3 / 0.9105) ≤ 1 + eulerMascheroniConstant / 3 := by
      rw [← log_exp (1 + eulerMascheroniConstant / 3)]
      exact log_le_log hc three_div_le_exp
    have hdiv : u / (3 / 0.9105) = 0.9105 * u / 3 := by field_simp
    rw [hdiv] at hlog
    rw [harmonicRemainder_of_lt_one ht1, abs_le]
    have hγ := eulerMascheroniConstant_lt_two_thirds
    have hlt : log t < 0 := log_neg ht ht1
    constructor <;> nlinarith
  · refine (abs_harmonicRemainder_le ht1).trans ?_
    have hle : t ^ (-1 : ℝ) ≤ t ^ (-(1 / 3 : ℝ)) :=
      rpow_le_rpow_of_exponent_le ht1 (by norm_num)
    rw [rpow_neg_one] at hle
    calc 6 / (11 * t) = 6 / 11 * t⁻¹ := by field_simp
      _ ≤ 0.9105 * t ^ (-(1 / 3 : ℝ)) := by
        gcongr
        norm_num

end TauCeti
