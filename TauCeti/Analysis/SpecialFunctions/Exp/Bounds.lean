/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Elementary bounds for the real exponential

Every affine function `A x + B` is eventually smaller than `exp (a x)` when `0 < a`. For `0 < x`
the function `x / (exp x - 1)`, the generating function of the Bernoulli numbers, lies between
`exp (-x)` and `1`. With `q = exp (-x)` it is `x q / (1 - q)`, the rescaled mean of the geometric
weights `(1 - q) q ^ k`, so these bounds control geometric averages as `q ↑ 1`.

Comparing a real power `y ^ ε` with an exponential level `exp (-t)` amounts to comparing `y`
with the rescaled level `exp (-(t / ε))`. For `σ ≥ 0` and `c > 0` the function `x ^ σ exp (-c x)`
is bounded on `x ≥ 0`.

## Main results

* `TauCeti.eventually_mul_add_lt_exp_mul`: `A x + B < exp (a x)` eventually, for `0 < a`.
* `TauCeti.exists_pos_eventually_forall_le_mul_exp`: finitely many eventual exponential bounds
  `f i s t ≤ A_i exp (-κ_i s)` combine into one, with the slowest rate and the largest constant.
* `TauCeti.exp_neg_le_div_exp_sub_one`: `exp (-x) ≤ x / (exp x - 1)` for `0 < x`.
* `TauCeti.div_exp_sub_one_le_one`: `x / (exp x - 1) ≤ 1` for `0 ≤ x`.
* `TauCeti.exp_neg_le_rpow_iff`: `exp (-t) ≤ y ^ ε ↔ exp (-(t / ε)) ≤ y` for `0 ≤ y`, `0 < ε`.
* `TauCeti.exists_rpow_mul_exp_neg_mul_le`: `x ^ σ exp (-c x)` is bounded on `x ≥ 0`, for `0 ≤ σ`,
  `0 < c`.
* `TauCeti.abs_exp_sub_one_le_mul_exp_abs`: `|exp t - 1| ≤ |t| exp |t|` for every real `t`.
* `TauCeti.exp_sub_one_sq_le_two_mul_sq_mul_cosh`: `(exp t - 1)² ≤ 2 t² cosh (2t)` for every real
  `t`.
* `TauCeti.pow_mul_exp_neg_mul_le`: `t ^ m exp (-a t) ≤ m! / a ^ m` for `0 < a`, `0 ≤ t`.
* `TauCeti.one_add_pow_mul_exp_neg_mul_le`, `TauCeti.one_add_pow_mul_exp_neg_add_mul_le`:
  `(1 + t) ^ n exp (-a t) ≤ n! exp a / a ^ n` and
  `(1 + t) ^ n exp (-(a + b) t) ≤ (n! exp a / a ^ n) exp (-b t)` for `0 < a`, `-1 ≤ t`.
* `TauCeti.inv_pow_add_pow_mul_exp_neg_mul_sub_one_sq_div_le`:
  `((y ^ m)⁻¹ + y ^ m) exp (-a ((y - 1)² / y)) ≤ 2 max (m! / (a / 4) ^ m) (2 ^ m)` for `0 < a`,
  `0 < y`.
-/

public section

open Filter Real
open scoped Nat

namespace TauCeti

/-- An affine function of `x` is eventually smaller than `exp (a x)` when `0 < a`. -/
theorem eventually_mul_add_lt_exp_mul {a : ℝ} (ha : 0 < a) (A B : ℝ) :
    ∀ᶠ x in atTop, A * x + B < exp (a * x) := by
  filter_upwards [(tendsto_exp_mul_div_rpow_atTop 1 a ha).eventually_gt_atTop (|A| + |B|),
    eventually_ge_atTop 1] with x hx hx1
  rw [rpow_one, lt_div_iff₀ (by linarith)] at hx
  nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self A)) (by linarith : (0 : ℝ) ≤ x),
    mul_nonneg (abs_nonneg B) (by linarith : (0 : ℝ) ≤ x - 1), le_abs_self B]

/-- Eventual exponential bounds `f i s t ≤ A_i exp (-κ_i s)` with rates `κ_i > 0`, for finitely
many indices `i`, combine into one bound `f i s t ≤ A exp (-κ s)` for all `i`, with the slowest
rate `κ = min_i κ_i` and the largest constant `A = max_i max A_i 0`. -/
theorem exists_pos_eventually_forall_le_mul_exp {ι α : Type*} [Finite ι] {f : ι → ℝ → α → ℝ}
    (h : ∀ i, ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ t, f i s t ≤ A * exp (-(κ * s))) :
    ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ i t, f i s t ≤ A * exp (-(κ * s)) := by
  cases isEmpty_or_nonempty ι
  · exact ⟨1, one_pos, 0, Eventually.of_forall fun _ i ↦ isEmptyElim i⟩
  cases nonempty_fintype ι
  choose κ hκ A hA using h
  set κ₀ := Finset.univ.inf' Finset.univ_nonempty κ
  set A₀ := Finset.univ.sup' Finset.univ_nonempty fun i ↦ max (A i) 0
  refine ⟨κ₀, (Finset.lt_inf'_iff _).2 fun i _ ↦ hκ i, A₀, ?_⟩
  filter_upwards [eventually_all.2 hA, eventually_ge_atTop 0] with s hs hs₀ i t
  have hκi : κ₀ ≤ κ i := Finset.inf'_le _ (Finset.mem_univ i)
  have hAi : max (A i) 0 ≤ A₀ := Finset.le_sup' (fun i ↦ max (A i) 0) (Finset.mem_univ i)
  calc f i s t ≤ A i * exp (-(κ i * s)) := hs i t
    _ ≤ A₀ * exp (-(κ₀ * s)) :=
      mul_le_mul ((le_max_left _ _).trans hAi)
        (exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hκi hs₀)))
        (exp_pos _).le ((le_max_right _ _).trans hAi)

/-- For `0 < x`, `exp (-x) ≤ x / (exp x - 1)`. -/
theorem exp_neg_le_div_exp_sub_one {x : ℝ} (hx : 0 < x) : exp (-x) ≤ x / (exp x - 1) := by
  rw [le_div_iff₀ (sub_pos.2 (one_lt_exp_iff.2 hx)), mul_sub, ← exp_add, neg_add_cancel,
    exp_zero, mul_one]
  linarith [add_one_le_exp (-x)]

/-- For `0 ≤ x`, `x / (exp x - 1) ≤ 1`. -/
theorem div_exp_sub_one_le_one {x : ℝ} (hx : 0 ≤ x) : x / (exp x - 1) ≤ 1 := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rw [div_le_one (sub_pos.2 (one_lt_exp_iff.2 hx))]
  linarith [add_one_le_exp x]

/-- For `0 ≤ y` and `0 < ε`, the power `y ^ ε` reaches the level `exp (-t)` exactly when `y`
reaches the level `exp (-(t / ε))`. -/
theorem exp_neg_le_rpow_iff {y ε t : ℝ} (hy : 0 ≤ y) (hε : 0 < ε) :
    exp (-t) ≤ y ^ ε ↔ exp (-(t / ε)) ≤ y := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [zero_rpow hε.ne', (exp_pos _).not_ge]
  rw [← le_log_iff_exp_le hy, ← le_log_iff_exp_le (rpow_pos_of_pos hy ε), log_rpow hy,
    ← neg_div, div_le_iff₀ hε, mul_comm]

/-- For `0 ≤ σ` and `0 < c`, the function `x ↦ x ^ σ exp (-c x)` is bounded on `x ≥ 0`: it tends
to `0` at infinity, and on a bounded interval `x ^ σ` is bounded. -/
theorem exists_rpow_mul_exp_neg_mul_le {σ c : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c) :
    ∃ M, 0 ≤ M ∧ ∀ x, 0 ≤ x → x ^ σ * exp (-(c * x)) ≤ M := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero σ c
    hc).eventually (ge_mem_nhds zero_lt_one))
  refine ⟨max 1 (max X 0 ^ σ), zero_le_one.trans (le_max_left _ _), fun x hx ↦ ?_⟩
  rcases le_total X x with h | h
  · exact (neg_mul c x ▸ hX x h).trans (le_max_left _ _)
  · exact (mul_le_of_le_one_right (by positivity) (exp_le_one_iff.2 (by nlinarith))).trans
      ((rpow_le_rpow hx (h.trans (le_max_left _ _)) hσ).trans (le_max_right _ _))

/-- `|exp t - 1| ≤ |t| exp |t|` for every real `t`, a global form of the mean value inequality for
the exponential. -/
theorem abs_exp_sub_one_le_mul_exp_abs (t : ℝ) : |exp t - 1| ≤ |t| * exp |t| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (t : ℂ) 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one] at h
  rwa [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at h

/-- `(exp t - 1)² ≤ 2 t² cosh (2t)` for every real `t`. The right-hand side is the power series
`∑ 2 · 4ⁿ t ^ (2n + 2) / (2n)!`, so this bounds `(exp t - 1)²` by a series of even powers. -/
theorem exp_sub_one_sq_le_two_mul_sq_mul_cosh (t : ℝ) :
    (exp t - 1) ^ 2 ≤ 2 * t ^ 2 * cosh (2 * t) := by
  have h1 := abs_exp_sub_one_le_mul_exp_abs t
  have h2 : exp (2 * |t|) ≤ 2 * cosh (2 * t) := by
    have h := exp_abs_le (2 * t)
    rw [abs_mul, abs_two] at h
    rw [cosh_eq]
    linarith
  calc (exp t - 1) ^ 2 = |exp t - 1| ^ 2 := (sq_abs _).symm
    _ ≤ (|t| * exp |t|) ^ 2 := by gcongr
    _ = t ^ 2 * exp (2 * |t|) := by
        rw [mul_pow, sq_abs, ← exp_nat_mul]; push_cast; ring_nf
    _ ≤ t ^ 2 * (2 * cosh (2 * t)) := by gcongr
    _ = 2 * t ^ 2 * cosh (2 * t) := by ring

/-- For `0 < a` and `0 ≤ t`, `t ^ m * exp (-a * t) ≤ m! / a ^ m`. -/
theorem pow_mul_exp_neg_mul_le {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (m : ℕ) :
    t ^ m * exp (-a * t) ≤ (m ! : ℝ) / a ^ m := by
  have h := pow_div_factorial_le_exp (a * t) (mul_nonneg ha.le ht) m
  rw [mul_pow, div_le_iff₀ (Nat.cast_pos.2 m.factorial_pos)] at h
  rw [neg_mul, exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _), div_mul_eq_mul_div,
    le_div_iff₀ (pow_pos ha m)]
  linarith

/-- For `0 < a` and `-1 ≤ t`, `(1 + t) ^ n * exp (-a * t) ≤ n! * exp a / a ^ n`. -/
theorem one_add_pow_mul_exp_neg_mul_le {a t : ℝ} (ha : 0 < a) (ht : -1 ≤ t) (n : ℕ) :
    (1 + t) ^ n * exp (-a * t) ≤ (n ! : ℝ) * exp a / a ^ n := by
  have h := mul_le_mul_of_nonneg_right
    (pow_mul_exp_neg_mul_le ha (t := 1 + t) (by linarith) n) (exp_pos a).le
  rwa [mul_add, mul_one, add_comm (-a), exp_add, mul_assoc, mul_assoc, ← exp_add,
    neg_add_cancel, exp_zero, mul_one, div_mul_eq_mul_div] at h

/-- For `0 < a`, any `b : ℝ`, and `-1 ≤ t`, `(1 + t) ^ n * exp (-(a + b) * t)` is bounded by
`((n ! * exp a) / a ^ n) * exp (-b * t)`. -/
theorem one_add_pow_mul_exp_neg_add_mul_le {a b t : ℝ} (ha : 0 < a) (ht : -1 ≤ t) (n : ℕ) :
    (1 + t) ^ n * exp (-(a + b) * t) ≤ ((n ! : ℝ) * exp a / a ^ n) * exp (-b * t) := by
  rw [neg_add, add_mul, exp_add, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (one_add_pow_mul_exp_neg_mul_le ha ht n) (exp_pos _).le

/-- For `0 < a`, `0 < y`, and `m : ℕ`, the symmetric Laurent weight `(y ^ m)⁻¹ + y ^ m` against
the exponential barrier `exp (-a * ((y - 1) ^ 2 / y))` is uniformly bounded by
`2 * max (m! / (a / 4) ^ m) (2 ^ m)`. -/
theorem inv_pow_add_pow_mul_exp_neg_mul_sub_one_sq_div_le {a y : ℝ} (ha : 0 < a) (hy : 0 < y)
    (m : ℕ) :
    ((y ^ m)⁻¹ + y ^ m) * exp (-a * ((y - 1) ^ 2 / y)) ≤
      2 * max ((m ! : ℝ) / (a / 4) ^ m) (2 ^ m) := by
  have hge2 : ∀ {t : ℝ}, 2 ≤ t →
      ((t ^ m)⁻¹ + t ^ m) * exp (-a * ((t - 1) ^ 2 / t)) ≤
        2 * max ((m ! : ℝ) / (a / 4) ^ m) (2 ^ m) := fun {t} ht => by
    have ht0 : 0 < t := by linarith
    have htm : (t ^ m)⁻¹ + t ^ m ≤ 2 * t ^ m := by
      have h1 : 1 ≤ t ^ m := one_le_pow₀ (by linarith)
      linarith [inv_le_one_of_one_le₀ h1]
    have hquad : t / 4 ≤ (t - 1) ^ 2 / t := by
      rw [div_le_div_iff₀ (by positivity) ht0]
      nlinarith [mul_nonneg (a := 3 * t - 2) (b := t - 2) (by linarith) (by linarith)]
    have hexp : exp (-a * ((t - 1) ^ 2 / t)) ≤ exp (-(a / 4) * t) :=
      exp_le_exp.mpr (by nlinarith)
    calc ((t ^ m)⁻¹ + t ^ m) * exp (-a * ((t - 1) ^ 2 / t))
        ≤ (2 * t ^ m) * exp (-(a / 4) * t) := mul_le_mul htm hexp (by positivity) (by positivity)
      _ = 2 * (t ^ m * exp (-(a / 4) * t)) := by ring
      _ ≤ 2 * ((m ! : ℝ) / (a / 4) ^ m) :=
          mul_le_mul_of_nonneg_left (pow_mul_exp_neg_mul_le (by positivity) ht0.le m) two_pos.le
      _ ≤ 2 * max ((m ! : ℝ) / (a / 4) ^ m) (2 ^ m) := by gcongr; exact le_max_left _ _
  rcases le_or_gt 2 y with hy2 | hy2
  · exact hge2 hy2
  · rcases le_or_gt y (1 / 2) with hy_half | hy_half
    · have hsymm_pow : ((y⁻¹) ^ m)⁻¹ + (y⁻¹) ^ m = (y ^ m)⁻¹ + y ^ m := by
        rw [inv_pow, inv_inv, add_comm]
      have hsymm_quad : (y⁻¹ - 1) ^ 2 / y⁻¹ = (y - 1) ^ 2 / y := by field_simp [hy.ne']; ring
      rw [← hsymm_pow, ← hsymm_quad]
      exact hge2 ((le_inv_comm₀ two_pos hy).mpr (by linarith))
    · have hym : (y ^ m)⁻¹ + y ^ m ≤ 2 * 2 ^ m := by
        have h1 : (y ^ m)⁻¹ ≤ 2 ^ m := by
          rw [← inv_pow]
          exact pow_le_pow_left₀ (by positivity) ((inv_le_comm₀ hy two_pos).mpr (by linarith)) m
        linarith [pow_le_pow_left₀ hy.le hy2.le m]
      have hexp1 : exp (-a * ((y - 1) ^ 2 / y)) ≤ 1 := exp_le_one_iff.mpr <| by
        rw [neg_mul]
        exact neg_nonpos.mpr (mul_nonneg ha.le (div_nonneg (sq_nonneg _) hy.le))
      calc ((y ^ m)⁻¹ + y ^ m) * exp (-a * ((y - 1) ^ 2 / y))
          ≤ (2 * 2 ^ m) * 1 := mul_le_mul hym hexp1 (by positivity) (by positivity)
        _ ≤ 2 * max ((m ! : ℝ) / (a / 4) ^ m) (2 ^ m) := by
            rw [mul_one]; gcongr; exact le_max_right _ _

end TauCeti
