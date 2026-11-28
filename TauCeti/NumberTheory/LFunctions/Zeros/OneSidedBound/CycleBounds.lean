/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Numerical bounds for Frobenius cycles in a theta-lift chain

A cycle with `n` letters and step exponent `e` at `p` has step size `P = p^e` and
residue size `q = P^n`. The elementary-divisor estimates for the corresponding
Hecke operator need a lower bound for `q` and an upper bound for a product of a
logarithmic factor and `P^(3 * Nat.clog p m)`. Separating the two factors at `√b`
allows the bounds to use only numerical scale inequalities, without assumptions
about the realization of the cycle by field embeddings.

The estimates follow the statements `New.Data.x₁_pow_le_sqrt_b` and
`New.Data.isLargeDegree_of_le_card` in the `grh` folder of
<https://github.com/lsernau/grh-lean> at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Real

namespace TauCeti.OneSidedBound

/-- A cutoff power with a block length at most `81 log x₁` fits in the square root
of the larger cutoff if its logarithm dominates the sixth power of `log x₁`. -/
theorem cutoff_pow_le_sqrt_of_le_log {x₁ b : ℝ} {r : ℕ} (hx₁ : 0 < x₁)
    (hlog : 35 ≤ log x₁) (hr : (r : ℝ) ≤ 81 * log x₁) (hb₀ : 0 < b)
    (hb : log x₁ ^ 6 ≤ log b) :
    x₁ ^ (3 * r ^ 2) ≤ √b := by
  have hlog3 : 39366 ≤ log x₁ ^ 3 := by
    calc
      39366 ≤ (35 : ℝ) ^ 3 := by norm_num
      _ ≤ log x₁ ^ 3 := by gcongr
  have he : (3 * r ^ 2 * 2 : ℕ) * log x₁ ≤ log b := by
    push_cast
    calc
      3 * (r : ℝ) ^ 2 * 2 * log x₁ ≤ 3 * (81 * log x₁) ^ 2 * 2 * log x₁ := by gcongr
      _ = 39366 * log x₁ ^ 3 := by ring
      _ ≤ log x₁ ^ 3 * log x₁ ^ 3 := by gcongr
      _ = log x₁ ^ 6 := (pow_add _ 3 3).symm
      _ ≤ log b := hb
  rw [le_sqrt (by positivity) hb₀.le, ← pow_mul]
  exact (log_le_log_iff (pow_pos hx₁ _) hb₀).mp (by rwa [log_pow])

/-- The power of the smaller cutoff indexed by the cyclotomic tower is at most
the square root of the larger cutoff. -/
theorem cutoff_pow_l₀_le_sqrt {x₁ b : ℝ} {s : ℕ} (hx₁ : 0 < x₁)
    (hlog : 35 ≤ log x₁) (hs : (s : ℝ) ≤ log x₁) (hb₀ : 0 < b)
    (hb : log x₁ ^ 6 ≤ log b) :
    x₁ ^ (3 * l₀ s ^ 2) ≤ √b := by
  refine cutoff_pow_le_sqrt_of_le_log hx₁ hlog ?_ hb₀ hb
  by_cases h : s = 0
  · subst s
    have hl : (l₀ 0 : ℝ) = 81 := by norm_num [l₀_def]
    linarith
  · exact (by exact_mod_cast l₀_le h : (l₀ s : ℝ) ≤ 81 * s).trans (by gcongr)

/-- The orbit length forces the residue size to dominate the fourth power of the
jet order `x * b`. Only `p ≥ 3`, rather than primality, is needed. -/
theorem jet_order_pow_four_le_residue_size {x b : ℝ} {m p j : ℕ}
    (hB : 2 ≤ log b) (hscale : log b ^ 8 ≤ x) (hxb : x ≤ b)
    (hm : x ≤ (m : ℝ) ^ 2) (hp : 3 ≤ p) (hj : m ≤ j) :
    (x * b) ^ 4 ≤ (p : ℝ) ^ j := by
  have hlog : 0 < log b := by linarith
  have hx : 0 < x := (pow_pos hlog _).trans_le hscale
  have hb : 0 < b := hx.trans_le hxb
  have hB4 : log b ^ 4 ≤ m := by
    apply le_of_pow_le_pow_left₀ two_ne_zero (Nat.cast_nonneg m)
    simpa only [← pow_mul, Nat.reduceMul] using hscale.trans hm
  have hm' : 8 * log b ≤ m := by
    calc
      8 * log b ≤ log b ^ 3 * log b := by
        gcongr
        calc
          8 = (2 : ℝ) ^ 3 := by norm_num
          _ ≤ log b ^ 3 := by gcongr
      _ = log b ^ 4 := (pow_succ _ _).symm
      _ ≤ m := hB4
  calc
    (x * b) ^ 4 ≤ (b * b) ^ 4 := by gcongr
    _ = exp (8 * log b) := by
      rw [← Nat.cast_ofNat (R := ℝ) (n := 8), exp_natCast_mul, exp_log hb]
      ring
    _ ≤ (p : ℝ) ^ j := exp_le_pow_of_exp_one_le
      (exp_one_lt_three.le.trans (by exact_mod_cast hp)) (hm'.trans (by exact_mod_cast hj))

/-- The logarithmic factor of the cycle degree condition fits inside `√b`.
Here `e` is the step exponent and `n` is the number of letters. -/
private theorem cycle_log_factor_le_sqrt {x x₁ b : ℝ} {m k f e n p : ℕ}
    (hx : 4 ≤ x) (hcut : x ^ 235 ≤ x₁) (hb : x₁ ^ 2 ≤ b)
    (hlog : log x₁ ≤ x) (hp : (p : ℝ) ≤ x₁) (hp₀ : 0 < p)
    (hm : (m : ℝ) ^ 2 ≤ 4 * x) (hk : (k : ℝ) ≤ x ^ 6) (hf : (f : ℝ) ≤ x ^ 12)
    (hn : n ≤ f) (he : (e : ℝ) ≤ x ^ 2) :
    ((n : ℝ) * k * log ((p : ℝ) ^ (e * n)) * ((m : ℝ) ^ 2 * f)) ^ 5 ≤ √b := by
  have hx₁ : 0 < x₁ := (pow_pos (by linarith) _).trans_le hcut
  have hn' : (n : ℝ) ≤ x ^ 12 := (by exact_mod_cast hn : (n : ℝ) ≤ f).trans hf
  have hlogp : log (p : ℝ) ≤ x := (log_le_log (by exact_mod_cast hp₀) hp).trans hlog
  have hm' : (m : ℝ) ^ 2 ≤ x ^ 2 := hm.trans (by nlinarith)
  rw [log_pow, Nat.cast_mul]
  calc
    ((n : ℝ) * k * ((e : ℝ) * n * log p) * ((m : ℝ) ^ 2 * f)) ^ 5 ≤
        (x ^ 12 * x ^ 6 * (x ^ 2 * x ^ 12 * x) * (x ^ 2 * x ^ 12)) ^ 5 := by
      have : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp₀)
      gcongr
    _ = x ^ 235 := by ring
    _ ≤ x₁ := hcut
    _ ≤ √b := by
      rw [le_sqrt hx₁.le ((sq_nonneg x₁).trans hb)]
      exact hb

/-- The power separation of the cutoffs gives a logarithmic separation, with `log x ≥ 1`. -/
private theorem cycle_cutoff_log_separation {x x₁ : ℝ} (hx : 3 ≤ x) (hcut : x ^ 235 ≤ x₁) :
    1 ≤ log x ∧ 235 * log x ≤ log x₁ := by
  have hx₀ : 0 < x := by linarith
  refine ⟨(le_log_iff_exp_le hx₀).2 (exp_one_lt_three.le.trans hx), ?_⟩
  simpa only [log_pow, Nat.cast_ofNat] using log_le_log (pow_pos hx₀ _) hcut

/-- The block length grows at most logarithmically in the chain length, uniformly in the
base `p ≥ 3`. The larger cutoff scale here lets us avoid an extra additive constant. -/
private theorem clog_le_log_cutoff {x x₁ : ℝ} {p m : ℕ} (hx : 4 ≤ x)
    (hcut : x ^ 235 ≤ x₁) (hm : (m : ℝ) ^ 2 ≤ 4 * x) (hp : 3 ≤ p) :
    (Nat.clog p m : ℝ) ≤ log x₁ := by
  obtain ⟨hlogx, hlogcut⟩ := cycle_cutoff_log_separation (by linarith) hcut
  let r := ⌈log x⌉₊
  have hx' : x ≤ (p : ℝ) ^ r := calc
    x = exp (log x) := (exp_log (by linarith)).symm
    _ ≤ (p : ℝ) ^ r := exp_le_pow_of_exp_one_le
      (exp_one_lt_three.le.trans (by exact_mod_cast hp)) (Nat.le_ceil _)
  have hm' : (m : ℝ) ≤ x := by
    apply le_of_pow_le_pow_left₀ two_ne_zero (by linarith)
    exact hm.trans (by nlinarith)
  have hr : Nat.clog p m ≤ r := Nat.clog_le_of_le_pow (by exact_mod_cast hm'.trans hx')
  have hceil : (r : ℝ) < log x + 1 := Nat.ceil_lt_add_one (by linarith)
  exact (by exact_mod_cast hr : (Nat.clog p m : ℝ) ≤ r).trans (by linarith)

/-- The cutoff separation absorbs the step-size contribution to the degree condition. -/
private theorem step_size_pow_le_sqrt {x₁ b : ℝ} {p e r : ℕ} (hx₁ : 1 ≤ x₁)
    (hlog : 35 ≤ log x₁) (hr : (r : ℝ) ≤ log x₁) (hb₀ : 0 < b)
    (hb : log x₁ ^ 6 ≤ log b) (hp : (p : ℝ) ≤ x₁) (he : e ≤ r) :
    ((p : ℝ) ^ e) ^ (3 * r) ≤ √b := by
  rw [← pow_mul]
  calc
    (p : ℝ) ^ (e * (3 * r)) ≤ x₁ ^ (e * (3 * r)) := by gcongr
    _ ≤ x₁ ^ (3 * r ^ 2) := by
      apply pow_le_pow_right₀ hx₁
      calc
        e * (3 * r) ≤ r * (3 * r) := by gcongr
        _ = 3 * r ^ 2 := by ring
    _ ≤ √b := cutoff_pow_le_sqrt_of_le_log (by linarith) hlog (hr.trans (by linarith)) hb₀ hb

/-- Separation of the cutoffs controls both the smaller logarithm and twice that
logarithm, which is needed to compare `x₁` with `√b`. -/
private theorem cycle_cutoff_log_bounds {x x₁ b : ℝ} (hx : 4 ≤ x)
    (hcut : x ^ 235 ≤ x₁) (hsmall : log x₁ ^ 6 ≤ log b) :
    235 ≤ log x₁ ∧ 2 * log x₁ ≤ log b := by
  obtain ⟨hlogx, hlogcut⟩ := cycle_cutoff_log_separation (by linarith) hcut
  have hlogx₁ : 235 ≤ log x₁ := by linarith
  refine ⟨hlogx₁, ?_⟩
  calc
    2 * log x₁ ≤ log x₁ ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    _ ≤ log x₁ ^ 6 := pow_le_pow_right₀ (by linarith) (by decide)
    _ ≤ log b := hsmall

/-- The size inequalities ensuring large degree for a Frobenius cycle of `n` letters,
step exponent `e`, and base `p`. The cutoff assumptions are weaker than the
separations in a theta-lift chain; `m` is the chain length and `k` the source rank.
The residue size is `p^(e*n)` and the proportion parameter is `1/(m²*f)`. -/
theorem frobenius_cycle_degree_bounds {x x₁ b : ℝ} {m k f n p e : ℕ}
    (hcut : x ^ 235 ≤ x₁) (hb₀ : 0 < b) (hsmall : log x₁ ^ 6 ≤ log b) (hlarge : log b ^ 8 ≤ x)
    (hm : x ≤ (m : ℝ) ^ 2) (hm' : (m : ℝ) ^ 2 ≤ 4 * x)
    (hk : x ^ 3 ≤ (k : ℝ)) (hk' : (k : ℝ) ≤ x ^ 6) (hf : (f : ℝ) ≤ x ^ 12)
    (hn : n ≤ f) (hp : 3 ≤ p) (hp' : (p : ℝ) ≤ x₁)
    (he : e ≤ Nat.clog p m) (hlen : m ≤ e * n) :
    0 < Nat.clog p m ∧ 2 * Nat.clog p m ≤ k ∧ 1 / ((m : ℝ) ^ 2 * f) ∈ Set.Ioc 0 1 ∧
    (x * b) ^ 4 ≤ (p : ℝ) ^ (e * n) ∧
    ((n : ℝ) * k * log ((p : ℝ) ^ (e * n)) / (1 / ((m : ℝ) ^ 2 * f))) ^ 5 *
      ((p : ℝ) ^ e) ^ (3 * Nat.clog p m) ≤ x * b := by
  have hx : 4 ≤ x := by
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
    have hlog := log_le_log (by norm_num) (hpR.trans hp')
    have hlog₁ : (21 / 20 : ℝ) ≤ log x₁ := by linarith [log_three_gt_d9]
    have hlogb : (21 / 20 : ℝ) ^ 6 ≤ log b :=
      (pow_le_pow_left₀ (by norm_num) hlog₁ _).trans hsmall
    calc
      4 ≤ ((21 / 20 : ℝ) ^ 6) ^ 8 := by norm_num
      _ ≤ log b ^ 8 := by gcongr
      _ ≤ x := hlarge
  have hx1 : 1 ≤ x := by linarith
  have hxx₁ : x ≤ x₁ := (le_self_pow₀ hx1 (by decide : 235 ≠ 0)).trans hcut
  have hx₁ : 1 ≤ x₁ := hx1.trans hxx₁
  obtain ⟨hlogx₁, hlogs⟩ := cycle_cutoff_log_bounds hx hcut hsmall
  have hb : x₁ ^ 2 ≤ b := (log_le_log_iff (pow_pos (by linarith) _) hb₀).1 (by
    simpa only [log_pow, Nat.cast_ofNat] using hlogs)
  have hxb : x ≤ b := hxx₁.trans ((le_self_pow₀ hx₁ two_ne_zero).trans hb)
  have hB : 2 ≤ log b := by linarith
  have hlog₁ : log x₁ ≤ x :=
    (le_self_pow₀ (by linarith) (by decide : 6 ≠ 0)).trans (hsmall.trans
      ((le_self_pow₀ (by linarith) (by decide : 8 ≠ 0)).trans hlarge))
  have hr := clog_le_log_cutoff hx hcut hm' hp
  have hr' := (hr.trans hlog₁).trans (le_self_pow₀ hx1 two_ne_zero)
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun hm₀ ↦
    (not_le_of_gt (by linarith : 0 < x)) (by
      simpa only [hm₀, Nat.cast_zero, zero_pow two_ne_zero] using hm)
  have hne := mul_ne_zero_iff.mp (Nat.ne_of_gt (hm1.trans hlen))
  have hf1 : 1 ≤ f := (Nat.one_le_iff_ne_zero.mpr hne.2).trans hn
  have he₀ : 0 < e := Nat.pos_of_ne_zero hne.1
  refine ⟨he₀.trans_le he, ?_, ⟨by positivity, ?_⟩,
    jet_order_pow_four_le_residue_size hB hlarge hxb hm hp hlen, ?_⟩
  · have h := calc
      2 * (Nat.clog p m : ℝ) ≤ 2 * x ^ 2 := by gcongr
      _ ≤ x * x ^ 2 := by gcongr; linarith
      _ = x ^ 3 := by ring
      _ ≤ k := hk
    exact_mod_cast h
  · have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf1
    apply (div_le_iff₀ (by positivity)).2
    rw [one_mul]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hmR) hfR
  · rw [div_div_eq_mul_div, div_one]
    have h₁ := cycle_log_factor_le_sqrt hx hcut hb hlog₁ hp' (by omega) hm' hk' hf hn
      ((by exact_mod_cast he : (e : ℝ) ≤ Nat.clog p m).trans hr')
    have h₂ := step_size_pow_le_sqrt hx₁ (by linarith) hr hb₀ hsmall hp' he
    calc
      _ ≤ √b * √b := by gcongr
      _ = b := mul_self_sqrt (by linarith)
      _ ≤ x * b := le_mul_of_one_le_left (by linarith) hx1

end TauCeti.OneSidedBound
