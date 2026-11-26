/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Asymptotics.ExpGrowth

/-!
# Exponential growth: products with an exactly growing factor, and growth along `k * n`

Mathlib's `ExpGrowth.expGrowthSup_mul_le` and `ExpGrowth.le_expGrowthSup_mul'` bound the upper
exponential growth of a product `u * v` above by `expGrowthSup u + expGrowthSup v` and below by
`expGrowthInf u + expGrowthSup v`. When `u` has an exact, finite exponential growth rate `a`, the
two bounds agree, so multiplying by `u` shifts the upper exponential growth by `a`.

Along the times `k * n`, the upper exponential growth is at most `k` times the original one, with
equality when `exp (c * n) * u n` is monotone for some real `c`. This extends Mathlib's
`Monotone.expGrowthSup_comp_mul`, the case `c = 0`.

## Main results

* `ExpGrowth.expGrowthSup_mul_of_expGrowthInf_eq` — if `expGrowthInf u = expGrowthSup u = a` with
  `a` real, then `expGrowthSup (u * v) = a + expGrowthSup v`.
* `ExpGrowth.expGrowthSup_exp_mul` — `expGrowthSup (fun n ↦ exp (a * n) * v n) = a +
  expGrowthSup v` for real `a`.
* `ExpGrowth.expGrowthSup_comp_mul_le` — `expGrowthSup (fun n ↦ u (k * n)) ≤ k * expGrowthSup u`
  for `k ≠ 0`.
* `ExpGrowth.expGrowthSup_comp_mul_of_monotone_exp_mul` — if `exp (c * n) * u n` is monotone
  for some real `c`, then `expGrowthSup (fun n ↦ u (k * n)) = k * expGrowthSup u` for `k ≠ 0`.
* `Monotone.expGrowthSup_comp_add`: a monotone sequence has the same upper exponential growth
  along the shifted times `n + k`.
* `ExpGrowth.expGrowthSup_rpow` — `expGrowthSup (fun n ↦ u n ^ t) = t * expGrowthSup u` for
  real `t ≥ 0`.
-/

public section

namespace ExpGrowth

open ENNReal EReal Filter

variable {u v : ℕ → ℝ≥0∞}

/-- Multiplying by a sequence of exact, finite exponential growth rate `a` adds `a` to the upper
exponential growth. -/
theorem expGrowthSup_mul_of_expGrowthInf_eq {a : ℝ} (hinf : expGrowthInf u = a)
    (hsup : expGrowthSup u = a) :
    expGrowthSup (u * v) = a + expGrowthSup v := by
  refine le_antisymm ?_ ?_
  · rw [← hsup]
    exact expGrowthSup_mul_le (.inl (by simp [hsup])) (.inl (by simp [hsup]))
  · rw [← hinf]
    exact le_expGrowthSup_mul'

/-- Multiplying by `exp (a * n)` with `a` real adds `a` to the upper exponential growth. -/
theorem expGrowthSup_exp_mul (a : ℝ) (v : ℕ → ℝ≥0∞) :
    expGrowthSup (fun n ↦ exp (a * n) * v n) = a + expGrowthSup v :=
  expGrowthSup_mul_of_expGrowthInf_eq (u := fun n ↦ exp (a * n)) expGrowthInf_exp expGrowthSup_exp

/-- The upper exponential growth rate of `u` along the times `k * n` is at most `k` times that of
`u`, for `k ≠ 0`. -/
theorem expGrowthSup_comp_mul_le {k : ℕ} (hk : k ≠ 0) (u : ℕ → ℝ≥0∞) :
    expGrowthSup (fun n ↦ u (k * n)) ≤ k * expGrowthSup u := by
  have hk₀ : (0 : EReal) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  refine expGrowthSup_le_iff.2 fun b hb ↦ ?_
  have hb' : expGrowthSup u < b / k := by
    rwa [EReal.lt_div_iff hk₀ (natCast_ne_top k), mul_comm]
  have hbk (n : ℕ) : b / k * (k * n : ℕ) = b * n := by
    rw [EReal.natCast_mul, ← mul_assoc,
      EReal.div_mul_cancel (natCast_ne_bot k) (natCast_ne_top k) hk₀.ne']
  have hkn : Tendsto (fun n : ℕ ↦ k * n) atTop atTop :=
    tendsto_id.const_mul_atTop' (Nat.pos_of_ne_zero hk)
  filter_upwards [hkn.eventually (eventually_le_exp hb')] with n hn
  rwa [hbk] at hn

/-- If the sequence `exp (c * n) * u n` is monotone, then the upper exponential growth rate of `u`
along the times `k * n` is `k` times that of `u`, for `k ≠ 0`. -/
theorem expGrowthSup_comp_mul_of_monotone_exp_mul {u : ℕ → ℝ≥0∞} {c : ℝ} {k : ℕ} (hk : k ≠ 0)
    (h : Monotone fun n : ℕ ↦ EReal.exp (c * n) * u n) :
    expGrowthSup (fun n ↦ u (k * n)) = k * expGrowthSup u := by
  have hck (n : ℕ) : (c : EReal) * ((k * n : ℕ) : EReal) = ((c * k : ℝ) : EReal) * n := by
    push_cast
    exact (mul_assoc _ _ _).symm
  have h₁ := h.expGrowthSup_comp_mul hk
  simp only [hck, expGrowthSup_exp_mul] at h₁
  refine (EReal.addLECancellable_coe (c * k)).inj_right.1 ?_
  rw [h₁, EReal.left_distrib_of_nonneg_of_ne_top (by positivity) (natCast_ne_top k)]
  push_cast
  rw [mul_comm]

/-- Raising a sequence to a nonnegative real power `t` multiplies its upper exponential growth
by `t`. -/
theorem expGrowthSup_rpow {t : ℝ} (ht : 0 ≤ t) (u : ℕ → ℝ≥0∞) :
    expGrowthSup (fun n ↦ u n ^ t) = t * expGrowthSup u := by
  simp only [expGrowthSup, ENNReal.log_rpow, ← EReal.mul_div]
  exact limsup_const_mul_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr ht) (EReal.coe_ne_top t)

end ExpGrowth

open ENNReal EReal ExpGrowth Filter Topology in
/-- A monotone sequence has the same upper exponential growth along the shifted times `n + k`. -/
theorem Monotone.expGrowthSup_comp_add {u : ℕ → ℝ≥0∞} (h : Monotone u) (k : ℕ) :
    expGrowthSup (fun n ↦ u (n + k)) = expGrowthSup u := by
  have hr : Tendsto (fun n : ℕ ↦ (1 : ℝ) + k * (1 / (n : ℝ))) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := (k : ℝ))).mul tendsto_one_div_atTop_nhds_zero_nat)
    rwa [mul_zero, add_zero] at this
  have hv : Tendsto (fun n : ℕ ↦ ((n + k : ℕ) : EReal) / n) atTop (𝓝 1) := by
    refine (EReal.tendsto_coe.2 hr).congr' ((eventually_gt_atTop 0).mono fun n hn ↦ ?_)
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    dsimp only
    rw [← EReal.coe_natCast, ← EReal.coe_natCast, ← EReal.coe_div, Nat.cast_add]
    congr 1
    field_simp
  have := h.expGrowthSup_comp (v := fun n ↦ n + k) hv one_ne_zero (EReal.coe_ne_top 1)
  rwa [one_mul] at this
