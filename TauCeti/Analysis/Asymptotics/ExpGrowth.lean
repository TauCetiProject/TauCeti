/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Asymptotics.ExpGrowth

/-!
# Exponential growth of products with an exactly growing factor

Mathlib's `ExpGrowth.expGrowthSup_mul_le` and `ExpGrowth.le_expGrowthSup_mul'` bound the upper
exponential growth of a product `u * v` above by `expGrowthSup u + expGrowthSup v` and below by
`expGrowthInf u + expGrowthSup v`. When `u` has an exact, finite exponential growth rate `a`, the
two bounds agree, so multiplying by `u` shifts the upper exponential growth by `a`.

## Main results

* `ExpGrowth.expGrowthSup_mul_of_expGrowthInf_eq` — if `expGrowthInf u = expGrowthSup u = a` with
  `a` real, then `expGrowthSup (u * v) = a + expGrowthSup v`.
* `ExpGrowth.expGrowthSup_exp_mul` — `expGrowthSup (fun n ↦ exp (a * n) * v n) = a +
  expGrowthSup v` for real `a`.
* `ExpGrowth.expGrowthSup_comp_mul_le` — `expGrowthSup (fun n ↦ u (k * n)) ≤ k * expGrowthSup u`
  for `k ≠ 0`.
* `ExpGrowth.expGrowthSup_comp_mul_of_monotone_exp_mul` — if `exp (c * n) * u n` is monotone
  for some real `c`, then `expGrowthSup (fun n ↦ u (k * n)) = k * expGrowthSup u` for `k ≠ 0`.
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
  have hkn : Tendsto (fun n : ℕ ↦ k * n) atTop atTop :=
    tendsto_id.const_mul_atTop' (Nat.pos_of_ne_zero hk)
  filter_upwards [hkn.eventually (eventually_le_exp hb')] with n hn
  rwa [EReal.natCast_mul, ← mul_assoc,
    EReal.div_mul_cancel (natCast_ne_bot k) (natCast_ne_top k) hk₀.ne'] at hn

/-- If the sequence `exp (c * n) * u n` is monotone, then the upper exponential growth rate of `u`
along the times `k * n` is `k` times that of `u`, for `k ≠ 0`. -/
theorem expGrowthSup_comp_mul_of_monotone_exp_mul {u : ℕ → ℝ≥0∞} {c : ℝ} {k : ℕ} (hk : k ≠ 0)
    (h : Monotone fun n : ℕ ↦ EReal.exp (c * n) * u n) :
    expGrowthSup (fun n ↦ u (k * n)) = k * expGrowthSup u := by
  have h₁ := h.expGrowthSup_comp_mul hk
  have hfun : (fun n : ℕ ↦ EReal.exp (c * ((k * n : ℕ) : EReal)) * u (k * n)) =
      fun n : ℕ ↦ EReal.exp (((c * k : ℝ) : EReal) * n) * u (k * n) := funext fun n ↦ by
    rw [EReal.natCast_mul, ← mul_assoc, ← EReal.coe_natCast (n := k), ← EReal.coe_mul]
  rw [hfun, expGrowthSup_exp_mul, expGrowthSup_exp_mul,
    EReal.left_distrib_of_nonneg_of_ne_top (by positivity) (EReal.natCast_ne_top k),
    ← EReal.coe_natCast, ← EReal.coe_mul, mul_comm (k : ℝ)] at h₁
  simpa only [EReal.add_sub_cancel_left, EReal.coe_natCast] using
    congrArg (· - ((c * k : ℝ) : EReal)) h₁

end ExpGrowth
