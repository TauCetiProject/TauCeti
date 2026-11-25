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
* `ExpGrowth.expGrowthSup_comp_mul_of_monotone_exp_mul` — if `exp (c * n) * u n` is monotone
  for some real `c`, then `expGrowthSup (fun n ↦ u (k * n)) = k * expGrowthSup u` for `k ≠ 0`.
-/

public section

namespace ExpGrowth

open ENNReal EReal

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

/-- If the sequence `exp (c * n) * u n` is monotone, then the upper exponential growth rate of `u`
along the times `k * n` is `k` times that of `u`, for `k ≠ 0`. -/
theorem expGrowthSup_comp_mul_of_monotone_exp_mul {u : ℕ → ℝ≥0∞} {c : ℝ} {k : ℕ} (hk : k ≠ 0)
    (h : Monotone fun n : ℕ ↦ EReal.exp (c * n) * u n) :
    expGrowthSup (fun n ↦ u (k * n)) = k * expGrowthSup u := by
  have h₁ := h.expGrowthSup_comp_mul hk
  have hfun : (fun n : ℕ ↦ EReal.exp (c * ((k * n : ℕ) : EReal)) * u (k * n)) =
      fun n : ℕ ↦ EReal.exp (((c * k : ℝ) : EReal) * n) * u (k * n) := funext fun n ↦ by
    congr 2
    rw [← EReal.coe_natCast, ← EReal.coe_natCast, ← EReal.coe_mul, ← EReal.coe_mul]
    congr 1
    push_cast
    ring
  rw [hfun, expGrowthSup_exp_mul, expGrowthSup_exp_mul,
    EReal.left_distrib_of_nonneg_of_ne_top (by positivity) (EReal.natCast_ne_top k)] at h₁
  have h₂ : ((c * k : ℝ) : EReal) = (k : EReal) * (c : EReal) := by
    rw [mul_comm, EReal.coe_mul]
    rfl
  rw [h₂] at h₁
  have := congrArg (fun x : EReal ↦ x - ((k * c : ℝ) : EReal)) h₁
  simp only [EReal.coe_mul, EReal.coe_natCast] at this
  rwa [← EReal.coe_natCast, ← EReal.coe_mul, EReal.add_sub_cancel_left,
    EReal.add_sub_cancel_left] at this

end ExpGrowth
