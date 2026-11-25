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

end ExpGrowth
