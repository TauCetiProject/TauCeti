/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.MeanValue

/-!
# Cauchy's formula for iterated derivatives as a circle average

Mathlib's `DiffContOnCl.circleAverage_smul_div` writes the value of a holomorphic `f : ℂ → E` at a
point `z` of the disc `ball c ρ` as the circle average of `f` against the kernel
`(w - c) / (w - z)`. This file records the analogue for iterated derivatives:
`f^{(k)}(z)` is `k!` times the circle average of `f` against `(w - c) / (w - z) ^ (k + 1)`
(`DiffContOnCl.iteratedDeriv_eq_factorial_smul_circleAverage`). It is Mathlib's
`DiffContOnCl.circleIntegral_one_div_sub_pow_smul` rewritten with `dw = i (w - c) dθ` on
`sphere c ρ`.
-/

public section

open Complex Metric Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ → E} {c z : ℂ} {ρ : ℝ}

/-- **Cauchy's integral formula for iterated derivatives as a circle average.** If `f` is
holomorphic on `ball c ρ` and continuous on its closure, then for `z ∈ ball c ρ`, `f^{(k)}(z)` is
`k!` times the circle average of `f` against the kernel `(w - c) / (w - z) ^ (k + 1)`. -/
theorem DiffContOnCl.iteratedDeriv_eq_factorial_smul_circleAverage
    (hf : DiffContOnCl ℂ f (ball c ρ)) (k : ℕ) (hz : z ∈ ball c ρ) :
    iteratedDeriv k f z = (k.factorial : ℂ) •
      Real.circleAverage (fun w ↦ ((w - c) / (w - z) ^ (k + 1)) • f w) c ρ := by
  have hρ : 0 < ρ := dist_nonneg.trans_lt (mem_ball.mp hz)
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [circleAverage_eq_circleIntegral hρ.ne',
    circleIntegral.integral_congr hρ.le (g := fun w ↦ (1 / (w - z) ^ (k + 1)) • f w) ?_,
    hf.circleIntegral_one_div_sub_pow_smul k hz, smul_smul, smul_smul]
  · rw [eq_comm]
    convert one_smul ℂ (iteratedDeriv k f z) using 2
    field_simp
  · intro w hw
    have hu : w - c ≠ 0 := sub_ne_zero.2 (ne_of_mem_sphere hw hρ.ne')
    simp only [smul_smul]
    congr 1
    field_simp
