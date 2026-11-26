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

For `k ≥ 1`, the same kernel is orthogonal to conjugates of holomorphic functions: the circle
average of `(w - c) / (w - z) ^ (k + 1)` against `conj (g w)` vanishes for every `g : ℂ → ℂ`
holomorphic on the disc and continuous on its closure
(`DiffContOnCl.circleAverage_div_sub_pow_mul_conj_eq_zero`). Together with the Cauchy formula
this expresses `f^{(k)}(z)` through the real part of `f` alone, which is the starting point of
the derivative form of the Borel–Carathéodory inequality.
-/

public section

open Complex Metric Real ComplexConjugate

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

/-- The Cauchy kernel `(w - c) / (w - z) ^ (k + 1)` of a point `z` of `ball c ρ` is continuous on
the circle `sphere c ρ`. -/
theorem Complex.continuousOn_div_sub_pow_sphere {k : ℕ} (hz : z ∈ ball c ρ) :
    ContinuousOn (fun w ↦ (w - c) / (w - z) ^ (k + 1)) (sphere c |ρ|) := by
  have hρ : 0 < ρ := dist_nonneg.trans_lt (mem_ball.mp hz)
  have h₁ : ContinuousOn (fun w : ℂ ↦ w - c) (sphere c ρ) := by fun_prop
  have h₂ : ContinuousOn (fun w : ℂ ↦ (w - z) ^ (k + 1)) (sphere c ρ) := by fun_prop
  rw [abs_of_pos hρ]
  refine h₁.div h₂ fun w hw ↦ pow_ne_zero _ (sub_ne_zero.2 fun hwz ↦ ?_)
  rw [mem_sphere, hwz] at hw
  exact (mem_ball.mp hz).ne hw

/-- The circle average of the Cauchy kernel `(w - c) / (w - z) ^ (k + 1)` against the conjugate of a
holomorphic function vanishes once `k ≥ 1`: on the circle, the conjugate kernel agrees with a
rational function that is holomorphic on the closed disc and vanishes at `c`. -/
theorem DiffContOnCl.circleAverage_div_sub_pow_mul_conj_eq_zero {g : ℂ → ℂ} {k : ℕ}
    (hg : DiffContOnCl ℂ g (ball c ρ)) (hk : 1 ≤ k) (hz : z ∈ ball c ρ) :
    Real.circleAverage (fun w ↦ (w - c) / (w - z) ^ (k + 1) * conj (g w)) c ρ = 0 := by
  have hzc : ‖z - c‖ < ρ := by simpa [dist_eq_norm] using hz
  have hρ : 0 < ρ := (norm_nonneg _).trans_lt hzc
  -- On the circle, `conj (w - c) = ρ ^ 2 / (w - c)`, so the conjugate of the kernel is the
  -- rational function `A` below, holomorphic on a neighbourhood of the closed disc.
  have hconjK (w : ℂ) (hw : w ∈ sphere c ρ) : conj ((w - c) / (w - z) ^ (k + 1)) =
      (ρ : ℂ) ^ 2 * (w - c) ^ k / ((ρ : ℂ) ^ 2 - (w - c) * conj (z - c)) ^ (k + 1) := by
    have hwc : ‖w - c‖ = ρ := by simpa [dist_eq_norm] using hw
    have hu : w - c ≠ 0 := norm_ne_zero_iff.mp (hwc.trans_ne hρ.ne')
    have hconj : conj (w - c) = (ρ : ℂ) ^ 2 / (w - c) := by
      rw [eq_div_iff hu, mul_comm, mul_conj, normSq_eq_norm_sq, hwc]; push_cast; ring
    have hsub : conj (w - z) = ((ρ : ℂ) ^ 2 - (w - c) * conj (z - c)) / (w - c) := by
      rw [show w - z = (w - c) - (z - c) by ring, map_sub, hconj]
      field_simp
    rw [map_div₀, map_pow, hconj, hsub, div_pow, pow_succ (w - c)]
    field_simp
  set A : ℂ → ℂ := fun w ↦
    (ρ : ℂ) ^ 2 * (w - c) ^ k / ((ρ : ℂ) ^ 2 - (w - c) * conj (z - c)) ^ (k + 1)
  have hden (w : ℂ) (hw : w ∈ closedBall c ρ) :
      ((ρ : ℂ) ^ 2 - (w - c) * conj (z - c)) ^ (k + 1) ≠ 0 := by
    refine pow_ne_zero _ fun h0 ↦ ?_
    have hwc : ‖w - c‖ ≤ ρ := by simpa [dist_eq_norm] using hw
    have : ‖(w - c) * conj (z - c)‖ = ρ ^ 2 := by
      rw [← sub_eq_zero.mp h0]
      simp [sq, abs_of_pos hρ]
    rw [norm_mul, norm_conj] at this
    nlinarith [norm_nonneg (z - c), norm_nonneg (w - c)]
  have hA : DifferentiableOn ℂ A (closure (ball c ρ)) := by
    have h₁ : DifferentiableOn ℂ (fun w : ℂ ↦ (ρ : ℂ) ^ 2 * (w - c) ^ k) (closedBall c ρ) := by
      fun_prop
    have h₂ : DifferentiableOn ℂ (fun w : ℂ ↦ ((ρ : ℂ) ^ 2 - (w - c) * conj (z - c)) ^ (k + 1))
        (closedBall c ρ) := by
      fun_prop
    rw [closure_ball c hρ.ne']
    exact h₁.div h₂ hden
  have hh : DiffContOnCl ℂ (fun w ↦ A w • g w) (ball c |ρ|) := by
    rw [abs_of_pos hρ]
    exact hA.diffContOnCl.smul hg
  calc Real.circleAverage (fun w ↦ (w - c) / (w - z) ^ (k + 1) * conj (g w)) c ρ
      = Real.circleAverage (conjCLE.toContinuousLinearMap ∘ fun w ↦ A w • g w) c ρ := by
        refine circleAverage_congr_sphere fun w hw ↦ ?_
        rw [abs_of_pos hρ] at hw
        simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply,
          smul_eq_mul, map_mul, A]
        rw [← hconjK w hw, conj_conj]
    _ = 0 := by
        rw [ContinuousLinearMap.circleAverage_comp_comm _
          (hh.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable',
          hh.circleAverage]
        simp [A, zero_pow (Nat.one_le_iff_ne_zero.mp hk)]
