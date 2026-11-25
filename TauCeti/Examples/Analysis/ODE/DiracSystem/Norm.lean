/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.DiracSystem.Norm
public import Mathlib.Analysis.Matrix.Normed

/-!
# Checks for constant potentials of the Dirac system

* **A purely imaginary constant potential.** For `q = ic` with `c` real, at `z = 0`,
  `Θ = (cosh ct, -sinh ct)` and `Φ = (-sinh ct, cosh ct)`
  (`TauCeti.Examples.DiracSystem.diracFundamentalMatrix_I_mul_const_zero`), and
  `det M = cosh² ct - sinh² ct = 1`
  (`TauCeti.Examples.DiracSystem.det_diracFundamentalMatrix_I_mul_const_zero`).
* **The norm convention.** For `q = 1 + i` on `[0, 1]` at `z = 0`,
  `M(1, 0) = cosh(√2) + (sinh(√2)/√2) Ω Q_q` with `Ω Q_q = [[1, -1], [-1, -1]]`
  (`TauCeti.Examples.DiracSystem.diracFundamentalMatrix_one_add_I`). Its Euclidean operator norm
  is `e^{√2} = exp(t|z| + ∫₀¹ |q|)`, so the bound is attained
  (`TauCeti.Examples.DiracSystem.norm_toEuclideanCLM_diracFundamentalMatrix_one_add_I`). Its
  maximum-row-sum norm, the operator norm for the sup-norm carrier `Fin 2 → ℂ`, exceeds `e^{√2}`,
  so the bound fails in that norm
  (`TauCeti.Examples.DiracSystem.exp_sqrt_two_lt_linfty_opNorm_diracFundamentalMatrix_one_add_I`).
-/

public section

open MeasureTheory Set Matrix Complex

namespace TauCeti.Examples.DiracSystem

/-- **A purely imaginary constant potential.** For `q = ic` with `c` real, at `z = 0`,
`M(t, 0) = [[cosh ct, -sinh ct], [-sinh ct, cosh ct]]`. -/
theorem diracFundamentalMatrix_I_mul_const_zero (c t : ℝ) :
    diracFundamentalMatrix (fun _ ↦ I * c) t 0 =
      !![(Real.cosh (c * t) : ℂ), -(Real.sinh (c * t) : ℂ);
        -(Real.sinh (c * t) : ℂ), (Real.cosh (c * t) : ℂ)] := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : (fun _ : ℝ ↦ I * ((0 : ℝ) : ℂ)) = 0 := by ext; simp
    rw [h0, diracFundamentalMatrix_zero_potential]
    simp
  have hc' : I * (c : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.2 hc)
  have hn : ‖I * (c : ℂ)‖ = |c| := by simp
  have hs : Real.sinh (t * |c|) / |c| * c = Real.sinh (c * t) := by
    rcases lt_or_gt_of_ne hc with h | h
    · rw [abs_of_neg h, mul_neg, Real.sinh_neg]
      field_simp
    · rw [abs_of_pos h]
      field_simp
  have hch : Real.cosh (t * |c|) = Real.cosh (c * t) := by
    rcases le_total 0 c with h | h
    · rw [abs_of_nonneg h, mul_comm]
    · rw [abs_of_nonpos h, mul_neg, Real.cosh_neg, mul_comm]
  rw [diracFundamentalMatrix_const_zero hc', hn, hch]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← hs]

/-- For `q = ic` at `z = 0`, `det M(t, 0) = cosh² ct - sinh² ct = 1`. -/
theorem det_diracFundamentalMatrix_I_mul_const_zero (c t : ℝ) :
    (diracFundamentalMatrix (fun _ ↦ I * c) t 0).det = 1 := by
  rw [diracFundamentalMatrix_I_mul_const_zero, det_fin_two_of]
  have h := Real.cosh_sq_sub_sinh_sq (c * t)
  have h' : ((Real.cosh (c * t) : ℂ)) ^ 2 - (Real.sinh (c * t) : ℂ) ^ 2 = 1 := by
    exact_mod_cast h
  linear_combination h'

/-- `|1 + i| = √2`. -/
private theorem norm_one_add_I : ‖(1 : ℂ) + I‖ = √2 := by
  rw [norm_def, normSq_apply]
  norm_num

/-- **The norm convention.** For `q = 1 + i` at `z = 0`,
`M(1, 0) = cosh(√2) + (sinh(√2)/√2) [[1, -1], [-1, -1]]`. -/
theorem diracFundamentalMatrix_one_add_I :
    diracFundamentalMatrix (fun _ ↦ 1 + I) 1 0 =
      (Real.cosh √2 : ℂ) • 1 + ((Real.sinh √2 / √2 : ℝ) : ℂ) • !![1, -1; -1, -1] := by
  rw [diracFundamentalMatrix_const_zero (by simp [Complex.ext_iff]), norm_one_add_I, one_mul]
  simp

/-- **The norm bound is attained.** For `q = 1 + i` on `[0, 1]` at `z = 0`, the Euclidean operator
norm of `M(1, 0)` is `e^{√2} = exp(1 · |0| + ∫₀¹ |q|)`. -/
theorem norm_toEuclideanCLM_diracFundamentalMatrix_one_add_I :
    ‖toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix (fun _ ↦ 1 + I) 1 0)‖ =
      Real.exp √2 ∧
    Real.exp √2 = Real.exp (1 * ‖(0 : ℂ)‖ + ∫ _ in (0 : ℝ)..1, ‖(1 : ℂ) + I‖) := by
  refine ⟨?_, ?_⟩
  · rw [norm_toEuclideanCLM_diracFundamentalMatrix_const_zero _ zero_le_one, norm_one_add_I,
      one_mul]
  · simp [norm_one_add_I]

open scoped Matrix.Norms.Operator in
/-- **The bound fails for the sup norm.** The maximum-row-sum norm of `M(1, 0)` for `q = 1 + i`,
which is the operator norm for the carrier `Fin 2 → ℂ` with the sup norm, is
`cosh(√2) + √2 sinh(√2) > e^{√2}`. -/
theorem exp_sqrt_two_lt_linfty_opNorm_diracFundamentalMatrix_one_add_I :
    Real.exp √2 < ‖diracFundamentalMatrix (fun _ ↦ 1 + I) 1 0‖ := by
  set s : ℝ := Real.sinh √2 / √2
  have hs : 0 < s := div_pos (Real.sinh_pos_iff.2 (by positivity)) (by positivity)
  have hrow : Real.cosh √2 + 2 * s ≤ ‖diracFundamentalMatrix (fun _ ↦ 1 + I) 1 0‖ := by
    have h := Finset.le_sup (f := fun i : Fin 2 ↦ ∑ j : Fin 2,
      ‖diracFundamentalMatrix (fun _ ↦ 1 + I) 1 0 i j‖₊) (Finset.mem_univ 0)
    rw [← linfty_opNNNorm_def] at h
    have h' : ((∑ j : Fin 2, ‖diracFundamentalMatrix (fun _ ↦ 1 + I) 1 0 0 j‖₊ : NNReal) : ℝ) ≤
        ‖diracFundamentalMatrix (fun _ ↦ 1 + I) 1 0‖ := h
    have e00 : diracFundamentalMatrix (fun _ ↦ 1 + I) 1 0 0 0 = ((Real.cosh √2 + s : ℝ) : ℂ) := by
      rw [diracFundamentalMatrix_one_add_I]
      simp [s]
    have e01 : diracFundamentalMatrix (fun _ ↦ 1 + I) 1 0 0 1 = -((s : ℝ) : ℂ) := by
      rw [diracFundamentalMatrix_one_add_I]
      simp [s]
    refine le_of_eq_of_le ?_ h'
    have hpos : 0 < Real.cosh √2 + s := by positivity
    rw [Fin.sum_univ_two, NNReal.coe_add, coe_nnNorm, coe_nnNorm, e00, e01, norm_neg, norm_real,
      norm_real, Real.norm_of_nonneg hpos.le, Real.norm_of_nonneg hs.le]
    ring
  have h2 : s * 2 = √2 * Real.sinh √2 := by
    simp only [s]
    field_simp
    rw [Real.sq_sqrt zero_le_two]
  have hsinh : 0 < Real.sinh √2 := Real.sinh_pos_iff.2 (by positivity)
  have hlt : 1 < √2 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one one_lt_two
  refine lt_of_lt_of_le ?_ hrow
  rw [← Real.cosh_add_sinh, mul_comm 2 s, h2]
  nlinarith

end TauCeti.Examples.DiracSystem
