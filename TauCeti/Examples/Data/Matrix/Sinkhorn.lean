/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Sinkhorn.Rate
public import TauCeti.Data.Matrix.Scaling.TwoByTwo

/-!
# A rational Sinkhorn iteration with certified errors

The kernel `!![1, 1; 1, 4]` scales to the probability matrix
`!![1/3, 1/6; 1/6, 1/3]` with uniform marginals. Its projective diameter is `log 4`, so each
half-step has Birkhoff factor `1/3` and a full sweep has factor `1/9`.

Starting from row factors `1`, we compute the first two row-normalized plans exactly. At every
iteration we certify the column residual and the shortfall of the dual value from the optimal
entropy. The plans have exact row marginals but generally not exact column marginals, so their
primal objectives are not advertised as feasible upper bounds. The objective certificate uses
the feasible algebraic optimum and the dual potentials of the current iterate instead.
The objective is `Matrix.relEntropy`; the finite-measure KL mass correction is constant on
the prescribed-marginal polytope and does not change the optimizer or the primal-dual gap.

The certificates specialize `Matrix.sum_abs_sum_sinkhornPlan_iterate_apply_sub_le` and
`Matrix.IsDiagonalScaling.relEntropy_sub_relEntropyDual_iterate_le`; no new convergence
argument is needed.

All calculations are in exact real arithmetic. No floating-point evaluation or numerical
decision axiom is used. For Sinkhorn's algorithm and its dual interpretation see Peyré and
Cuturi, *Computational Optimal Transport*, Chapter 4.
-/

public section

open Matrix Real

namespace TauCeti.SinkhornExample

/-- A positive rational kernel with nontrivial Sinkhorn iteration. -/
def kernel : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 4]

/-- The entries of the example kernel. -/
theorem kernel_def : kernel = !![1, 1; 1, 4] := (rfl)

/-- The entropy-minimizing scaling with uniform probability marginals. -/
noncomputable def optimalPlan : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 3, 1 / 6; 1 / 6, 1 / 3]

/-- The entries of the optimal plan. -/
theorem optimalPlan_def : optimalPlan = !![1 / 3, 1 / 6; 1 / 6, 1 / 3] := (rfl)

/-- The row-normalized plan associated to row factors after `n` sweeps from `1`.
Forming the plan performs a column update followed by a row update. -/
noncomputable def iterate (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  kernel.sinkhornPlan (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2)
    ((kernel.sinkhornStep (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2))^[n] (fun _ ↦ 1))

/-- The defining iteration, in the generic matrix API. -/
theorem iterate_def (n : ℕ) : iterate n =
    kernel.sinkhornPlan (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2)
      ((kernel.sinkhornStep (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2))^[n] (fun _ ↦ 1)) := (rfl)

/-- The kernel is strictly positive. -/
theorem kernel_pos (i j : Fin 2) : 0 < kernel i j := by
  fin_cases i <;> fin_cases j <;> norm_num [kernel_def]

private theorem scaling : IsDiagonalScaling optimalPlan kernel ![1, 1 / 2] ![1 / 3, 1 / 6] := by
  rw [isDiagonalScaling_def]
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [kernel_def, optimalPlan_def]

private theorem row_pos (i : Fin 2) : 0 < (![1, 1 / 2] : Fin 2 → ℝ) i := by
  fin_cases i <;> norm_num

private theorem col_pos (j : Fin 2) : 0 < (![1 / 3, 1 / 6] : Fin 2 → ℝ) j := by
  fin_cases j <;> norm_num

/-- The algebraic solution has both prescribed marginals. -/
theorem optimalPlan_hasMarginals :
    HasMarginals optimalPlan (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2) := by
  rw [hasMarginals_def]
  constructor <;> intro i <;> fin_cases i <;>
    norm_num [optimalPlan_def, Fin.sum_univ_two]

/-- Every nonnegative plan with uniform marginals has entropy at least that of the explicit
algebraic solution. The reference is `kernel`, not the product of the marginals. -/
theorem relEntropy_optimalPlan_le {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : ∀ i j, 0 ≤ P i j) (hm : HasMarginals P (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2)) :
    relEntropy optimalPlan kernel ≤ relEntropy P kernel :=
  scaling.relEntropy_le kernel_pos row_pos col_pos optimalPlan_hasMarginals hP hm

/-- The projective diameter is exactly the logarithm of four. -/
@[simp] theorem projectiveDiameter_kernel : kernel.projectiveDiameter = log 4 := by
  rw [projectiveDiameter_fin_two kernel_pos]
  norm_num [kernel_def, abs_of_nonneg (log_nonneg (by norm_num : (1 : ℝ) ≤ 4))]

/-- Each half-step has contraction factor `1/3`, not merely an unspecified factor below one. -/
theorem tanh_projectiveDiameter_kernel : tanh (kernel.projectiveDiameter / 4) = 1 / 3 := by
  rw [projectiveDiameter_kernel]
  let s := exp (log 4 / 4)
  have hs : s * s = 2 := by
    simp only [s, ← exp_add]
    have hhalf : log (4 : ℝ) / 4 + log 4 / 4 = log 4 / 2 := by ring
    rw [hhalf, exp_half, exp_log (by norm_num),
      sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]
    norm_num
  calc tanh (log 4 / 4) = (s * s - 1) / (s * s + 1) := by
        rw [tanh_eq, exp_neg]
        dsimp [s]
        field_simp
    _ = 1 / 3 := by rw [hs]; norm_num

/-- The initial pair of half-steps, computed with rational arithmetic. -/
@[simp] theorem iterate_zero : iterate 0 = !![5 / 14, 1 / 7; 5 / 26, 4 / 13] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [iterate_def, sinkhornPlan_apply, sinkhornStep_def, sinkhornUpdate_def,
      mulVec_apply, kernel_def, Fin.sum_univ_two, vecHead, vecTail]

/-- After one further sweep the plan is still rational and closer to the algebraic optimum. -/
@[simp] theorem iterate_one : iterate 1 = !![41 / 122, 10 / 61; 41 / 242, 40 / 121] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [iterate_def, sinkhornPlan_apply, sinkhornStep_def, sinkhornUpdate_def,
      mulVec_apply, kernel_def, Fin.sum_univ_two, vecHead, vecTail]

/-- Every iterate has its row marginal exactly, even before convergence. -/
theorem sum_iterate_apply (n : ℕ) (i : Fin 2) : ∑ j, iterate n i j = 1 / 2 := by
  rw [iterate_def]
  exact sum_sinkhornPlan_apply kernel_pos _ (fun _ ↦ by norm_num)
    (sinkhornStep_iterate_pos kernel_pos (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)
      (fun _ ↦ zero_lt_one) n) i

/-- The initial column residual is nonzero: its exact `ℓ¹` value is `9/91`. -/
theorem sum_abs_sum_iterate_zero :
    ∑ j, |∑ i, iterate 0 i j - 1 / 2| = 9 / 91 := by
  norm_num [iterate_zero, Fin.sum_univ_two]

/-- A certified column-marginal error bound for every iteration. -/
theorem sum_abs_sum_iterate_sub_le (n : ℕ) :
    ∑ j, |∑ i, iterate n i j - 1 / 2| ≤ exp ((1 / 3 : ℝ) ^ (2 * n) * log 4) - 1 := by
  have h := sum_abs_sum_sinkhornPlan_iterate_apply_sub_le kernel_pos
    (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) scaling optimalPlan_hasMarginals
    row_pos col_pos (fun _ ↦ zero_lt_one) n
  rw [tanh_projectiveDiameter_kernel, projectiveDiameter_kernel] at h
  simpa only [iterate_def, Fin.sum_univ_two, add_halves, mul_one] using h

/-- The dual objective at the logarithms of the current scaling factors. -/
noncomputable def dualValue (n : ℕ) : ℝ :=
  kernel.relEntropyDual (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2)
    (fun i ↦ log ((kernel.sinkhornStep (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2))^[n + 1]
      (fun _ ↦ 1) i))
    (fun j ↦ log (kernelᵀ.sinkhornUpdate (fun _ ↦ 1 / 2)
      ((kernel.sinkhornStep (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2))^[n] (fun _ ↦ 1)) j))

/-- The dual value uses the logarithms of the next row factors and the current column update. -/
theorem dualValue_def (n : ℕ) : dualValue n =
    kernel.relEntropyDual (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2)
      (fun i ↦ log ((kernel.sinkhornStep (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2))^[n + 1]
        (fun _ ↦ 1) i))
      (fun j ↦ log (kernelᵀ.sinkhornUpdate (fun _ ↦ 1 / 2)
        ((kernel.sinkhornStep (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2))^[n] (fun _ ↦ 1)) j)) := (rfl)

/-- The dual value is a genuine lower bound, although the iterate need not be feasible. -/
theorem dualValue_le (n : ℕ) : dualValue n ≤ relEntropy optimalPlan kernel := by
  rw [dualValue_def]
  apply relEntropyDual_le_relEntropy kernel_pos
    (fun i j ↦ (scaling.pos kernel_pos row_pos col_pos i j).le) optimalPlan_hasMarginals

/-- The certified objective gap decays by `1/9` per full sweep. -/
theorem relEntropy_sub_dualValue_le (n : ℕ) :
    relEntropy optimalPlan kernel - dualValue n ≤ (1 / 3 : ℝ) ^ (2 * n) * log 4 := by
  have h := scaling.relEntropy_sub_relEntropyDual_iterate_le optimalPlan_hasMarginals kernel_pos
    (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) row_pos col_pos (fun _ ↦ zero_lt_one) n
  rw [tanh_projectiveDiameter_kernel, projectiveDiameter_kernel] at h
  simpa only [dualValue_def, Function.iterate_succ_apply', Fin.sum_univ_two, add_halves, one_mul]
    using h

end TauCeti.SinkhornExample
