/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Norm bounds for finite chains of kernels

A kernel sends a family of input vectors to a family of output vectors by summing one
linear map application per input index. In a chain, the index types and coefficient spaces
may vary at each step. An exponential bound for the final norm adds the logarithmic
costs of the kernels and the costs of counting the intermediate indices.
-/

public section

open Finset Real

namespace LinearMap

variable {𝕜 : Type*} {I V : ℕ → Type*} [∀ j, Fintype (I j)]

section

variable [Semiring 𝕜] [∀ j, AddCommMonoid (V j)] [∀ j, Module 𝕜 (V j)]

/-- Apply the first `n` finite kernels, summing over the input indices at each step. -/
def sumKernelChain (K : ∀ j, I j → I (j + 1) → V j →ₗ[𝕜] V (j + 1)) (v : I 0 → V 0) :
    (n : ℕ) → I n → V n
  | 0 => v
  | n + 1 => fun b ↦ ∑ a, K n a b (sumKernelChain K v n a)

/-- A chain of length zero leaves the input family unchanged. -/
@[simp]
theorem sumKernelChain_zero (K : ∀ j, I j → I (j + 1) → V j →ₗ[𝕜] V (j + 1))
    (v : I 0 → V 0) : sumKernelChain K v 0 = v := (rfl)

/-- Extending the chain by one step sums the next kernel against the previous output. -/
@[simp]
theorem sumKernelChain_succ_apply (K : ∀ j, I j → I (j + 1) → V j →ₗ[𝕜] V (j + 1))
    (v : I 0 → V 0) (n : ℕ) (b : I (n + 1)) :
    sumKernelChain K v (n + 1) b = ∑ a, K n a b (sumKernelChain K v n a) := (rfl)

end

/-- A pointwise norm estimate for the kernels gives a bound on each output of the chain;
only the cardinalities of the summation indices are charged. -/
theorem norm_sumKernelChain_le_exp [Semiring 𝕜] [∀ j, SeminormedAddCommGroup (V j)]
    [∀ j, Module 𝕜 (V j)] (K : ∀ j, I j → I (j + 1) → V j →ₗ[𝕜] V (j + 1))
    {v : I 0 → V 0} {n : ℕ} {B : ℝ} {c r : ℕ → ℝ}
    (hv : ∀ a, ‖v a‖ ≤ exp B)
    (hc : ∀ j < n, (Fintype.card (I j) : ℝ) ≤ exp (c j))
    (hK : ∀ j < n, ∀ a b u, ‖K j a b u‖ ≤ exp (r j) * ‖u‖) (b : I n) :
    ‖sumKernelChain K v n b‖ ≤ exp (B + ∑ j ∈ Finset.range n, (c j + r j)) := by
  induction n with
  | zero => simpa using hv b
  | succ n ih =>
    rw [sumKernelChain_succ_apply, sum_range_succ]
    have hprev := ih (fun j hj ↦ hc j (hj.trans (Nat.lt_succ_self n)))
      (fun j hj ↦ hK j (hj.trans (Nat.lt_succ_self n)))
    calc
      ‖∑ a, K n a b (sumKernelChain K v n a)‖ ≤
          ∑ a, ‖K n a b (sumKernelChain K v n a)‖ := norm_sum_le _ _
      _ ≤ ∑ _a : I n, exp (r n) * exp (B + ∑ j ∈ Finset.range n, (c j + r j)) :=
        sum_le_sum fun a _ ↦ (hK n (Nat.lt_succ_self n) a b _).trans
          (mul_le_mul_of_nonneg_left (hprev a) (exp_nonneg _))
      _ ≤ exp (c n) * (exp (r n) * exp (B + ∑ j ∈ Finset.range n, (c j + r j))) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hc n (Nat.lt_succ_self n)) (by positivity)
      _ = exp (B + ((∑ j ∈ Finset.range n, (c j + r j)) + (c n + r n))) := by
        rw [← mul_assoc, ← exp_add, ← exp_add, add_comm (c n + r n), add_assoc]

end LinearMap
