/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Derivatives of a composite with a function of temperate growth

If `q : E → F` has temperate growth, Faà di Bruno's bound `norm_iteratedFDeriv_comp_le` controls
the `n`-th derivative of a composite `f ∘ q` at `x` by `n!` times a bound for the derivatives of
`f` of order at most `n` at `q x`, times a polynomial in `‖x‖` that does not depend on `f`. This is
how the derivatives of Gaussians `exp ∘ q`, with `q` quadratic, are bounded.

## Main statements

* `Function.HasTemperateGrowth.exists_norm_iteratedFDeriv_comp_le`: the bound
  `‖D^n (f ∘ q) x‖ ≤ n! M (C (1 + ‖x‖)^j)^n` whenever `‖D^i f (q x)‖ ≤ M` for all `i ≤ n`.
-/

public section

open scoped Nat ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Faà di Bruno's bound for a composite with a function of temperate growth.** If `q` has
temperate growth and `f` is smooth, there are `j` and `C > 0` such that
`‖D^n (f ∘ q) x‖ ≤ n! M (C (1 + ‖x‖)^j)^n` whenever the derivatives of `f` of order at most `n`
at `q x` have norm at most `M`. -/
theorem Function.HasTemperateGrowth.exists_norm_iteratedFDeriv_comp_le {f : F → G} {q : E → F}
    (hf : ContDiff ℝ ∞ f) (hq : q.HasTemperateGrowth) (n : ℕ) :
    ∃ (j : ℕ) (C : ℝ), 0 < C ∧ ∀ (x : E) (M : ℝ),
      (∀ i ≤ n, ‖iteratedFDeriv ℝ i f (q x)‖ ≤ M) →
        ‖iteratedFDeriv ℝ n (f ∘ q) x‖ ≤ n ! * M * (C * (1 + ‖x‖) ^ j) ^ n := by
  obtain ⟨j, C₀, hC₀, hj⟩ := hq.norm_iteratedFDeriv_le_uniform n
  refine ⟨j, 1 + C₀, by positivity, fun x M hM ↦ ?_⟩
  have hD₁ : 1 ≤ (1 + C₀) * (1 + ‖x‖) ^ j :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by simp))
  refine norm_iteratedFDeriv_comp_le hf hq.1 (by exact_mod_cast le_top) x hM fun i hi hin ↦ ?_
  exact (hj i hin x).trans ((mul_le_mul_of_nonneg_right (by linarith) (by positivity) :
    C₀ * (1 + ‖x‖) ^ j ≤ (1 + C₀) * (1 + ‖x‖) ^ j).trans (le_self_pow₀ hD₁ (by omega)))
