/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# Derivatives of a function composed with a map of temperate growth

If `q : E → F` has temperate growth, its first `n` derivatives grow at most polynomially, so
Faà di Bruno's estimate `norm_iteratedFDeriv_comp_le` bounds the `n`-th derivative of a composite
`f ∘ q` by the derivatives of `f` at `q x` times a polynomial weight in `‖x‖`. This is the step
behind the Schwartz-type bounds for Gaussians `exp ∘ q` with a quadratic exponent `q`, such as
the heat kernel and the complex Gaussian of a theta series.

## Main statements

* `Function.HasTemperateGrowth.exists_norm_iteratedFDeriv_comp_le`: if the derivatives of `f`
  of order at most `n` are bounded by `B` at `q x`, then
  `‖D^n (f ∘ q) x‖ ≤ n! B (1 + C)^n (1 + ‖x‖)^(j n)`, with `j` and `C` depending only on `q`
  and `n`.
-/

public section

open scoped Nat ContDiff

namespace Function.HasTemperateGrowth

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Faà di Bruno for a map of temperate growth.** If `q` has temperate growth, there are `j`
and `C ≥ 0` such that whenever the derivatives of `f` of order at most `n` are bounded by `B` at
`q x`, the `n`-th derivative of `f ∘ q` at `x` is bounded by `n! B (1 + C)^n (1 + ‖x‖)^(j n)`. -/
theorem exists_norm_iteratedFDeriv_comp_le {f : F → G} (hf : ContDiff ℝ ∞ f) {q : E → F}
    (hq : q.HasTemperateGrowth) (n : ℕ) :
    ∃ (j : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (x : E) (B : ℝ),
      (∀ i ≤ n, ‖iteratedFDeriv ℝ i f (q x)‖ ≤ B) →
        ‖iteratedFDeriv ℝ n (f ∘ q) x‖ ≤ n ! * B * (1 + C) ^ n * (1 + ‖x‖) ^ (j * n) := by
  obtain ⟨j, C, hC, hj⟩ := hq.norm_iteratedFDeriv_le_uniform n
  refine ⟨j, C, hC, fun x B hB ↦ ?_⟩
  -- The `i`-th derivative of `q` at `x` is at most `D ^ i` with `D = (1 + C) (1 + ‖x‖)^j ≥ 1`.
  set D : ℝ := (1 + C) * (1 + ‖x‖) ^ j
  have hD₁ : 1 ≤ D := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by simp))
  have hcomp : ‖iteratedFDeriv ℝ n (f ∘ q) x‖ ≤ n ! * B * D ^ n := by
    refine norm_iteratedFDeriv_comp_le hf hq.1 (by exact_mod_cast le_top) x hB
      (fun i hi hin ↦ ?_)
    exact (hj i hin x).trans ((mul_le_mul_of_nonneg_right (by linarith) (by positivity) :
      C * (1 + ‖x‖) ^ j ≤ D).trans (le_self_pow₀ hD₁ (by omega)))
  rwa [mul_assoc _ ((1 + C) ^ n), pow_mul, ← mul_pow]

end Function.HasTemperateGrowth
