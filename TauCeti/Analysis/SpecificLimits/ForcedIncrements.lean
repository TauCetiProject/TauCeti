/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Increments damped by a factor and forced by a summable sequence

Let `x` be a sequence in a seminormed group whose increments `δ k = x (k + 1) - x k` obey

  `‖δ (k + 1)‖ ≤ q ‖δ k‖ + B φ k ‖x (k + 1)‖`

with `q, B ≥ 0` and a nonnegative summable forcing `φ`. The forcing term depends on `x` itself, so
a bound on the increments needs a bound on `x` and conversely. This file closes the loop by strong
induction: if `‖δ 0‖ ≤ D φ 0`, `‖x 0‖ + D ∑ φ ≤ M` and `(q D + B M) φ k ≤ D φ (k + 1)`, then every
increment satisfies `‖δ k‖ ≤ D φ k`; the induction carries the bound `‖x (k + 1)‖ ≤ M` along.

Such recursions arise from the increments of the quotient `v / u` of an exact solution `v` and an
approximate solution `u` of a second-order linear difference equation.

## Main results

* `TauCeti.norm_sub_le_mul_of_norm_sub_add_two_le`: the increment bound `‖δ k‖ ≤ D φ k`.
-/

public section

open Finset

namespace TauCeti

/-- **Increments forced by a summable sequence.** Let the increments of a sequence `x` in a
seminormed group satisfy
`‖x (k + 2) - x (k + 1)‖ ≤ q ‖x (k + 1) - x k‖ + B φ k ‖x (k + 1)‖`, where `φ ≥ 0` is summable and
`q, B ≥ 0`. If `‖x 1 - x 0‖ ≤ D φ 0` for some `D ≥ 0`, `‖x 0‖ + D ∑ φ ≤ M` and
`(q D + B M) φ k ≤ D φ (k + 1)` for every `k`, then `‖x (k + 1) - x k‖ ≤ D φ k` for every `k`. -/
theorem norm_sub_le_mul_of_norm_sub_add_two_le {E : Type*} [SeminormedAddCommGroup E]
    {x : ℕ → E} {φ : ℕ → ℝ} {q B D M : ℝ}
    (hx : ∀ k, ‖x (k + 2) - x (k + 1)‖ ≤ q * ‖x (k + 1) - x k‖ + B * φ k * ‖x (k + 1)‖)
    (hφ0 : ∀ k, 0 ≤ φ k) (hφ : Summable φ) (hq : 0 ≤ q) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (h0 : ‖x 1 - x 0‖ ≤ D * φ 0) (hM : ‖x 0‖ + D * ∑' k, φ k ≤ M)
    (hstep : ∀ k, (q * D + B * M) * φ k ≤ D * φ (k + 1)) (k : ℕ) :
    ‖x (k + 1) - x k‖ ≤ D * φ k := by
  -- strong induction: the bound up to `k` makes `‖x (k + 1)‖ ≤ M`
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | k
  · exact h0
  have hxk : ‖x (k + 1)‖ ≤ M := by
    rw [← sub_add_cancel (x (k + 1)) (x 0), ← sum_range_sub x (k + 1)]
    calc ‖∑ j ∈ range (k + 1), (x (j + 1) - x j) + x 0‖
        ≤ ∑ j ∈ range (k + 1), D * φ j + ‖x 0‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact (norm_sum_le _ _).trans (sum_le_sum fun j hj ↦ ih j (mem_range.1 hj))
      _ ≤ D * ∑' j, φ j + ‖x 0‖ := by
          rw [← mul_sum]
          gcongr
          exact hφ.sum_le_tsum _ fun j _ ↦ hφ0 j
      _ ≤ M := by linarith
  calc ‖x (k + 1 + 1) - x (k + 1)‖ ≤ q * ‖x (k + 1) - x k‖ + B * φ k * ‖x (k + 1)‖ := hx k
    _ ≤ q * (D * φ k) + B * φ k * M := by
        gcongr
        · exact ih k (by omega)
        · exact mul_nonneg hB (hφ0 k)
    _ = (q * D + B * M) * φ k := by ring
    _ ≤ D * φ (k + 1) := hstep k

end TauCeti
