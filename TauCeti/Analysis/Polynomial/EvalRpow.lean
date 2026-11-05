/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Real polynomials evaluated at real powers

For a nonnegative real `x`, a real polynomial `p` evaluated at `x ^ ε` and multiplied by `x ^ a`
expands into real powers of `x`, one per coefficient:
`x ^ a * p.eval (x ^ ε) = ∑ᵢ pᵢ x ^ (a + i ε)` for `0 < a` and `0 ≤ ε`. Applied termwise to a
nonnegative family `f`, the series `∑ⱼ f j ^ a * p.eval (f j ^ ε)` therefore converges, and splits
into the series `∑ⱼ f j ^ (a + i ε)`, as soon as each of these finitely many series converges.
This is how a polynomial test function `p (μ ^ ε)` is evaluated against a zeta function
`∑ⱼ μⱼ ^ s` in Karamata's proof of the Hardy–Littlewood Tauberian theorem.

## Main results

* `Polynomial.rpow_mul_eval_rpow_eq_sum`: `x ^ a * p.eval (x ^ ε) = ∑ᵢ pᵢ x ^ (a + i ε)`.
* `Polynomial.summable_rpow_mul_eval_rpow`: `∑ⱼ f j ^ a * p.eval (f j ^ ε)` converges when each
  `∑ⱼ f j ^ (a + i ε)` with `i ≤ natDegree p` does.
* `Polynomial.tsum_rpow_mul_eval_rpow_eq_sum`: the series `∑ⱼ f j ^ a * p.eval (f j ^ ε)` in terms
  of the series `∑ⱼ f j ^ (a + i ε)`.
-/

public section

open Finset Real

namespace Polynomial

/-- A real polynomial evaluated at `x ^ ε` and multiplied by `x ^ a` is a sum of real powers of
`x`, one for each coefficient. -/
theorem rpow_mul_eval_rpow_eq_sum {x a ε : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (hε : 0 ≤ ε)
    (p : ℝ[X]) :
    x ^ a * p.eval (x ^ ε) = ∑ i ∈ range (p.natDegree + 1), p.coeff i * x ^ (a + i * ε) := by
  rw [eval_eq_sum_range, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← rpow_mul_natCast hx, mul_left_comm,
    ← rpow_add' hx (show a + ε * (i : ℝ) ≠ 0 by positivity), mul_comm ε]

/-- The series `∑ⱼ f j ^ a * p.eval (f j ^ ε)` over a nonnegative family converges when each
series `∑ⱼ f j ^ (a + i ε)` with `i ≤ natDegree p` does. -/
theorem summable_rpow_mul_eval_rpow {ι : Type*} {f : ι → ℝ} (hf : ∀ j, 0 ≤ f j) {a ε : ℝ}
    (ha : 0 < a) (hε : 0 ≤ ε) (p : ℝ[X])
    (hsum : ∀ i ≤ p.natDegree, Summable fun j ↦ f j ^ (a + i * ε)) :
    Summable fun j ↦ f j ^ a * p.eval (f j ^ ε) :=
  (summable_sum fun i hi ↦ (hsum i (Nat.lt_succ_iff.1 (mem_range.1 hi))).mul_left
    (p.coeff i)).congr fun j ↦ (rpow_mul_eval_rpow_eq_sum (hf j) ha hε p).symm

/-- The series `∑ⱼ f j ^ a * p.eval (f j ^ ε)` over a nonnegative family, in terms of the series
`∑ⱼ f j ^ (a + i ε)`, provided these converge for `i ≤ natDegree p`. -/
theorem tsum_rpow_mul_eval_rpow_eq_sum {ι : Type*} {f : ι → ℝ} (hf : ∀ j, 0 ≤ f j) {a ε : ℝ}
    (ha : 0 < a) (hε : 0 ≤ ε) (p : ℝ[X])
    (hsum : ∀ i ≤ p.natDegree, Summable fun j ↦ f j ^ (a + i * ε)) :
    ∑' j, f j ^ a * p.eval (f j ^ ε) =
      ∑ i ∈ range (p.natDegree + 1), p.coeff i * ∑' j, f j ^ (a + i * ε) := by
  have hsum' : ∀ i ∈ range (p.natDegree + 1), Summable fun j ↦ f j ^ (a + i * ε) :=
    fun i hi ↦ hsum i (Nat.lt_succ_iff.1 (mem_range.1 hi))
  rw [tsum_congr fun j ↦ rpow_mul_eval_rpow_eq_sum (hf j) ha hε p,
    Summable.tsum_finsetSum fun i hi ↦ (hsum' i hi).mul_left _]
  exact sum_congr rfl fun i hi ↦ (hsum' i hi).tsum_mul_left _

end Polynomial
