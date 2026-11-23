/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.PositivePart

/-!
# Derivatives of positive-part powers

For every natural number `n ≠ 1`, the truncated power `x ↦ max x 0 ^ n` is everywhere
differentiable on `ℝ` with derivative `n * max x 0 ^ (n - 1)`, including at `x = 0` where both left
and right derivatives vanish (for `n = 0`, `max x 0 ^ 0 = 1`; for `n ≥ 2`, differentiation reduces
to the primitive formula `TauCeti.intervalIntegral.integral_max_zero_pow`). The hypothesis `n ≠ 1`
cannot be dropped: for `n = 1`, `x ↦ max x 0` is not differentiable at `0`.

## Main results

* `TauCeti.hasDerivAt_max_zero_pow`: `y ↦ max y 0 ^ n` has derivative `n * max x 0 ^ (n - 1)` at
  `x` for `n ≠ 1`.
* `HasDerivAt.max_zero_pow`: chain rule for composing `x ↦ max x 0 ^ n` (`n ≠ 1`) with a
  differentiable real function.
-/

public section

open Filter MeasureTheory

namespace TauCeti

/-- For `n ≠ 1`, `y ↦ max y 0 ^ n` has derivative `(n : ℝ) * max x 0 ^ (n - 1)` at every `x : ℝ`,
including at `x = 0`. -/
theorem hasDerivAt_max_zero_pow {n : ℕ} (hn : n ≠ 1) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ max y 0 ^ n) ((n : ℝ) * max x 0 ^ (n - 1)) x := by
  rcases n with _ | _ | m
  · simpa using hasDerivAt_const x (1 : ℝ)
  · exact (hn rfl).elim
  · have hm : 0 < m + 1 := Nat.succ_pos m
    have hc : Continuous fun y : ℝ ↦ max y 0 ^ (m + 1) := by fun_prop
    have hprim : HasDerivAt (fun y : ℝ ↦ ∫ u in (0 : ℝ)..y, max u 0 ^ (m + 1))
        (max x 0 ^ (m + 1)) x :=
      _root_.intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
        (hc.stronglyMeasurableAtFilter volume _) hc.continuousAt
    refine (hprim.const_mul ((m + 2 : ℕ) : ℝ)).congr_of_eventuallyEq
      (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    rw [TauCeti.intervalIntegral.integral_max_zero_pow hm 0 y, max_self,
      zero_pow (Nat.succ_ne_zero _), sub_zero]
    have hcast : ((m + 2 : ℕ) : ℝ) = (m + 1 : ℕ) + 1 := by push_cast; ring
    rw [hcast, mul_div_cancel₀ _ (by positivity)]

end TauCeti

namespace HasDerivAt

/-- Chain rule for composing `y ↦ max y 0 ^ n` (`n ≠ 1`) with a differentiable function
`f : ℝ → ℝ`. -/
theorem max_zero_pow {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) {n : ℕ} (hn : n ≠ 1) :
    HasDerivAt (fun y ↦ max (f y) 0 ^ n) ((n : ℝ) * max (f x) 0 ^ (n - 1) * f') x :=
  (TauCeti.hasDerivAt_max_zero_pow hn (f x)).comp x hf

end HasDerivAt
