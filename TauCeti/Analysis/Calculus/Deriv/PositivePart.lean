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

For every positive integer `n`, the truncated power `x ↦ max x 0 ^ (n + 1)` is everywhere
differentiable on `ℝ` with derivative `(n + 1) * max x 0 ^ n`, including at `x = 0` where both left
and right derivatives vanish. This follows directly by differentiating the primitive formula
`TauCeti.intervalIntegral.integral_max_zero_pow`. The positivity hypothesis `0 < n` cannot be
dropped: for `n = 0`, `x ↦ max x 0` is not differentiable at `0`.

## Main results

* `TauCeti.hasDerivAt_max_zero_pow`: `y ↦ max y 0 ^ (n + 1)` has derivative
  `(n + 1) * max x 0 ^ n` at `x` for `0 < n`.
* `HasDerivAt.max_zero_pow`: chain rule for composing `x ↦ max x 0 ^ (n + 1)` with a differentiable
  real function.
-/

public section

open Filter MeasureTheory

namespace TauCeti

/-- For `0 < n`, `y ↦ max y 0 ^ (n + 1)` has derivative `(n + 1) * max x 0 ^ n` at every `x : ℝ`,
including at `x = 0`. -/
theorem hasDerivAt_max_zero_pow {n : ℕ} (hn : 0 < n) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ max y 0 ^ (n + 1)) ((n + 1 : ℝ) * max x 0 ^ n) x := by
  have hc : Continuous fun y : ℝ ↦ max y 0 ^ n := by fun_prop
  have hprim : HasDerivAt (fun y : ℝ ↦ ∫ u in (0 : ℝ)..y, max u 0 ^ n) (max x 0 ^ n) x :=
    _root_.intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
      (hc.stronglyMeasurableAtFilter volume _) hc.continuousAt
  have hmul := hprim.const_mul (n + 1 : ℝ)
  refine hmul.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [TauCeti.intervalIntegral.integral_max_zero_pow hn 0 y, max_self,
    zero_pow (Nat.succ_ne_zero n), sub_zero, mul_div_cancel₀ _ (by positivity)]

end TauCeti

namespace HasDerivAt

/-- Chain rule for composing `y ↦ max y 0 ^ (n + 1)` (`0 < n`) with a differentiable function
`f : ℝ → ℝ`. -/
theorem max_zero_pow {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) {n : ℕ} (hn : 0 < n) :
    HasDerivAt (fun y ↦ max (f y) 0 ^ (n + 1)) ((n + 1 : ℝ) * max (f x) 0 ^ n * f') x :=
  (TauCeti.hasDerivAt_max_zero_pow hn (f x)).comp x hf

end HasDerivAt
