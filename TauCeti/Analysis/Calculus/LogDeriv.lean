/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Derivative and logarithmic derivative of an even function at the origin

Over a nontrivially normed field of characteristic zero, the derivative `deriv f 0` and logarithmic
derivative `logDeriv f 0` of any even function `f` (`Function.Even f`) vanish at `0`, with no
differentiability or nonvanishing hypothesis (by Lean's totalization of `deriv` and division).

## Main results

* `Function.Even.deriv_zero`: `deriv f 0 = 0` when `f.Even`.
* `Function.Even.logDeriv_zero`: `logDeriv f 0 = 0` when `f.Even`.
-/

public section

/-- The derivative of an even function vanishes at `0` over a field of characteristic zero,
with no differentiability assumption (by totalization of `deriv`). -/
theorem Function.Even.deriv_zero {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} (hf : f.Even) : deriv f 0 = 0 := by
  have hneg : deriv (fun x ↦ f (-x)) 0 = -deriv f 0 := by
    simpa only [neg_zero] using deriv_comp_neg (f := f) (x := (0 : 𝕜))
  rw [funext hf] at hneg
  have htwo : (2 : 𝕜) • deriv f 0 = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hneg
  exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero

/-- The logarithmic derivative of an even function vanishes at `0` over a field of characteristic
zero, with no differentiability or nonvanishing assumption. -/
theorem Function.Even.logDeriv_zero {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {f : 𝕜 → 𝕜'} (hf : f.Even) :
    logDeriv f 0 = 0 := by
  rw [logDeriv_apply, hf.deriv_zero, zero_div]
