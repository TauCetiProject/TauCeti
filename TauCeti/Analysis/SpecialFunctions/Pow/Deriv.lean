/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivative steps for iterated derivatives of real and complex power functions

This file records one-step `HasDerivAt` identities for the explicit iterated derivatives of
`y ↦ y ^ α` (`α : ℝ`) and `y ↦ (y : ℂ) ^ c` (`c : ℂ`), continuing Mathlib's
`Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean` and complementing `Real.iter_deriv_rpow_const`
(which gives `deriv^[k]` without proving `HasDerivAt`).

## Main results

* `TauCeti.hasDerivAt_descPochhammer_mul_rpow`: for `x ≠ 0` or `i + 1 ≤ α`,
  `y ↦ (descPochhammer ℝ i).eval α * y ^ (α - i)` has derivative
  `(descPochhammer ℝ (i + 1)).eval α * x ^ (α - (i + 1 : ℕ))` at `x`.
* `TauCeti.hasDerivAt_descPochhammer_mul_ofReal_cpow`: for nonzero real `x`,
  `y ↦ (descPochhammer ℂ i).eval c * (y : ℂ) ^ (c - i)` has derivative
  `(descPochhammer ℂ (i + 1)).eval c * (x : ℂ) ^ (c - (i + 1 : ℕ))` at `x`.
-/

public section

namespace TauCeti

/-- Derivative step for the `i`-th derivative of `y ↦ y ^ α`: for `x ≠ 0` or `i + 1 ≤ α`,
`y ↦ (descPochhammer ℝ i).eval α * y ^ (α - i)` has derivative
`(descPochhammer ℝ (i + 1)).eval α * x ^ (α - (i + 1 : ℕ))` at `x`. -/
theorem hasDerivAt_descPochhammer_mul_rpow (α : ℝ) (i : ℕ) {x : ℝ}
    (hx : x ≠ 0 ∨ (i : ℝ) + 1 ≤ α) :
    HasDerivAt (fun y : ℝ => (descPochhammer ℝ i).eval α * y ^ (α - i))
      ((descPochhammer ℝ (i + 1)).eval α * x ^ (α - (i + 1 : ℕ))) x := by
  have hd := (Real.hasDerivAt_rpow_const (p := α - i)
    (hx.imp_right fun h => by linarith)).const_mul ((descPochhammer ℝ i).eval α)
  refine hd.congr_deriv ?_
  rw [descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_natCast, Nat.cast_add, Nat.cast_one]
  ring_nf

/-- Derivative step for the `i`-th real derivative of `y ↦ (y : ℂ) ^ c`: at every nonzero real `x`,
`y ↦ (descPochhammer ℂ i).eval c * (y : ℂ) ^ (c - i)` has derivative
`(descPochhammer ℂ (i + 1)).eval c * (x : ℂ) ^ (c - (i + 1 : ℕ))`. -/
theorem hasDerivAt_descPochhammer_mul_ofReal_cpow (c : ℂ) (i : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (descPochhammer ℂ i).eval c * (y : ℂ) ^ (c - i))
      ((descPochhammer ℂ (i + 1)).eval c * (x : ℂ) ^ (c - (i + 1 : ℕ))) x := by
  rcases eq_or_ne (c - i) 0 with h0 | h0
  · have hfn : (fun y : ℝ => (descPochhammer ℂ i).eval c * (y : ℂ) ^ (c - i)) =
        fun _ => (descPochhammer ℂ i).eval c := by ext y; simp [h0]
    rw [hfn, descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_natCast, h0, mul_zero, zero_mul]
    exact hasDerivAt_const x _
  · have hd := (hasDerivAt_ofReal_cpow_const hx h0).const_mul ((descPochhammer ℂ i).eval c)
    refine hd.congr_deriv ?_
    rw [descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_natCast, Nat.cast_add, Nat.cast_one]
    ring_nf

end TauCeti
