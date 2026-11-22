/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Analysis.Normed.Group.Defs

/-!
# Norm scaling under iterated scalar actions

If acting by `u` turns the weighted norm `‖e‖ * r` into `‖u • e‖ * s` for every `e`, then
acting by `u ^ n` turns `‖e‖ * r ^ n` into `‖u ^ n • e‖ * s ^ n`. Only a monoid action and a
real-valued norm are needed. With `s = 1` and `r = ‖u‖` this is the scaling law
`‖u ^ n • e‖ = ‖e‖ * ‖u‖ ^ n` for an element `u` by which acting scales every norm by `‖u‖`;
the weighted form also covers `s = 0`.

## Main results

* `TauCeti.norm_pow_smul_mul_pow`: `‖u ^ n • e‖ * s ^ n = ‖e‖ * r ^ n` whenever
  `‖u • e‖ * s = ‖e‖ * r` for every `e`.
-/

public section

namespace TauCeti

/-- If acting by `u` changes the weighted norm `‖e‖ * r` into `‖u • e‖ * s` for every `e`, then
acting by `u ^ n` changes `‖e‖ * r ^ n` into `‖u ^ n • e‖ * s ^ n`. -/
theorem norm_pow_smul_mul_pow {M E : Type*} [Monoid M] [MulAction M E] [Norm E] {u : M}
    {r s : ℝ} (hu : ∀ e : E, ‖u • e‖ * s = ‖e‖ * r) (n : ℕ) (e : E) :
    ‖u ^ n • e‖ * s ^ n = ‖e‖ * r ^ n := by
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, pow_succ, ← mul_assoc, ih, mul_right_comm, hu, mul_assoc, ← pow_succ']

end TauCeti
