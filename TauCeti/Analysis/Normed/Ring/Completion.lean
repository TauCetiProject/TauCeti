/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion

/-!
# Power-multiplicative norms on completions

The norm of the completion of a seminormed ring extends the norm of the ring by continuity, so
identities between continuous functions of the norm pass from the ring to its completion. This
file records that power-multiplicativity, `‖x ^ n‖ = ‖x‖ ^ n`, is such an identity. A
power-multiplicative norm determines the power-bounded elements of a normed ring with a
topologically nilpotent unit: they are exactly the elements of norm at most one.

## Main results

* `IsPowMul.completion`: the norm of the completion of a seminormed ring with a
  power-multiplicative norm is power-multiplicative.
-/

public section

open UniformSpace

/-- **The completion of a seminormed ring with a power-multiplicative norm has a
power-multiplicative norm.** Both sides of `‖x ^ n‖ = ‖x‖ ^ n` are continuous in `x` and agree on
the dense image of the ring. -/
theorem IsPowMul.completion {R : Type*} [SeminormedRing R] (h : IsPowMul (‖·‖ : R → ℝ)) :
    IsPowMul (‖·‖ : Completion R → ℝ) := by
  intro x n hn
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_pow n).norm (continuous_norm.pow n)
  | ih a =>
    have hcoe : ((a ^ n : R) : Completion R) = (a : Completion R) ^ n :=
      map_pow Completion.coeRingHom a n
    simp only [← hcoe, Completion.norm_coe, h a hn]
