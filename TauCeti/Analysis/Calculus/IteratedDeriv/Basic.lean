/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Smoothness from derivative towers

A sequence of functions linked by ordinary derivatives gives a smooth initial function.
-/

public section

open scoped ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A tower of functions with the stated successive ordinary derivatives gives a smooth zeroth
function. -/
theorem contDiff_of_derivative_tower (F : ℕ → ℝ → E)
    (hF : ∀ k x, HasDerivAt (F k) (F (k + 1) x) x) : ContDiff ℝ ∞ (F 0) := by
  have hiter (k : ℕ) : iteratedDeriv k (F 0) = F k := by
    induction k with
    | zero => exact iteratedDeriv_zero
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      exact funext (fun x ↦ (hF k x).deriv)
  apply contDiff_of_differentiable_iteratedDeriv (n := ⊤)
  intro k _
  rw [hiter k]
  exact fun x ↦ (hF k x).differentiableAt

end TauCeti
