/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Differentiability of finite Dirichlet polynomials

`LSeries.differentiable_sum_term` states that a finite sum of Dirichlet terms is entire.
It supplies the correction to a holomorphic continuation after finitely many coefficient changes.
-/

public section

namespace LSeries

/-- A finite Dirichlet polynomial is entire, including at `s = 0`. -/
theorem differentiable_sum_term (c : ℕ → ℂ) (S : Finset ℕ) :
    Differentiable ℂ (fun s ↦ ∑ n ∈ S, LSeries.term c s n) :=
  Differentiable.fun_sum fun n _ s ↦ (LSeries.hasDerivAt_term c n s).differentiableAt

end LSeries
