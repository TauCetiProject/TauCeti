/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Dynamics.BirkhoffSum.NormedSpace

/-!
# Pointwise norm bounds for Birkhoff averages

Complements `Mathlib.Dynamics.BirkhoffSum.NormedSpace` with elementary pointwise norm
inequalities for `birkhoffAverage ℝ` over any self-map `T` and normed-module-valued observable
`f`, requiring no measure theory or ergodicity hypotheses.

## Main results

* `TauCeti.norm_birkhoffAverage_le` — the norm of `birkhoffAverage ℝ T f n x` is at most
  `birkhoffAverage ℝ T (fun y ↦ ‖f y‖) n x`.
-/

public section

namespace TauCeti

/-- Pointwise norm bound for Birkhoff averages: the norm of a Birkhoff average is bounded by the
Birkhoff average of the pointwise norms. -/
theorem norm_birkhoffAverage_le {Ω E : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    [IsBoundedSMul ℝ E] (T : Ω → Ω) (f : Ω → E) (n : ℕ) (x : Ω) :
    ‖birkhoffAverage ℝ T f n x‖ ≤ birkhoffAverage ℝ T (fun y ↦ ‖f y‖) n x := by
  simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
  calc
    ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, f (T^[k] x)‖
      ≤ ‖(n : ℝ)⁻¹‖ * ‖∑ k ∈ Finset.range n, f (T^[k] x)‖ := norm_smul_le _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, ‖f (T^[k] x)‖ := by
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

end TauCeti
