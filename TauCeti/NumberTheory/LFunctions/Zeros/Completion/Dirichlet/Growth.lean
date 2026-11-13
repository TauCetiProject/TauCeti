/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.FiniteOrder
public import TauCeti.NumberTheory.LSeries.HurwitzZeta.Growth

/-!
# Order one and vertical-strip growth of primitive Dirichlet completions

For a primitive nonprincipal Dirichlet character `χ` modulo `N`, the completed function of the
record `dirichletData χ hχ` is `N ^ (s / 2)` times Mathlib's completed L-function. The polar terms
of Mathlib's Hurwitz decomposition cancel, so it is `N ^ (s / 2)` times the entire periodic
completion `ZMod.completedLFunction₀ χ`. This is `N ^ (-s / 2)` times a finite combination of
entire parts of Hurwitz functional-equation pairs, whose kernels decay exponentially.

The split Mellin estimates therefore give an explicit bound
`‖Λ(s)‖ ≤ exp (C (1 + ‖s‖) log (2 + ‖s‖))` on the whole plane. Hence the completion has order
at most one (`dirichletData_completed_orderLE_one`, the Dirichlet instance of the order bound for
split Mellin integrals), and the record has finite order. On each closed vertical strip the
Mellin bounds depend only on the real part, so the completion has vertical-strip growth.

This route does not use Stirling's formula, partial summation or the functional equation.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 5.
* H. Davenport, *Multiplicative Number Theory*, Chapter 12.
-/

public section

open Complex

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-- The completed function of a primitive nonprincipal Dirichlet record is the conductor power
times the entire periodic completion. -/
theorem dirichletData_completed_eq_mul_completedLFunction₀ (hne : χ ≠ 1) (s : ℂ) :
    (dirichletData χ hχ).completed s = (N : ℂ) ^ (s / 2) * ZMod.completedLFunction₀ (χ ·) s := by
  rw [dirichletData_completed, χ.completedLFunction_eq_completedLFunction₀ hne]

/-- **Explicit order-one bound.** The completed function of a primitive nonprincipal Dirichlet
record satisfies `‖Λ(s)‖ ≤ exp (C (1 + ‖s‖) log (2 + ‖s‖))` on the whole plane. -/
theorem exists_norm_dirichletData_completed_le_exp_mul_log (hne : χ ≠ 1) :
    ∃ C > 0, ∀ s : ℂ, ‖(dirichletData χ hχ).completed s‖ ≤
      Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨C, hC, hb⟩ := ZMod.exists_norm_completedLFunction₀_le_exp_mul_log (χ ·)
  refine ⟨Real.log N + C, by positivity, fun s ↦ ?_⟩
  have hpow := norm_natCast_cpow_ofReal_mul_le_exp_mul_log (NeZero.ne N) (1 / 2) s
  rw [show ((1 / 2 : ℝ) : ℂ) * s = s / 2 by push_cast; ring,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_one_div_cancel two_ne_zero, one_mul] at hpow
  rw [dirichletData_completed_eq_mul_completedLFunction₀ χ hχ hne, norm_mul, add_mul, add_mul,
    Real.exp_add]
  exact mul_le_mul hpow (hb s) (norm_nonneg _) (Real.exp_pos _).le

/-- **Order at most one.** The completed function of a primitive nonprincipal Dirichlet record
is entire of order at most one. -/
theorem dirichletData_completed_orderLE_one (hne : χ ≠ 1) :
    OrderLE (dirichletData χ hχ).completed 1 := by
  obtain ⟨C, -, hC⟩ := exists_norm_dirichletData_completed_le_exp_mul_log χ hχ hne
  exact orderLE_one_of_norm_le_exp_mul_log hC

/-- A primitive nonprincipal Dirichlet record has finite order. -/
theorem dirichletData_isFiniteOrder (hne : χ ≠ 1) : (dirichletData χ hχ).IsFiniteOrder := by
  rw [AnalyticLFunctionData.IsFiniteOrder, dirichletData_entireCompletion_of_ne_one χ hχ hne]
  exact (dirichletData_completed_orderLE_one χ hχ hne).isFiniteOrder

/-- **Vertical-strip growth.** The completed function of a primitive nonprincipal Dirichlet
record has vertical-strip growth. -/
theorem dirichletData_completed_hasVerticalStripGrowth (hne : χ ≠ 1) :
    HasVerticalStripGrowth (dirichletData χ hχ).completed := by
  refine (hasVerticalStripGrowth_congr fun s ↦ ?_).mpr
    ((hasVerticalStripGrowth_natCast_cpow_ofReal_mul (NeZero.ne N) (1 / 2)).mul
      (ZMod.hasVerticalStripGrowth_completedLFunction₀ (χ ·)))
  rw [dirichletData_completed_eq_mul_completedLFunction₀ χ hχ hne,
    show s / 2 = ((1 / 2 : ℝ) : ℂ) * s by push_cast; ring]

end TauCeti.LFunctions
