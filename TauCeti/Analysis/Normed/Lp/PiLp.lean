/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Monotonicity of finite product norms

The finite `Lᵖ` norm respects coordinatewise bounds on norms, including when the two
families have different target spaces. This compares scalar evaluations of a vector
family with the vector family's `Lᵖ` norm.
-/

public section

open scoped ENNReal

namespace PiLp

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞}
  {E F : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)]
  [∀ i, SeminormedAddCommGroup (F i)]

/-- Coordinatewise domination of norms implies domination of finite `Lᵖ` norms. -/
theorem norm_mono {x : PiLp p E} {y : PiLp p F}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [norm_eq_card, norm_eq_card]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    apply Set.Finite.toFinset_mono
    intro i hi hzero
    exact hi (le_antisymm (by simpa only [hzero] using h i) (norm_nonneg _))
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [norm_eq_ciSup, norm_eq_ciSup]
    exact ciSup_mono (Set.finite_range _).bddAbove h
  · simp only [norm_eq_sum (ENNReal.toReal_pos hp0 hp)]
    gcongr
    · exact Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _
    · exact h _

/-- Taking coordinate norms preserves the finite `Lᵖ` norm. -/
@[simp]
theorem norm_norm (x : PiLp p E) :
    ‖WithLp.toLp p (fun i ↦ ‖x i‖)‖ = ‖x‖ :=
  le_antisymm (norm_mono fun i ↦ by simp) (norm_mono fun i ↦ by simp)

end PiLp
