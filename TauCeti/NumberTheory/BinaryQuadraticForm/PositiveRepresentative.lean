/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Content
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positive-leading representatives of indefinite binary forms

An integral binary form of positive discriminant represents a positive integer on a
primitive vector. Completing that vector to an oriented basis gives a properly equivalent
form with positive leading coefficient. Primitivity and discriminant are preserved by the
existing special-linear action. This applies to both square and nonsquare discriminants.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7 and the narrow analogue.
-/

public section

open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-- An indefinite integral form represents a positive integer on a primitive vector. -/
theorem exists_isCoprime_eval_pos (f : BinaryQuadraticForm ℤ) (hD : 0 < f.discrim) :
    ∃ x y : ℤ, IsCoprime x y ∧ 0 < f.eval x y := by
  by_cases ha : 0 < f.a
  · exact ⟨1, 0, isCoprime_one_left, by simpa using ha⟩
  by_cases ha₀ : f.a = 0
  · have hb : f.b ≠ 0 := by
      intro hb
      simp [discrim_def, _root_.discrim, ha₀, hb] at hD
    by_cases hc : 0 < f.c
    · exact ⟨0, 1, isCoprime_one_right, by simpa using hc⟩
    rcases lt_or_gt_of_ne hb with hb | hb
    · refine ⟨f.c - 1, 1, isCoprime_one_right, ?_⟩
      rw [eval_def, ha₀]
      have hb' : f.b ≤ -1 := by omega
      have hc' : f.c ≤ 0 := by omega
      nlinarith
    · refine ⟨1 - f.c, 1, isCoprime_one_right, ?_⟩
      rw [eval_def, ha₀]
      have hb' : 1 ≤ f.b := by omega
      have hc' : f.c ≤ 0 := by omega
      nlinarith
  have ha' : f.a < 0 := by omega
  have hval : 0 < f.eval (-f.b) (2 * f.a) := by
    have hmul : f.eval (-f.b) (2 * f.a) = -f.a * f.discrim := by
      simp only [eval_def, discrim_def, _root_.discrim]
      ring
    rw [hmul]
    exact mul_pos (neg_pos.mpr ha') hD
  obtain ⟨x, y, hxy, _, _, hscale⟩ :=
    exists_isCoprime_eval_eq_gcd_sq_mul f (-f.b) (2 * f.a)
      (Or.inr (mul_ne_zero (by decide) ha₀))
  refine ⟨x, y, hxy, ?_⟩
  rw [hscale] at hval
  exact pos_of_mul_pos_right hval (sq_nonneg _)

/-- Every indefinite integral binary form has a proper representative with positive leading term. -/
theorem exists_smul_a_pos (f : BinaryQuadraticForm ℤ) (hD : 0 < f.discrim) :
    ∃ γ : SL(2, ℤ), 0 < (γ • f).a := by
  obtain ⟨x, y, hxy, hval⟩ := exists_isCoprime_eval_pos f hD
  obtain ⟨γ, hγ⟩ := exists_smul_a_eq_eval f hxy
  exact ⟨γ, hγ ▸ hval⟩

end TauCeti.BinaryQuadraticForm
