/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import TauCeti.Combinatorics.Pigeonhole.Scales

/-!
# A power window avoiding a finite set

The additive pigeonhole on scales, applied to logarithms, selects a single interval
`[Y, Y²]` throughout which every exceptional value lies outside `(x ^ (1 / B), x]`.
Equivalently, for positive exceptional values `e`, no `log e` lies in `(log x / B, log x]`.
For instance, applying the lemma to the values `e ^ (1 / κ)` of finitely many positive `e`,
with `κ > 0`, gives that each such `e` satisfies `x ^ κ < e` or `e ≤ x ^ (κ / B)`.
-/

public section

open Real Set

namespace Finset

/-- Some window `[Y, Y²]` avoids the finite exceptional set `T` in the sense that every
`x` in the window separates each `e ∈ T` into `x < e` or `e ≤ x ^ (1 / B)`. -/
theorem exists_forall_mem_Icc_lt_or_le_rpow (T : Finset ℝ) {X B : ℝ} (hX : 1 ≤ X)
    (hB : 1 ≤ 2 * B) :
    ∃ Y ∈ Set.Icc (X ^ (1 / (2 ^ (T.card + 2) * B ^ T.card) : ℝ)) (X ^ (1 / 2 : ℝ)),
      ∀ x ∈ Set.Icc Y (Y ^ 2), ∀ e ∈ T, x < e ∨ e ≤ x ^ (1 / B) := by
  classical
  have hX₀ : 0 < X := zero_lt_one.trans_le hX
  have hB₀ : 0 < B := by linarith
  obtain ⟨y, hy, hgap⟩ := (T.image log).exists_mem_Icc_forall_two_mul_lt_or_mul_le hB
    (log_nonneg hX) card_image_le
  refine ⟨exp y, ?_, ?_⟩
  · simpa only [Set.mem_Icc, rpow_def_of_pos hX₀, mul_one_div, exp_le_exp] using hy
  · intro x hx e he
    have hx₀ : 0 < x := (exp_pos y).trans_le hx.1
    by_cases he₀ : 0 < e
    · rcases hgap (log e) (mem_image_of_mem log he) with h | h
      · left
        apply (log_lt_log_iff hx₀ he₀).mp
        have hx' := log_le_log hx₀ hx.2
        rw [log_pow, log_exp, Nat.cast_ofNat] at hx'
        exact hx'.trans_lt h
      · right
        apply (log_le_log_iff he₀ (rpow_pos_of_pos hx₀ _)).mp
        rw [log_rpow hx₀, one_div_mul_eq_div, le_div_iff₀ hB₀, mul_comm]
        exact h.trans (by simpa only [log_exp] using log_le_log (exp_pos y) hx.1)
    · exact Or.inr ((le_of_not_gt he₀).trans (rpow_pos_of_pos hx₀ _).le)

end Finset
