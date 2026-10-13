/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: the Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Field

/-!
# Shifting finite log-sum-exp expressions

Subtracting a constant before exponentiating and adding it back after taking the logarithm
preserves log-sum-exp on a nonempty finite set. Choosing the maximum makes every exponential
at most one and their sum lie between one and the cardinality. These exact real identities
underlie max-shift stabilization of log-domain algorithms; they assert no floating-point
error bounds.
-/

public section

open Real

namespace Finset

variable {ι : Type*}

/-- Log-sum-exp is unchanged by subtracting a common shift inside the exponentials and
adding it back outside the logarithm. The nonempty hypothesis excludes `log 0`. -/
theorem log_sum_exp_eq_add_log_sum_exp_sub (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (c : ℝ) :
    log (∑ i ∈ s, exp (f i)) = c + log (∑ i ∈ s, exp (f i - c)) := by
  have hpos : 0 < ∑ i ∈ s, exp (f i) := sum_pos (fun i _ ↦ exp_pos (f i)) hs
  simp_rw [exp_sub, ← sum_div]
  rw [log_div hpos.ne' (exp_ne_zero c), log_exp, add_sub_cancel]

/-- Subtracting the maximum makes each exponential at most one. -/
theorem exp_sub_sup'_le_one (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ)
    {i : ι} (hi : i ∈ s) : exp (f i - s.sup' hs f) ≤ 1 := by
  exact exp_le_one_iff.mpr (sub_nonpos.mpr (le_sup' f hi))

/-- The sum of exponentials shifted by their maximum is at most the number of terms. -/
theorem sum_exp_sub_sup'_le_card (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) :
    ∑ i ∈ s, exp (f i - s.sup' hs f) ≤ s.card := by
  simpa using sum_le_sum (fun i hi ↦ s.exp_sub_sup'_le_one hs f hi)

/-- The sum of exponentials shifted by their maximum is at least one: a maximizing term
has exponential one. -/
theorem one_le_sum_exp_sub_sup' (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) :
    1 ≤ ∑ i ∈ s, exp (f i - s.sup' hs f) := by
  obtain ⟨i, hi, hmax⟩ := s.exists_mem_eq_sup' hs f
  calc
    1 = exp (f i - s.sup' hs f) := by rw [hmax, sub_self, exp_zero]
    _ ≤ ∑ j ∈ s, exp (f j - s.sup' hs f) :=
      single_le_sum (fun j _ ↦ exp_nonneg (f j - s.sup' hs f)) hi

end Finset
