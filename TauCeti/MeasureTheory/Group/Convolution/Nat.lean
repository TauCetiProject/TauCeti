/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Convolution masses on the natural numbers

Convolution on `ℕ` is a finite discrete convolution at every singleton. This formula
allows renewal equations on integer time to be solved recursively.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- The mass of a singleton under convolution on `ℕ` is a finite convolution sum. -/
theorem conv_apply_singleton_nat (μ ν : Measure ℕ) [SFinite ν] (n : ℕ) :
    (μ ∗ ν) {n} = ∑ j ∈ Finset.range (n + 1), μ {j} * ν {n - j} := by
  rw [conv, map_apply measurable_add (measurableSet_singleton n),
    prod_apply (by measurability), lintegral_countable']
  have hterm (j : ℕ) :
      ν (Prod.mk j ⁻¹' ((fun p : ℕ × ℕ ↦ p.1 + p.2) ⁻¹' {n})) =
        if j ≤ n then ν {n - j} else 0 := by
    split_ifs with hj
    · congr 1
      ext k
      simp only [mem_preimage, mem_singleton_iff]
      omega
    · have he : Prod.mk j ⁻¹' ((fun p : ℕ × ℕ ↦ p.1 + p.2) ⁻¹' {n}) = ∅ := by
        ext k
        simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
        omega
      simp [he]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun j hj ↦ by
    have : ¬ j ≤ n := by simpa using hj
    simp [this])]
  exact Finset.sum_congr rfl fun j hj ↦ by
    simp [Nat.le_of_lt_succ (Finset.mem_range.1 hj), mul_comm]

end MeasureTheory.Measure
