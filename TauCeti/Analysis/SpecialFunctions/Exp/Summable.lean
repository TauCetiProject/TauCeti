/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# A summable exponential series over the integers

The decay `e^(-2π (|m| - 1))` is summable over `m ∈ ℤ`, being a two-sided geometric series. It is
the summable majorant of the rows of lattice series in the coordinates of modular forms on
`1 ≤ Im z`, shared by the Eisenstein series of weights one and two.

## Main declarations

* `TauCeti.summable_exp_neg_two_pi_mul_abs_sub_one`: `∑_{m ∈ ℤ} e^(-2π (|m| - 1))` converges.
-/

public section

open Real

namespace TauCeti

/-- The decay `e^(-2π (|m| - 1))` is summable over `m ∈ ℤ`. -/
theorem summable_exp_neg_two_pi_mul_abs_sub_one :
    Summable fun m : ℤ ↦ Real.exp (-2 * π * (|(m : ℝ)| - 1)) := by
  have hg : Summable fun n : ℕ ↦ Real.exp (2 * π) * Real.exp (-2 * π) ^ n :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos]))).mul_left _
  have hexp (n : ℕ) : Real.exp (-2 * π * (|((n : ℤ) : ℝ)| - 1)) =
      Real.exp (2 * π) * Real.exp (-2 * π) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    rw [abs_of_nonneg (Nat.cast_nonneg n)]
    ring
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨hg.congr fun n ↦ (hexp n).symm, ?_⟩
  refine hg.congr fun n ↦ ?_
  rw [← hexp]
  push_cast
  rw [abs_neg]

end TauCeti
