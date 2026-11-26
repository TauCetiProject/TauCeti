/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Examples.TwoState
import Mathlib.Tactic.NormNum

/-!
# Examples: worked values for two-state chains

Worked values of the closed forms of `TauCeti.Probability.twoStateChain`.

* With `a = 1/2` and `b = 1/4` the equilibrium law is `(1/3, 2/3)`, detailed balance reads
  `1/3 · 1/2 = 2/3 · 1/4`, the mean return time to `false` is `3 = 1 / π {false}`, and started at
  `false` the total variation distance to equilibrium is `(4/3) · 4⁻ⁿ`: `4/3, 1/3, 1/12, …`.
* The chain with `a = b = 1` always switches. Its equilibrium law is uniform, but started at
  `false` its distance to equilibrium is `1` at every time, so the aperiodicity hypothesis of
  `ProbabilityTheory.Kernel.Invariant.tendsto_tvDist_pow_comp` cannot be dropped. Two copies started
  at `false` and at `true` are at total variation distance `2` at every time: they never meet, and
  the coupling bound `2 · P(τ > n) = 2` is attained.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, Example 1.1.4 and §1.8.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti.Probability

namespace TauCeti.Examples.TwoStateChain

/-! ### The chain with `a = 1/2` and `b = 1/4` -/

/-- The switching probability `1/2`. -/
def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- The switching probability `1/4`. -/
def quarter : unitInterval := ⟨1 / 4, by norm_num, by norm_num⟩

/-- The value of `half`. -/
theorem coe_half : (half : ℝ) = 1 / 2 := (rfl)

/-- The value of `quarter`. -/
theorem coe_quarter : (quarter : ℝ) = 1 / 4 := (rfl)

-- The equilibrium law is `(1/3, 2/3)`.
example : (twoStateEquilibrium half quarter).real {false} = 1 / 3 ∧
    (twoStateEquilibrium half quarter).real {true} = 2 / 3 := by
  simp only [twoStateEquilibrium_real_false, twoStateEquilibrium_real_true, coe_half, coe_quarter]
  norm_num

-- Detailed balance: the flows `1/3 · 1/2` from `false` to `true` and `2/3 · 1/4` back are both
-- `1/6`, so the equilibrium law is reversible.
example : (twoStateEquilibrium half quarter).real {false} * half = 1 / 6 ∧
    (twoStateEquilibrium half quarter).real {true} * quarter = 1 / 6 ∧
    (twoStateChain half quarter).IsReversible (twoStateEquilibrium half quarter) := by
  refine ⟨?_, ?_, (twoStateChain_isReversible_iff half quarter _).mpr ?_⟩ <;>
  · simp only [twoStateEquilibrium_real_false, twoStateEquilibrium_real_true, coe_half,
      coe_quarter]
    norm_num

-- Kac's formula: the mean return time to `false` is `(1 - a) + a (1 + 1/b) = 3`.
example : (twoStateChain half quarter).meanReturnTime false = 3 := by
  rw [twoStateChain_meanReturnTime_false half quarter
    (fun h => by simpa [coe_quarter] using congrArg Subtype.val h), coe_half, coe_quarter]
  norm_num

-- Started at `false`, the distance to equilibrium is `(4/3) · 4⁻ⁿ`.
example (n : ℕ) :
    tvDist ((twoStateChain half quarter ^ n) false) (twoStateEquilibrium half quarter) =
      4 / 3 * (1 / 4) ^ n := by
  rw [tvDist_twoStateChain_pow_false_twoStateEquilibrium, coe_half, coe_quarter]
  norm_num

/-! ### The switching chain `a = b = 1` -/

-- Its equilibrium law is uniform.
example : (twoStateEquilibrium 1 1).real {true} = 1 / 2 := by
  simp only [twoStateEquilibrium_real_true, Set.Icc.coe_one]
  norm_num

-- Started at `false`, the distance to the uniform law is `1` at every time.
example (n : ℕ) : tvDist ((twoStateChain 1 1 ^ n) false) (twoStateEquilibrium 1 1) = 1 := by
  rw [tvDist_twoStateChain_pow_false_twoStateEquilibrium, Set.Icc.coe_one]
  norm_num

-- Started at `false` and at `true`, two copies stay at distance `2` at every time.
example (n : ℕ) : tvDist ((twoStateChain 1 1 ^ n) false) ((twoStateChain 1 1 ^ n) true) = 2 := by
  rw [← Measure.dirac_bind (twoStateChain 1 1 ^ n).measurable,
    ← Measure.dirac_bind (twoStateChain 1 1 ^ n).measurable (a := true),
    tvDist_twoStateChain_pow_comp 1 1 n (by simp), tvDist_dirac_left, Set.Icc.coe_one]
  simp

end TauCeti.Examples.TwoStateChain
