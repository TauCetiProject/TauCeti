/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.BorelSpace.Order
public import TauCeti.MeasureTheory.Measure.IntegerValued.Basic
public import TauCeti.MeasureTheory.Measure.Stieltjes

/-!
# Counting measures from Stieltjes functions

A nondecreasing right-continuous natural-valued path on the half-line determines a
locally finite integer-valued measure. Its mass on `(a,b]` is the increment of the path;
its mass at zero is zero. Thus a path starting at zero is exactly the cumulative count
of the resulting measure, with repeated occurrences represented by jumps larger than one.

The construction uses Mathlib's `StieltjesFunction.measure`, rather than choosing or
ordering jump times. Integrality follows first on bounded windows from the generating
π-system of initial intervals, then globally by a countable cover. No bound on the total
number of occurrences is imposed.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 2 and 7, for counting measures and their temporal count paths.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StieltjesFunction

/-- A Stieltjes function on the half-line with natural-valued increments from zero defines an
integer-valued measure. Its initial value is arbitrary: the measure records increments and has
no atom at zero. -/
theorem isIntegerValued_measure (f : StieltjesFunction ℝ≥0)
    (hf : ∀ t, ∃ n : ℕ, f t - f 0 = n) : f.measure.IsIntegerValued := by
  have hmass (t : ℝ≥0) : ∃ n : ℕ, f.measure (Iic t) = n := by
    obtain ⟨n, hn⟩ := hf t
    exact ⟨n, by simp [hn]⟩
  apply Measure.isIntegerValued_of_restrict
    (s := fun n : ℕ => Iic (n : ℝ≥0)) (fun _ => measurableSet_Iic)
  · ext t
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact exists_nat_ge t
  · intro n
    let μ := f.measure.restrict (Iic (n : ℝ≥0))
    apply Measure.isIntegerValued_of_isPiSystem (μ := μ)
      (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic (α := ℝ≥0))) isPiSystem_Iic
    · rintro _ ⟨t, rfl⟩
      simpa [μ, Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic] using hmass (min t n)
    · simpa [μ] using hmass n

end StieltjesFunction

namespace TauCeti.Probability

/-- Every nondecreasing right-continuous natural-valued path starting at zero is the
cumulative count of a locally finite integer-valued measure on the half-line.
The intervals include their right endpoint and there is no occurrence at zero. The
cumulative counts uniquely determine the measure by `Measure.ext_of_Iic'`, even when its total
mass is infinite. -/
theorem exists_measure_of_countingPath (N : ℝ≥0 → ℕ) (hN : Monotone N)
    (hcont : ∀ t, ContinuousWithinAt N (Ici t) t) (hzero : N 0 = 0) :
    ∃ μ : Measure ℝ≥0, IsLocallyFiniteMeasure μ ∧ μ.IsIntegerValued ∧
      μ {0} = 0 ∧ (∀ t, μ (Iic t) = N t) ∧
      ∀ a b, μ (Ioc a b) = (N b - N a : ℕ) := by
  let f : StieltjesFunction ℝ≥0 :=
    { toFun := fun t => (N t : ℝ)
      mono' := fun _ _ h => Nat.cast_le.mpr (hN h)
      right_continuous' := fun t =>
        (continuous_of_discreteTopology (f := fun n : ℕ => (n : ℝ))).continuousAt
          |>.comp_continuousWithinAt (hcont t) }
  have hf (t : ℝ≥0) : f t = (N t : ℝ) := rfl
  have hcumulative (t : ℝ≥0) : f.measure (Iic t) = N t := by
    simp [hf, hzero]
  refine ⟨f.measure, inferInstance,
    f.isIntegerValued_measure (fun t => ⟨N t, by simp [hf, hzero]⟩), ?_, hcumulative, ?_⟩
  · have hIic : Iic (0 : ℝ≥0) = {0} := by
      ext t
      simp only [mem_Iic, mem_singleton_iff, le_zero_iff]
    simpa only [hIic, hzero, Nat.cast_zero] using hcumulative 0
  · intro a b
    rw [f.measure_Ioc, hf, hf]
    by_cases hab : a ≤ b
    · rw [← Nat.cast_sub (hN hab)]
      simp
    · have hba : N b ≤ N a := hN (le_of_not_ge hab)
      simp [Nat.sub_eq_zero_of_le hba, ENNReal.ofReal_eq_zero, hba]

end TauCeti.Probability
