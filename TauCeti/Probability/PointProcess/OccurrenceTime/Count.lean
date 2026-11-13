/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.Reconstruction

/-!
# Counts at occurrence times

For a locally finite counting measure, at most `n` occurrences strictly precede
occurrence `n`. If its location has multiplicity at most one, the cumulative count
there is exactly `n + 1`, and the next occurrence is strictly later (possibly infinite).
Only simplicity at the selected location is required; earlier multiple points are allowed.

Consequently the next interarrival exceeds a given duration exactly when the
corresponding interval after the current occurrence is empty. This is the pathwise
link between waiting-time survival events and increments of a counting process.
Finite configurations, an occurrence at zero, and zero observation durations are included.
No value obtained by converting an infinite occurrence time to a finite time is used.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge
  University Press, 2018, Chapter 7, Theorem 7.2.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable {μ : Measure ℝ≥0} [IsLocallyFiniteMeasure μ] {n : ℕ}

/-- At most `n` occurrences strictly precede the finite occurrence with index `n`,
even if that occurrence has multiplicity greater than one. -/
theorem IsIntegerValued.apply_Iio_toNNReal_occurrenceTime_le (hμ : μ.IsIntegerValued)
    (hn : μ.occurrenceTime n ≠ ∞) :
    μ (Iio (μ.occurrenceTime n).toNNReal) ≤ n := by
  classical
  rw [congrArg (fun ν : Measure ℝ≥0 => ν (Iio (μ.occurrenceTime n).toNNReal))
    hμ.eq_occurrenceTimeMeasure, TauCeti.Probability.occurrenceTimeMeasure_apply]
  rw [tsum_eq_sum (s := Finset.range n)]
  · exact (Finset.sum_le_card_nsmul _ _ 1 (fun k _ => by split_ifs <;> simp)).trans
      (by simp)
  · intro k hk
    apply ite_eq_right
    rintro ⟨hkfin, hkt⟩
    have hnk := μ.monotone_occurrenceTime (Nat.le_of_not_gt (by simpa using hk))
    have hlt : μ.occurrenceTime k < μ.occurrenceTime n := by
      rw [← ENNReal.coe_toNNReal hkfin, ← ENNReal.coe_toNNReal hn, ENNReal.coe_lt_coe]
      exact hkt
    exact hlt.not_ge hnk

/-- At a finite occurrence of multiplicity at most one, the cumulative count is
exactly its index plus one. Other locations need not be simple. -/
theorem IsIntegerValued.apply_Iic_toNNReal_occurrenceTime (hμ : μ.IsIntegerValued)
    (hn : μ.occurrenceTime n ≠ ∞)
    (hs : μ {(μ.occurrenceTime n).toNNReal} ≤ 1) :
    μ (Iic (μ.occurrenceTime n).toNNReal) = n + 1 := by
  apply le_antisymm
  · calc
      μ (Iic (μ.occurrenceTime n).toNNReal) =
          μ (Iio (μ.occurrenceTime n).toNNReal ∪ {(μ.occurrenceTime n).toNNReal}) := by
            rw [Iio_union_right]
      _ ≤ μ (Iio (μ.occurrenceTime n).toNNReal) + μ {(μ.occurrenceTime n).toNNReal} :=
        measure_union_le _ _
      _ ≤ n + 1 := add_le_add (hμ.apply_Iio_toNNReal_occurrenceTime_le hn) hs
  · exact (μ.occurrenceTime_le_iff n _).1 (le_of_eq (ENNReal.coe_toNNReal hn).symm)

/-- A finite occurrence of multiplicity at most one is followed strictly later by
the next occurrence. The latter may be infinite for a finite configuration. -/
theorem IsIntegerValued.occurrenceTime_lt_succ (hμ : μ.IsIntegerValued)
    (hn : μ.occurrenceTime n ≠ ∞)
    (hs : μ {(μ.occurrenceTime n).toNNReal} ≤ 1) :
    μ.occurrenceTime n < μ.occurrenceTime (n + 1) := by
  apply lt_of_not_ge
  intro hle
  have hcount := (μ.occurrenceTime_le_iff (n + 1) _).1
    (hle.trans (le_of_eq (ENNReal.coe_toNNReal hn).symm))
  rw [hμ.apply_Iic_toNNReal_occurrenceTime hn hs] at hcount
  have : (n + 1 + 1 : ℝ≥0∞) > n + 1 := by exact_mod_cast Nat.lt_succ_self (n + 1)
  exact this.not_ge (by simpa only [Nat.cast_add, Nat.cast_one] using hcount)

/-- An observation window after a simple finite occurrence is empty exactly when
its right endpoint is strictly before the next occurrence. The right endpoint is
included, so an occurrence exactly there makes the window nonempty. -/
theorem IsIntegerValued.apply_Ioc_toNNReal_occurrenceTime_eq_zero_iff
    (hμ : μ.IsIntegerValued) (hn : μ.occurrenceTime n ≠ ∞)
    (hs : μ {(μ.occurrenceTime n).toNNReal} ≤ 1) {b : ℝ≥0}
    (hb : (μ.occurrenceTime n).toNNReal ≤ b) :
    μ (Ioc (μ.occurrenceTime n).toNNReal b) = 0 ↔
      (b : ℝ≥0∞) < μ.occurrenceTime (n + 1) := by
  have hsplit : μ (Iic b) = n + 1 + μ (Ioc (μ.occurrenceTime n).toNNReal b) := by
    rw [← Iic_union_Ioc_eq_Iic hb, measure_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      hμ.apply_Iic_toNNReal_occurrenceTime hn hs]
  have hnext : (b : ℝ≥0∞) < μ.occurrenceTime (n + 1) ↔ μ (Iic b) < n + 1 + 1 := by
    simp only [lt_iff_not_ge, μ.occurrenceTime_le_iff, Nat.cast_add, Nat.cast_one]
  rw [hnext]
  constructor
  · intro hzero
    rw [hsplit, hzero, add_zero]
    exact_mod_cast Nat.lt_succ_self (n + 1)
  · intro hlt
    obtain ⟨k, hk⟩ := hμ.exists_eq_natCast measurableSet_Iic (measure_Iic_lt_top (μ := μ))
    have hle : k ≤ n + 1 := by
      rw [hk] at hlt
      exact Nat.le_of_lt_succ (by exact_mod_cast hlt)
    have hmass : μ (Iic b) = n + 1 := le_antisymm
      (by rw [hk]; exact_mod_cast hle) (by rw [hsplit]; exact le_add_right le_rfl)
    rw [hmass] at hsplit
    exact (ENNReal.add_right_inj (by simp : (n : ℝ≥0∞) + 1 ≠ ∞)).1
      (by simpa only [add_zero] using hsplit.symm)

/-- For two finite consecutive occurrences, the interarrival exceeds `s` exactly
when there is no occurrence in the closed-right window of duration `s` after the
first. Simplicity is needed only at the first occurrence. -/
theorem IsIntegerValued.lt_toNNReal_occurrenceTime_sub_iff (hμ : μ.IsIntegerValued)
    (hn : μ.occurrenceTime n ≠ ∞) (hnext : μ.occurrenceTime (n + 1) ≠ ∞)
    (hs : μ {(μ.occurrenceTime n).toNNReal} ≤ 1) (s : ℝ≥0) :
    s < (μ.occurrenceTime (n + 1)).toNNReal - (μ.occurrenceTime n).toNNReal ↔
      μ (Ioc (μ.occurrenceTime n).toNNReal ((μ.occurrenceTime n).toNNReal + s)) = 0 := by
  rw [hμ.apply_Ioc_toNNReal_occurrenceTime_eq_zero_iff hn hs (le_add_of_nonneg_right s.2)]
  rw [← ENNReal.coe_toNNReal hnext, ENNReal.coe_lt_coe]
  exact lt_tsub_iff_left

end MeasureTheory.Measure
