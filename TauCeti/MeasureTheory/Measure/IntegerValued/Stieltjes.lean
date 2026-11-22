/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.IntegerValued.Basic
public import TauCeti.MeasureTheory.Measure.Stieltjes

/-!
# Integer-valued Stieltjes measures and left-jump bounds

A Stieltjes function on the half-line with natural-valued increments from zero defines an
integer-valued measure (`StieltjesFunction.isIntegerValued_measure`).

For a locally finite integer-valued measure on the half-line, at any positive time some earlier
natural-valued cumulative count `⌊μ (0, s]⌋` is at most `⌊μ {t}⌋` below `⌊μ (0, t]⌋`
(`MeasureTheory.Measure.IsIntegerValued.exists_nat_count_le_add_floor`).

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
    (hf : ∀ t, ∃ n : ℕ, f t - f 0 = n) : f.measure.IsIntegerValued :=
  Measure.isIntegerValued_of_Iic fun t => by
    obtain ⟨n, hn⟩ := hf t
    exact ⟨n, by simp [hn]⟩

end StieltjesFunction

namespace MeasureTheory.Measure

variable {μ : Measure ℝ≥0} [IsLocallyFiniteMeasure μ]

/-- At a positive time, the cumulative count of a locally finite integer-valued measure jumps
from the left by at most the mass of that time. The bound is stated without left limits: some
earlier count is at most that mass below. -/
theorem IsIntegerValued.exists_nat_count_le_add_floor (hμ : μ.IsIntegerValued) {t : ℝ≥0}
    (ht : 0 < t) :
    ∃ s < t, ⌊(μ (Ioc 0 t)).toNNReal⌋₊ ≤ ⌊(μ (Ioc 0 s)).toNNReal⌋₊ + ⌊(μ {t}).toNNReal⌋₊ := by
  obtain ⟨u, hu, hut, hlim⟩ := exists_seq_strictMono_tendsto' ht
  have hinter : ⋂ n, Ioc (u n) t = {t} := by
    ext x
    simp only [mem_iInter, mem_Ioc, mem_singleton_iff]
    refine ⟨fun h => le_antisymm (h 0).2 (le_of_tendsto' hlim fun n => (h n).1.le), ?_⟩
    rintro rfl n
    exact ⟨(hut n).2, le_rfl⟩
  have htop : μ {t} ≠ ∞ :=
    ne_top_of_le_ne_top measure_Ioc_lt_top.ne (measure_mono (singleton_subset_iff.2 ⟨ht, le_rfl⟩))
  -- The masses of `(u n, t]` decrease to the mass of `{t}`, which is below its successor.
  have hmass := tendsto_measure_iInter_atTop (μ := μ) (s := fun n => Ioc (u n) t)
    (fun _ => measurableSet_Ioc.nullMeasurableSet)
    (fun _ _ hmn => Ioc_subset_Ioc_left (hu.monotone hmn)) ⟨0, measure_Ioc_lt_top.ne⟩
  rw [hinter] at hmass
  obtain ⟨n, hn⟩ :=
    (hmass.eventually (Iio_mem_nhds (ENNReal.lt_add_right htop one_ne_zero))).exists
  refine ⟨u n, (hut n).2, ?_⟩
  have hsplit : μ (Ioc 0 t) = μ (Ioc 0 (u n)) + μ (Ioc (u n) t) := by
    rw [← measure_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Ioc_union_Ioc_eq_Ioc (hut n).1.le (hut n).2.le]
  have hn' : (⌊(μ (Ioc (u n) t)).toNNReal⌋₊ : ℝ≥0∞) < ⌊(μ {t}).toNNReal⌋₊ + 1 := by
    rw [hμ.natCast_natFloor_Ioc, hμ.natCast_natFloor_apply htop.lt_top]
    exact hn
  rw [← hμ.natCast_natFloor_Ioc 0 t, ← hμ.natCast_natFloor_Ioc 0 (u n),
    ← hμ.natCast_natFloor_Ioc (u n) t] at hsplit
  have h1 : ⌊(μ (Ioc (u n) t)).toNNReal⌋₊ < ⌊(μ {t}).toNNReal⌋₊ + 1 := by exact_mod_cast hn'
  have h2 : ⌊(μ (Ioc 0 t)).toNNReal⌋₊ =
      ⌊(μ (Ioc 0 (u n))).toNNReal⌋₊ + ⌊(μ (Ioc (u n) t)).toNNReal⌋₊ := by
    exact_mod_cast hsplit
  omega

end MeasureTheory.Measure
