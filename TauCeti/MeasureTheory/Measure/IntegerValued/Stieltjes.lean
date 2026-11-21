/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.BorelSpace.Order
public import TauCeti.MeasureTheory.Measure.IntegerValued.Basic
public import TauCeti.MeasureTheory.Measure.Stieltjes
public import Mathlib.Topology.Order.Cadlag

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

Conversely, the natural-valued cumulative count `t ↦ ⌊μ (0,t]⌋` of a locally finite
integer-valued measure is a counting path: it starts at zero, is nondecreasing and
right-continuous, and at a positive time some earlier count is at most the mass of that time
below. In particular a simple measure has a count path with jumps of size at most one.

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
      simp only [mem_Iic, mem_singleton_iff, nonpos_iff_eq_zero]
    simpa only [hIic, hzero, Nat.cast_zero] using hcumulative 0
  · intro a b
    rw [f.measure_Ioc, hf, hf]
    by_cases hab : a ≤ b
    · rw [← Nat.cast_sub (hN hab)]
      simp
    · have hba : N b ≤ N a := hN (le_of_not_ge hab)
      simp [Nat.sub_eq_zero_of_le hba, ENNReal.ofReal_eq_zero, hba]

end TauCeti.Probability

namespace MeasureTheory.Measure

variable {μ : Measure ℝ≥0} [IsLocallyFiniteMeasure μ]

/-- The natural-valued cumulative count of a locally finite measure on the half-line is
nondecreasing. No integrality is needed. -/
theorem monotone_nat_count : Monotone fun t : ℝ≥0 => ⌊(μ (Ioc 0 t)).toNNReal⌋₊ :=
  fun _ _ hst => Nat.floor_mono <| ENNReal.toNNReal_mono measure_Ioc_lt_top.ne <|
    measure_mono <| Ioc_subset_Ioc_right hst

/-- For a locally finite integer-valued measure, the natural-valued count of a bounded
interval is its mass. -/
theorem IsIntegerValued.natCast_nat_count_Ioc (hμ : μ.IsIntegerValued) (a b : ℝ≥0) :
    (⌊(μ (Ioc a b)).toNNReal⌋₊ : ℝ≥0∞) = μ (Ioc a b) :=
  hμ.natCast_floor_toNNReal measurableSet_Ioc measure_Ioc_lt_top.ne

/-- The cumulative count of a locally finite integer-valued measure is right-continuous:
it is constant on a right neighbourhood of each time. -/
theorem IsIntegerValued.isRightContinuous_nat_count (hμ : μ.IsIntegerValued) :
    IsRightContinuous fun t : ℝ≥0 => ⌊(μ (Ioc 0 t)).toNNReal⌋₊ := by
  intro a
  have hIoc (r : ℝ≥0) : μ.restrict (Ioi 0) (Iic r) = μ (Ioc 0 r) := by
    rw [restrict_apply measurableSet_Iic, inter_comm, Ioi_inter_Iic]
  have hlim : Tendsto (fun r => μ (Ioc 0 r)) (𝓝[>] a) (𝓝 (μ (Ioc 0 a))) := by
    simpa only [hIoc] using tendsto_measure_Iic_nhdsGT (μ := μ.restrict (Ioi 0))
      ⟨a + 1, lt_add_one a, (hIoc _).trans_lt measure_Ioc_lt_top |>.ne⟩
  rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
  have hlt : μ (Ioc 0 a) < ⌊(μ (Ioc 0 a)).toNNReal⌋₊ + 1 := by
    rw [hμ.natCast_nat_count_Ioc]
    exact ENNReal.lt_add_right measure_Ioc_lt_top.ne one_ne_zero
  -- Masses just to the right of `a` are integers below the next integer, hence unchanged.
  filter_upwards [hlim (Iio_mem_nhds hlt), self_mem_nhdsWithin] with r hr har
  refine le_antisymm ?_ (monotone_nat_count (le_of_lt har))
  rw [mem_preimage, mem_Iio, ← hμ.natCast_nat_count_Ioc] at hr
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hr)

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
    rw [hμ.natCast_nat_count_Ioc, hμ.natCast_floor_toNNReal (measurableSet_singleton t) htop]
    exact hn
  rw [← hμ.natCast_nat_count_Ioc 0 t, ← hμ.natCast_nat_count_Ioc 0 (u n),
    ← hμ.natCast_nat_count_Ioc (u n) t] at hsplit
  have h1 : ⌊(μ (Ioc (u n) t)).toNNReal⌋₊ < ⌊(μ {t}).toNNReal⌋₊ + 1 := by exact_mod_cast hn'
  have h2 : ⌊(μ (Ioc 0 t)).toNNReal⌋₊ =
      ⌊(μ (Ioc 0 (u n))).toNNReal⌋₊ + ⌊(μ (Ioc (u n) t)).toNNReal⌋₊ := by
    exact_mod_cast hsplit
  omega

end MeasureTheory.Measure
