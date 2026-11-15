/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Linear asymptotics of monotone functions

For a monotone real-valued function on the nonnegative half-line, convergence of the
ratio to time along the natural numbers implies convergence along all times. The
integer floor and its successor bracket each observation time. This allows laws of
large numbers for nondecreasing processes to be transferred through countably many
coordinates, without imposing continuity of their paths. For a monotone natural-valued
sequence, the average of its successive differences has the same limit as its ratio
to the index, regardless of its initial value.
-/

public section

open Filter Topology
open scoped NNReal

namespace Monotone

/-- The average of the successive differences of a monotone natural-valued sequence
converges to the same limit as its ratio to the index, with no restriction on its initial value. -/
theorem tendsto_sum_range_sub_div_iff {f : ℕ → ℕ} (hf : Monotone f) {a : ℝ} :
    Tendsto (fun n : ℕ ↦ ((∑ i ∈ Finset.range n, (f (i + 1) - f i) : ℕ) : ℝ) / n)
      atTop (𝓝 a) ↔ Tendsto (fun n : ℕ ↦ (f n : ℝ) / n) atTop (𝓝 a) := by
  have htel (n : ℕ) :
      ((∑ i ∈ Finset.range n, (f (i + 1) - f i) : ℕ) : ℝ) / n =
        (f n : ℝ) / n - (f 0 : ℝ) / n := by
    rw [Finset.sum_range_tsub hf, Nat.cast_sub (hf (Nat.zero_le n)), sub_div]
  simp_rw [htel]
  have hzero := tendsto_const_div_atTop_nhds_zero_nat (f 0 : ℝ)
  constructor
  · intro h
    simpa only [sub_add_cancel, add_zero] using h.add hzero
  · intro h
    simpa only [sub_zero] using h.sub hzero

/-- A monotone function with linear asymptotics at integer times has the same asymptotics
along the entire nonnegative real half-line. No sign assumption on the function is needed. -/
theorem tendsto_div_of_tendsto_natCast {f : ℝ≥0 → ℝ} (hf : Monotone f) {r : ℝ}
    (h : Tendsto (fun n : ℕ ↦ f n / n) atTop (𝓝 r)) :
    Tendsto (fun t : ℝ≥0 ↦ f t / t) atTop (𝓝 r) := by
  have hfloor : Tendsto (fun t : ℝ≥0 ↦ ⌊(t : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have hsucc : Tendsto (fun t : ℝ≥0 ↦ ⌊(t : ℝ)⌋₊ + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ ↦ Nat.le_succ _) hfloor
  have hratio : Tendsto (fun t : ℝ≥0 ↦ (⌊(t : ℝ)⌋₊ : ℝ) / t) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have hratio' : Tendsto (fun t : ℝ≥0 ↦ ((⌊(t : ℝ)⌋₊ + 1 : ℕ) : ℝ) / t)
      atTop (𝓝 1) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero, id_eq] using
      hratio.add ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        (NNReal.tendsto_coe_atTop.2 tendsto_id))
  have hlower : Tendsto (fun t : ℝ≥0 ↦ f (⌊(t : ℝ)⌋₊ : ℕ) / t) atTop (𝓝 r) := by
    have hp := (h.comp hfloor).mul hratio
    simp only [mul_one] at hp
    apply hp.congr'
    filter_upwards [hfloor.eventually (eventually_gt_atTop 0)] with t ht
    exact div_mul_div_cancel₀ (Nat.cast_ne_zero.mpr ht.ne')
  have hupper : Tendsto (fun t : ℝ≥0 ↦ f (⌊(t : ℝ)⌋₊ + 1 : ℕ) / t)
      atTop (𝓝 r) := by
    have hp := (h.comp hsucc).mul hratio'
    simp only [mul_one] at hp
    apply hp.congr
    intro t
    exact div_mul_div_cancel₀ (by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · exact Eventually.of_forall fun t ↦ div_le_div_of_nonneg_right
      (hf (by exact_mod_cast Nat.floor_le t.coe_nonneg)) t.coe_nonneg
  · exact Eventually.of_forall fun t ↦ div_le_div_of_nonneg_right
      (hf (by exact_mod_cast (Nat.lt_floor_add_one (t : ℝ)).le)) t.coe_nonneg

end Monotone
