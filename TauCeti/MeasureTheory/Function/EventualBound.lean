/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Deterministic eventual bounds for almost everywhere small sequences

If real functions `Y n` are almost everywhere eventually below every positive constant, then a
single deterministic sequence `δ n → 0` eventually bounds them almost everywhere.

Truncation arguments for random matrices use this to replace a random truncation level by a
deterministic one, so that the truncated entries remain independent and identically distributed.

The measure only needs to be s-finite: an s-finite measure has the same null sets as the finite
measure `Measure.toFinite`.

## Main statements

* `MeasureTheory.exists_tendsto_zero_ae_eventually_le`: a deterministic null sequence eventually
  bounds functions that are almost everywhere eventually below every positive constant.

## Implementation notes

For each level `1 / (k + 1)`, continuity from above yields an index after which the level is
exceeded only on a set of measure at most `2⁻ᵏ`. The first Borel–Cantelli lemma then lets `δ n`
step down through these levels.
-/

public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : ℕ → Ω → ℝ}

/-- The finite-measure case of `exists_tendsto_zero_ae_eventually_le`. -/
private theorem exists_tendsto_zero_ae_eventually_le_of_isFiniteMeasure [IsFiniteMeasure μ]
    (hY : ∀ n, AEMeasurable (Y n) μ) (h : ∀ ε > 0, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, Y n ω ≤ ε) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, Y n ω ≤ δ n := by
  -- `B k N`: some `Y n` with `n ≥ N` exceeds the level `1 / (k + 1)`.
  set B : ℕ → ℕ → Set Ω := fun k N ↦ ⋃ n ≥ N, {ω | 1 / ((k : ℝ) + 1) < Y n ω} with hB
  have hsmall (k : ℕ) : ∃ N, μ (B k N) ≤ 2⁻¹ ^ k := by
    have hmeas (N : ℕ) : NullMeasurableSet (B k N) μ :=
      .biUnion (to_countable _) fun n _ ↦ nullMeasurableSet_lt aemeasurable_const (hY n)
    have hnull : μ (⋂ N, B k N) = 0 := by
      refine measure_mono_null (fun ω hω ↦ ?_)
        (ae_iff.1 (h (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat))
      simp only [hB, mem_iInter, mem_iUnion, mem_ofPred_eq, exists_prop] at hω
      simp only [mem_ofPred_eq, Filter.not_eventually, not_le, frequently_atTop]
      exact hω
    have hlim := tendsto_measure_iInter_atTop hmeas
      (fun N M hNM ω hω ↦ by
        simp only [hB, mem_iUnion, exists_prop] at hω ⊢
        obtain ⟨n, hn, hY⟩ := hω
        exact ⟨n, hNM.trans hn, hY⟩)
      ⟨0, measure_ne_top μ _⟩
    rw [hnull] at hlim
    exact (hlim.eventually (ge_mem_nhds (ENNReal.pow_pos (by norm_num) k))).exists
  choose N hN using hsmall
  -- `c n` is the largest `k ≤ n` whose index `N k` has been passed.
  set c : ℕ → ℕ := fun n ↦ Nat.findGreatest (fun k ↦ N k ≤ n) n
  have hcN {K n : ℕ} (hn : max (N K) K ≤ n) : K ≤ c n ∧ N (c n) ≤ n :=
    ⟨Nat.le_findGreatest (le_of_max_le_right hn) (le_of_max_le_left hn),
      Nat.findGreatest_spec (P := fun k ↦ N k ≤ n) (le_of_max_le_right hn)
        (le_of_max_le_left hn)⟩
  refine ⟨fun n ↦ 1 / ((c n : ℝ) + 1),
    tendsto_one_div_add_atTop_nhds_zero_nat.comp <|
      tendsto_atTop.2 fun K ↦ eventually_atTop.2 ⟨max (N K) K, fun n hn ↦ (hcN hn).1⟩, ?_⟩
  have hsum : ∑' k, μ (B k (N k)) ≠ ∞ :=
    ne_top_of_le_ne_top (by simp [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two])
      (tsum_le_tsum hN)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.1 hω
  refine eventually_atTop.2 ⟨max (N K) K, fun n hn ↦ ?_⟩
  obtain ⟨hKc, hNc⟩ := hcN hn
  have := hK (c n) hKc
  simp only [hB, mem_iUnion, mem_ofPred_eq, exists_prop, not_exists, not_and, not_lt] at this
  exact this n hNc

/-- If real functions `Y n` are almost everywhere eventually below every positive constant, then
some deterministic sequence `δ n → 0` almost everywhere eventually bounds `Y n`. The measure is
only required to be s-finite. -/
theorem exists_tendsto_zero_ae_eventually_le [SFinite μ] (hY : ∀ n, AEMeasurable (Y n) μ)
    (h : ∀ ε > 0, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, Y n ω ≤ ε) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, Y n ω ≤ δ n := by
  simp_rw [← ae_toFinite (μ := μ)] at h ⊢
  exact exists_tendsto_zero_ae_eventually_le_of_isFiniteMeasure
    (fun n ↦ (hY n).mono_ac (toFinite_absolutelyContinuous μ)) h

end MeasureTheory
