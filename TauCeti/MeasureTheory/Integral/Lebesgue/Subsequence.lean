/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Almost everywhere convergence along a subsequence

If the Lebesgue integrals of nonnegative functions `F n : α → ℝ≥0∞` tend to `0`, then along a
subsequence the functions themselves tend to `0` almost everywhere. Choose the subsequence with
integrals below `2⁻ʲ`: the sum `∑ⱼ F (φ j)` then has finite integral, so it is finite almost
everywhere, and its terms tend to `0` there.

## Main statements

* `TauCeti.exists_strictMono_ae_tendsto_zero_of_tendsto_lintegral`: a subsequence of functions
  whose integrals tend to `0` tends to `0` almost everywhere.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **A subsequence converging almost everywhere.** If `F n : α → ℝ≥0∞` are almost everywhere
measurable and `∫⁻ F n ∂μ → 0`, then along a subsequence `F (φ j) a → 0` for almost every `a`. -/
theorem exists_strictMono_ae_tendsto_zero_of_tendsto_lintegral {F : ℕ → α → ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) μ) (h : Tendsto (fun n ↦ ∫⁻ a, F n a ∂μ) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ a ∂μ, Tendsto (fun j ↦ F (φ j) a) atTop (𝓝 0) := by
  -- Along a subsequence with `∫⁻ F (φ j) < 2⁻ʲ`, the sum `∑ⱼ F (φ j) a` has finite integral.
  obtain ⟨φ, hφ, hlt⟩ := extraction_forall_of_eventually fun j ↦
    h.eventually (gt_mem_nhds (ENNReal.pow_pos (a := 2⁻¹) (by simp) j))
  refine ⟨φ, hφ, ?_⟩
  have hsum : ∫⁻ a, ∑' j, F (φ j) a ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun j ↦ hF (φ j)]
    exact ((ENNReal.tsum_le_tsum fun j ↦ (hlt j).le).trans_lt (by simp)).ne
  -- So the sum is finite almost everywhere, and its terms tend to `0` there.
  filter_upwards [ae_lt_top' (AEMeasurable.tsum fun j ↦ hF (φ j)) hsum] with a ha
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha.ne

end TauCeti
