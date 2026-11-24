/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.Encard

/-!
# Summable integer-level tail measures

Integrability bounds the sum of the measures of strict superlevel sets at positive
integer thresholds. This gives a summable sequence for Borel–Cantelli arguments.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The measures of the strict superlevel sets at positive integer thresholds of an
integrable real function have finite sum, even on an infinite measure space. -/
theorem Integrable.tsum_measure_mem_Ioi_nat_succ_lt_top
    {μ : Measure α} {g : α → ℝ} (hint : Integrable g μ) :
    (∑' i : ℕ, μ {x | g x ∈ Ioi ((i + 1 : ℕ) : ℝ)}) < ∞ := by
  let f := hint.aemeasurable.mk g
  calc
    _ = ∑' i : ℕ, μ {x | ((i + 1 : ℕ) : ℝ) < f x} := by
      refine tsum_congr fun i ↦ measure_congr ?_
      filter_upwards [hint.aemeasurable.ae_eq_mk] with x hx
      have hx' : g x = f x := hx
      simp only [mem_Ioi, hx']
    _ = ∫⁻ x, ({i : ℕ | ((i + 1 : ℕ) : ℝ) < f x}.encard : ℝ≥0∞) ∂μ :=
      (lintegral_encard_setOf_eq_tsum μ fun _ ↦
        measurableSet_lt measurable_const hint.aemeasurable.measurable_mk).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hint.aemeasurable.ae_eq_mk] with x hx
      have hcount : {i : ℕ | ((i + 1 : ℕ) : ℝ) < f x}.encard ≤ (⌊‖g x‖⌋₊ : ℕ∞) := by
        rw [← Set.Nat.encard_range]
        exact Set.encard_mono fun i (hi : ((i + 1 : ℕ) : ℝ) < f x) ↦
          Nat.lt_of_succ_le (Nat.le_floor (hi.le.trans (hx ▸ Real.le_norm_self (g x))))
      exact (ENat.toENNReal_mono hcount).trans (by
        rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (Nat.floor_le (norm_nonneg _)))
    _ < ∞ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint.norm (.of_forall fun _ ↦ norm_nonneg _)]
      exact ENNReal.ofReal_lt_top

end MeasureTheory
