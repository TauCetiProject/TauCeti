/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SpotExit.Basic
public import TauCeti.Probability.Process.HittingTime
public import Mathlib.Probability.Process.LocalProperty

/-!
# Spot exits as bounded localizers

The exits from `(1 / (n + 1), n + 1)` are stopping times for an everywhere-continuous
adapted stock process. If the stock is almost surely strictly positive, these exits form
a native `ProbabilityTheory.IsLocalizingSequence` on the original filtration.

Before and at exit, the stock stays in the closed spot interval provided it starts there.
For the native stopped stages, which discard paths whose exit is at zero, both the stock
and its reciprocal are bounded by `n + 1`. This remains true for an unbounded random
initial stock value, without an initial moment assumption. It supplies bounded-spot
localization for Itô pricing arguments; it does not assert an Itô formula or replication.

The stopping-time results apply on arbitrary raw filtrations and assume continuity on
every path. For an almost-surely continuous stock, use an everywhere-continuous adapted
version instead, augmenting the filtration by null sets first if needed to preserve
adaptation when modifying the exceptional paths.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §6.4.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology TauCeti.Probability
open scoped NNReal ENNReal

namespace Continuous

variable {Ω : Type*} {S : ℝ≥0 → Ω → ℝ} {ω : Ω} {n : ℕ}

/-- A continuous stock path has positive exit time exactly when its initial spot is
strictly inside the spot domain. -/
theorem spotExitTime_pos_iff (hS : Continuous (S · ω)) :
    0 < spotExitTime S n ω ↔ S 0 ω ∈ Ioo ((n + 1 : ℝ)⁻¹) (n + 1) := by
  rw [spotExitTime_def, lt_iff_not_ge, ← WithTop.coe_zero,
    isOpen_Ioo.isClosed_compl.hittingAfter_le_iff hS]
  simp

/-- A continuous stock path starting in the closed spot interval stays there up to and
including its exit from the open spot domain. -/
theorem mem_Icc_of_le_spotExitTime (hS : Continuous (S · ω))
    (hstart : S 0 ω ∈ Icc ((n + 1 : ℝ)⁻¹) (n + 1)) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ spotExitTime S n ω) :
    S t ω ∈ Icc ((n + 1 : ℝ)⁻¹) (n + 1) := by
  rw [spotExitTime_def] at ht
  exact hS.mem_Icc_of_le_hittingAfter_compl_Ioo bot_le hstart ht

/-- Stopping a continuous stock path at its spot exit keeps it in the closed spot
interval for all times, provided it starts there. -/
theorem stoppedProcess_spotExitTime_mem_Icc (hS : Continuous (S · ω))
    (hstart : S 0 ω ∈ Icc ((n + 1 : ℝ)⁻¹) (n + 1)) (t : ℝ≥0) :
    stoppedProcess S (spotExitTime S n) t ω ∈ Icc ((n + 1 : ℝ)⁻¹) (n + 1) := by
  rw [spotExitTime_def]
  exact hS.stoppedProcess_hittingAfter_compl_Ioo_mem_Icc bot_le hstart

/-- The native stopped stage of the stock stays between zero and `n + 1`.
Immediate-exit paths contribute zero, so there is no initial-spot bound. -/
theorem stoppedProcess_indicator_spotExitTime_mem_Icc (hS : Continuous (S · ω))
    (t : ℝ≥0) :
    stoppedProcess (fun u ↦ {ω | 0 < spotExitTime S n ω}.indicator (S u))
        (spotExitTime S n) t ω ∈ Icc 0 (n + 1 : ℝ) := by
  classical
  rw [stoppedProcess_indicator_comm]
  by_cases hpos : 0 < spotExitTime S n ω
  · rw [indicator_of_mem hpos]
    have hb := hS.stoppedProcess_spotExitTime_mem_Icc
      (Ioo_subset_Icc_self (hS.spotExitTime_pos_iff.mp hpos)) t
    exact ⟨(by positivity : 0 ≤ (n + 1 : ℝ)⁻¹).trans hb.1, hb.2⟩
  · rw [indicator_of_notMem hpos]
    exact ⟨le_rfl, by positivity⟩

/-- The native stopped stage of the reciprocal stock stays between zero and `n + 1`.
Immediate-exit paths contribute zero, including all paths at index zero. -/
theorem stoppedProcess_indicator_inv_spotExitTime_mem_Icc (hS : Continuous (S · ω))
    (t : ℝ≥0) :
    stoppedProcess (fun u ↦ {ω | 0 < spotExitTime S n ω}.indicator (S⁻¹ u))
        (spotExitTime S n) t ω ∈ Icc 0 (n + 1 : ℝ) := by
  classical
  rw [stoppedProcess_indicator_comm, stoppedProcess_inv]
  by_cases hpos : 0 < spotExitTime S n ω
  · rw [indicator_of_mem hpos, Pi.inv_apply]
    have hb := hS.stoppedProcess_spotExitTime_mem_Icc
      (Ioo_subset_Icc_self (hS.spotExitTime_pos_iff.mp hpos)) t
    have hN : (0 : ℝ) < n + 1 := by positivity
    have hval := (inv_pos.mpr hN).trans_le hb.1
    exact ⟨(inv_pos.mpr hval).le, (inv_le_comm₀ hval hN).mpr hb.1⟩
  · rw [indicator_of_notMem hpos]
    exact ⟨le_rfl, by positivity⟩

end Continuous

namespace MeasureTheory.Adapted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {S : ℝ≥0 → Ω → ℝ}

/-- Each spot exit of an everywhere-continuous adapted stock is a stopping time on its
original filtration, without assuming positivity of the stock. -/
theorem isStoppingTime_spotExitTime (hS : Adapted ℱ S)
    (hcont : ∀ ω, Continuous (S · ω)) (n : ℕ) : IsStoppingTime ℱ (spotExitTime S n) := by
  rw [spotExitTime_def]
  exact hS.isStoppingTime_hittingAfter_compl_of_isOpen hcont isOpen_Ioo 0

/-- The spot exits of an everywhere-continuous adapted stock with almost surely strictly
positive paths form a localizing sequence on its original filtration. Neither usual
conditions, deterministic initial spot, nor initial moments are assumed. -/
theorem isLocalizingSequence_spotExitTime (hS : Adapted ℱ S)
    (hcont : ∀ ω, Continuous (S · ω)) (hpos : ∀ᵐ ω ∂P, ∀ t, 0 < S t ω) :
    IsLocalizingSequence ℱ (spotExitTime S) P where
  isStoppingTime := hS.isStoppingTime_spotExitTime hcont
  tendsto_top := hpos.mono fun ω hω ↦ tendsto_spotExitTime (hcont ω) hω
  mono := ae_of_all _ (monotone_spotExitTime S)

end MeasureTheory.Adapted
