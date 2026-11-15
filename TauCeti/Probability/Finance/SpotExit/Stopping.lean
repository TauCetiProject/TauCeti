/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SpotExit.Basic
public import TauCeti.Probability.Process.HittingTime
public import TauCeti.Probability.Process.Stopping
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

Continuity is required on every path when asserting a stopping-time property. Almost-sure
continuity of a raw version is not enough; a continuous adapted version or a suitable
augmentation must be supplied before applying these results.

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

/-- The native stopped stages of the stock and its reciprocal are both between zero and
`n + 1`. Paths with immediate exit are discarded, so no bound or moment assumption on
the initial stock is needed, and the assertion includes `n = 0`. -/
theorem stoppedProcess_indicator_spotExitTime_mem_Icc (hS : Continuous (S · ω))
    (t : ℝ≥0) :
    stoppedProcess (fun u ↦ {ω | 0 < spotExitTime S n ω}.indicator (S u))
        (spotExitTime S n) t ω ∈ Icc 0 (n + 1 : ℝ) ∧
      stoppedProcess (fun u ↦ {ω | 0 < spotExitTime S n ω}.indicator (S⁻¹ u))
        (spotExitTime S n) t ω ∈ Icc 0 (n + 1 : ℝ) := by
  classical
  rw [stoppedProcess_indicator_comm, stoppedProcess_indicator_comm, stoppedProcess_inv]
  by_cases hpos : 0 < spotExitTime S n ω
  · have hstart : S 0 ω ∈ Ioo ((n + 1 : ℝ)⁻¹) (n + 1) := by
      rw [spotExitTime_def] at hpos
      simpa only [mem_compl_iff, not_not] using
        notMem_of_lt_hittingAfter hpos (le_refl (0 : ℝ≥0))
    have hb : stoppedProcess S (spotExitTime S n) t ω ∈
        Icc ((n + 1 : ℝ)⁻¹) (n + 1) := by
      apply stoppedProcess_mem (fun u hu ↦ ?_) t
      rw [spotExitTime_def] at hu
      exact hS.mem_Icc_of_le_hittingAfter_compl_Ioo bot_le (Ioo_subset_Icc_self hstart) hu
    have hN : (0 : ℝ) < n + 1 := by positivity
    have hval : 0 < stoppedProcess S (spotExitTime S n) t ω :=
      (inv_pos.mpr hN).trans_le hb.1
    simp only [Set.indicator_apply, mem_ofPred_eq, hpos, ↓reduceIte, Pi.inv_apply]
    exact ⟨⟨hval.le, hb.2⟩, ⟨(inv_pos.mpr hval).le,
      (inv_le_comm₀ hval hN).mpr hb.1⟩⟩
  · simp only [Set.indicator_apply, mem_ofPred_eq, hpos, ↓reduceIte, Pi.inv_apply,
      mem_Icc, le_refl, true_and]
    exact ⟨by positivity, by positivity⟩

end Continuous

namespace MeasureTheory.Adapted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {S : ℝ≥0 → Ω → ℝ}

/-- The spot exits of an everywhere-continuous adapted stock with almost surely strictly
positive paths form a localizing sequence on its original filtration. Neither usual
conditions, deterministic initial spot, nor initial moments are assumed. -/
theorem isLocalizingSequence_spotExitTime (hS : Adapted ℱ S)
    (hcont : ∀ ω, Continuous (S · ω)) (hpos : ∀ᵐ ω ∂P, ∀ t, 0 < S t ω) :
    IsLocalizingSequence ℱ (spotExitTime S) P where
  isStoppingTime n := by
    rw [spotExitTime_def]
    exact hS.isStoppingTime_hittingAfter_compl_of_isOpen hcont isOpen_Ioo 0
  tendsto_top := hpos.mono fun ω hω ↦ tendsto_spotExitTime (hcont ω) hω
  mono := ae_of_all _ (monotone_spotExitTime S)

end MeasureTheory.Adapted
