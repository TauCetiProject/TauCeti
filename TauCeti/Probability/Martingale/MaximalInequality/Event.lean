/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.MaximalInequality.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IsLUB

/-!
# Closed-level event-refined maximal inequality

For a nonnegative submartingale, Doob's maximal inequality retains the crossing event in the
terminal expectation. This refinement, unlike the weak bound by the whole terminal expectation,
can be integrated over the threshold to obtain strong maximal estimates for stochastic-integral
approximation.

We extend the strict-crossing refinement from `MaximalInequality.Basic` to the closed event
that the running supremum is at least the threshold. No usual-filtration assumption is needed.
Uncountable crossing events are interpreted using outer measure and restricted integrals;
right continuity identifies them almost everywhere with countable measurable crossing events.
The finite-set input in `MaximalInequality.Basic` uses Mathlib's `maximal_ineq` without dropping
its terminal event indicator.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Theorem 1.3.8.
-/

public section
noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace MeasureTheory.Submartingale

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [LinearOrder ι]
  {ℱ : Filtration ι m0} {f : ι → Ω → ℝ} [IsFiniteMeasure μ]

/-- **Closed-level event-refined Doob inequality.** The running supremum is taken in `ℝ≥0∞`,
so no pathwise boundedness assumption or convention for an unattained real supremum is needed.
The terminal expectation retains exactly the event that this supremum is at least `ε`. -/
theorem mul_measure_le_iSup_le_setIntegral
    [TopologicalSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (ε : ℝ≥0) :
    ε * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
        f T ω ∂μ) := by
  by_cases hε : ε = 0
  · simp [hε]
  obtain ⟨δ, hδmono, hδmem, hδlim⟩ := exists_seq_strictMono_tendsto' (pos_iff_ne_zero.2 hε)
  let Y : Ω → ℝ≥0∞ := fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)
  let A : ℕ → Set Ω := fun n ↦ {ω | (δ n : ℝ≥0∞) < Y ω}
  have hY : AEMeasurable Y μ := aemeasurable_iSup_le_ofReal
    (fun t ↦ ((hf.stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl).aemeasurable) hcont
  have hA (n : ℕ) : NullMeasurableSet (A n) μ := nullMeasurableSet_lt aemeasurable_const hY
  have hanti : Antitone A := by
    intro i j hij ω h
    have hij' : (δ i : ℝ≥0∞) ≤ δ j := by exact_mod_cast hδmono.monotone hij
    exact hij'.trans_lt h
  have hδlim' : Tendsto (fun n ↦ (δ n : ℝ≥0∞)) atTop (𝓝 (ε : ℝ≥0∞)) :=
    ENNReal.continuous_coe.tendsto ε |>.comp hδlim
  have hInter : (⋂ n, A n) = {ω | (ε : ℝ≥0∞) ≤ Y ω} := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq, A]
    exact ⟨fun h ↦ le_of_tendsto' hδlim' (fun n ↦ (h n).le),
      fun h n ↦ lt_of_lt_of_le (by exact_mod_cast (hδmem n).2) h⟩
  -- Decreasing crossing events converge in measure and under the terminal expectation.
  have hmeasure := tendsto_measure_iInter_atTop hA hanti ⟨0, measure_ne_top _ _⟩
  have hint := tendsto_integral_of_dominated_convergence (fun ω ↦ ‖f T ω‖)
    (fun n ↦ (hf.integrable T).aestronglyMeasurable.indicator₀ (hA n)) (hf.integrable T).norm
    (fun n ↦ Eventually.of_forall (fun ω ↦ norm_indicator_le_norm_self (f T) ω))
    (Eventually.of_forall (fun ω ↦ (hanti.tendsto_indicator _ _ _).trans (pure_le_nhds _)))
  simp_rw [integral_indicator₀ (hA _)] at hint
  rw [integral_indicator₀ (NullMeasurableSet.iInter hA)] at hint
  have hbound (n : ℕ) : δ n * μ (A n) ≤ ENNReal.ofReal (∫ ω in A n, f T ω ∂μ) := by
    have hset : A n = {ω | ∃ t ≤ T, (δ n : ℝ) < f t ω} := by
      ext ω
      simp [A, Y, lt_iSup_iff, ENNReal.coe_lt_ofReal]
    rw [hset]
    exact hf.mul_measure_exists_le_lt_le_setIntegral hnonneg hcont (δ n)
  have h := le_of_tendsto_of_tendsto'
    (ENNReal.Tendsto.mul hδlim' (Or.inr (measure_ne_top _ _)) hmeasure
      (Or.inr ENNReal.coe_ne_top)) (ENNReal.tendsto_ofReal hint) hbound
  simpa only [hInter] using h

end MeasureTheory.Submartingale
