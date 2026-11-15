/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.Predictable.Measure
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Square energy of elementary holdings

The lower square-energy integral of an elementary holding is the sum of the squared
heights times the masses of its trading intervals. For Lebesgue time on a finite
horizon these masses are the clipped interval lengths. The formulas are pathwise,
allow repeated dates and empty grids, and impose no moment or filtration hypotheses.

These identities connect finite-grid stochastic-integral estimates to the actual
lower-integral energy used in predictable approximation and localization. In particular,
no divergent Bochner integral is interpreted as zero energy. Left-measurable heights
in `Lᵖ` also give an elementary holding in the predictable `Lᵖ` space on each finite
horizon; this membership result does not require the grid to be monotone.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory Finset Set
open scoped ENNReal NNReal

namespace TauCeti.Finance

variable {Ω ι : Type*} [LinearOrder ι] {τ : ℕ → ι} {n : ℕ} {a : ℕ → Ω → ℝ}

private theorem enorm_sq_simpleHolding (hτ : MonotoneOn τ (Set.Iic n)) (t : ι) (ω : Ω) :
    ‖simpleHolding τ n a t ω‖ₑ ^ 2 =
      ∑ j ∈ range n, (Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ ‖a j ω‖ₑ ^ 2) t := by
  by_cases ht : ∃ j < n, t ∈ Ioc (τ j) (τ (j + 1))
  · obtain ⟨j, hj, hjt⟩ := ht
    rw [simpleHolding_of_mem_Ioc hτ hj hjt,
      sum_eq_single_of_mem j (mem_range.mpr hj), indicator_of_mem hjt]
    intro i hi hij
    exact indicator_of_notMem
      (hτ.notMem_Ioc_of_mem_Ioc_of_ne (mem_range.mp hi) hj hij hjt) _
  · have hzero {M : Type} [AddCommMonoid M] (b : ℕ → M) :
        ∑ j ∈ range n, (Ioc (τ j) (τ (j + 1))).indicator (fun _ ↦ b j) t = 0 :=
      sum_eq_zero fun j hj ↦ indicator_of_notMem (fun hjt ↦ ht ⟨j, mem_range.mp hj, hjt⟩) _
    rw [simpleHolding_def, hzero (fun j ↦ a j ω), hzero (fun j ↦ ‖a j ω‖ₑ ^ 2)]
    simp

/-- The pathwise square energy of elementary holdings for any time measure is the
sum of the squared heights times the masses of the disjoint trading intervals. -/
theorem _root_.MeasureTheory.Measure.lintegral_enorm_sq_simpleHolding [MeasurableSpace ι]
    (μ : Measure ι)
    (hτ : MonotoneOn τ (Set.Iic n))
    (hI : ∀ j < n, MeasurableSet (Ioc (τ j) (τ (j + 1)))) (ω : Ω) :
    ∫⁻ t, ‖simpleHolding τ n a t ω‖ₑ ^ 2 ∂μ =
      ∑ j ∈ range n, ‖a j ω‖ₑ ^ 2 * μ (Ioc (τ j) (τ (j + 1))) := by
  simp_rw [enorm_sq_simpleHolding hτ]
  rw [lintegral_finsetSum _ (fun j hj ↦ measurable_const.indicator (hI j (mem_range.mp hj)))]
  exact sum_congr rfl fun j hj ↦ lintegral_indicator_const (hI j (mem_range.mp hj)) _

/-- Under finite-horizon Lebesgue time, the square energy uses the interval lengths
clipped at the horizon, including intervals that have not yet started. -/
theorem lintegral_enorm_sq_simpleHolding_timeMeasure {τ : ℕ → ℝ≥0}
    (hτ : MonotoneOn τ (Set.Iic n)) (T : ℝ≥0) (ω : Ω) :
    ∫⁻ t, ‖simpleHolding τ n a t ω‖ₑ ^ 2 ∂TauCeti.Probability.timeMeasure T =
      ∑ j ∈ range n, ‖a j ω‖ₑ ^ 2 *
        ENNReal.ofReal ((min (τ (j + 1)) T : ℝ≥0) - (τ j : ℝ)) := by
  rw [Measure.lintegral_enorm_sq_simpleHolding _ hτ (fun _ _ ↦ measurableSet_Ioc)]
  simp only [TauCeti.Probability.timeMeasure_Ioc]

/-- Left-measurable `Lᵖ` heights give predictable `Lᵖ` holdings on every finite horizon.
No order condition on the grid, boundedness, or finiteness of the sample measure is needed. -/
theorem memLp_simpleHolding_predictableMeasure {τ : ℕ → ℝ≥0} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω} [SFinite P] {p : ℝ≥0∞}
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (haLp : ∀ i < n, MemLp (a i) p P) (T : ℝ≥0) :
    MemLp (Function.uncurry (simpleHolding τ n a)) p (ℱ.predictableMeasure P T) := by
  rw [ℱ.memLp_predictableMeasure_iff P (isStronglyPredictable_simpleHolding ha) T p]
  have hterm (i : ℕ) (hi : i ∈ range n) : MemLp
      ((Ioc (τ i) (τ (i + 1)) ×ˢ (univ : Set Ω)).indicator (fun q ↦ a i q.2)) p
      ((TauCeti.Probability.timeMeasure T).prod P) :=
    ((haLp i (mem_range.mp hi)).comp_snd _).indicator
      (measurableSet_Ioc.prod MeasurableSet.univ).nullMeasurableSet
  convert memLp_finsetSum (range n) hterm using 1
  ext ⟨t, ω⟩
  simp only [Function.uncurry_apply_pair, simpleHolding_def]
  apply sum_congr rfl
  intro i _
  by_cases ht : t ∈ Ioc (τ i) (τ (i + 1)) <;> simp [ht]

end TauCeti.Finance
