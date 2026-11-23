/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.Predictable.Measure
import TauCeti.MeasureTheory.Function.Lp.Iterated

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
horizon; this membership result does not require the grid to be monotone. Conversely,
an `Lᵖ((timeMeasure T).prod P)` simple holding on a monotone grid can be clipped by
zeroing out heights on steps of zero length in `(0, T]`, yielding `Lᵖ(P)` heights with
the same holding and elementary gains on `[0, T]`
(`TauCeti.Finance.exists_memLp_simpleHolding_simpleGains_eq_on_Iic`).

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
  simpa only [Function.uncurry_def, simpleHolding_def] using
    memLp_finsetSum (range n) fun i hi ↦
      ℱ.memLp_indicator_Ioc_predictableMeasure T (τ i) (τ (i + 1))
        (ha i (mem_range.mp hi)) (haLp i (mem_range.mp hi))

/-- Zeroing out the heights of a simple strategy on steps that contribute zero length on `(0, T]`
preserves left-endpoint measurability, the holding on `[0, T]`, and elementary gains on `[0, T]`,
while making every retained height `Lᵖ(P)` whenever the holding is
`Lᵖ((timeMeasure T).prod P)`. -/
theorem exists_memLp_simpleHolding_simpleGains_eq_on_Iic
    {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω} [SFinite P]
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ} {T : ℝ≥0} {p : ℝ≥0∞}
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hK : MemLp (Function.uncurry (simpleHolding τ n a)) p
      ((TauCeti.Probability.timeMeasure T).prod P)) :
    ∃ a' : ℕ → Ω → ℝ,
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (a' j)) ∧
      (∀ j < n, MemLp (a' j) p P) ∧
      (∀ s ≤ T, ∀ ω, simpleHolding τ n a' s ω = simpleHolding τ n a s ω) ∧
      (∀ (W : ℝ≥0 → Ω → ℝ), ∀ t ≤ T, ∀ ω,
        simpleGains τ n a' W t ω = simpleGains τ n a W t ω) := by
  classical
  let a' (j : ℕ) : Ω → ℝ := if min (τ j) T < min (τ (j + 1)) T then a j else 0
  refine ⟨a', fun j hj ↦ ?_, fun j hj ↦ ?_, fun s hs ω ↦ ?_, fun W t ht ω ↦ ?_⟩
  · dsimp only [a']
    split_ifs
    · exact ha j hj
    · exact stronglyMeasurable_zero
  · dsimp only [a']
    split_ifs with hlt
    · have hτj : τ j < T := lt_of_not_ge fun hle ↦ hlt.not_ge <| by
        simpa only [min_eq_right hle] using min_le_right (τ (j + 1)) T
      have hne : TauCeti.Probability.timeMeasure T (Ioc (τ j) (τ (j + 1))) ≠ 0 := by
        rw [TauCeti.Probability.timeMeasure_Ioc]
        exact (ENNReal.ofReal_pos.2 (sub_pos.2 (by
          exact_mod_cast (min_eq_left hτj.le ▸ hlt)))).ne'
      have hsec : ∀ᵐ s ∂TauCeti.Probability.timeMeasure T,
          MemLp (fun ω ↦ simpleHolding τ n a s ω) p P := by
        simpa only [Function.uncurry_apply_pair] using hK.ae_memLp_prod_right
      have hex : ∃ s ∈ Ioc (τ j) (τ (j + 1)),
          MemLp (fun ω ↦ simpleHolding τ n a s ω) p P := by
        by_contra hnot
        push Not at hnot
        exact hne (measure_mono_null (fun s hs ↦ hnot s hs) (ae_iff.1 hsec))
      obtain ⟨s, hs, hs_mem⟩ := hex
      exact hs_mem.ae_eq (.of_forall fun ω ↦ simpleHolding_of_mem_Ioc hτ hj hs ω)
    · exact MemLp.zero
  · simp only [simpleHolding_def]
    refine sum_congr rfl fun j _ ↦ ?_
    by_cases hjs : s ∈ Ioc (τ j) (τ (j + 1))
    · simp [a', hjs.1.trans_le hjs.2, hjs.1.trans_le hs]
    · simp [hjs]
  · simp only [simpleGains_def]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' := mem_range.1 hj
    dsimp only [a']
    split_ifs with hlt
    · rfl
    · have heq : min (τ j) T = min (τ (j + 1)) T :=
        le_antisymm (min_le_min_right T (hτ hj'.le hj' (Nat.le_succ j))) (not_lt.1 hlt)
      have hmin : min (τ j) t = min (τ (j + 1)) t := calc
        min (τ j) t = min (min (τ j) T) t := by rw [min_assoc, min_eq_right ht]
        _ = min (min (τ (j + 1)) T) t := by rw [heq]
        _ = min (τ (j + 1)) t := by rw [min_assoc, min_eq_right ht]
      simp [hmin]

end TauCeti.Finance
