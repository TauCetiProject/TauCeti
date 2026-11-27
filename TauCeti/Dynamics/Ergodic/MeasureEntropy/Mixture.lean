/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Basic
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Entropy of mixtures of invariant probabilities

For probability measures `μ`, `ν` and `a ∈ [0, 1]` (in `ℝ≥0∞`), write `m = a • μ + (1 - a) • ν`
for their mixture. For a measurable countable label `ξ`, concavity of `negMulLog` gives
`a H_μ(ξ) + (1 - a) H_ν(ξ) ≤ H_m(ξ)`, and subadditivity of `negMulLog` with
`negMulLog (x * y) = y negMulLog x + x negMulLog y` gives the reverse inequality up to the
bounded error `c(a) = negMulLog a + negMulLog (1 - a)`. Applied to itineraries and divided by `n`,
the error disappears, so entropy rates are affine in the measure:
`h_m(T, ξ) = a h_μ(T, ξ) + (1 - a) h_ν(T, ξ)` when `T` preserves `μ` and `ν`. Taking suprema
gives `h_m(T) ≤ a h_μ(T) + (1 - a) h_ν(T)`.

The reverse inequality for the Kolmogorov–Sinai entropy needs a single label that is good for
`μ` and for `ν` at once, and is not proved here.

## Main results

* `TauCeti.negMulLog_add_le`: `negMulLog` is subadditive on `[0, ∞)`.
* `TauCeti.mul_add_mul_le_countablePartitionEntropy_mixture` and
  `TauCeti.countablePartitionEntropy_mixture_le`: the two-sided bound for `H_m(ξ)`.
* `TauCeti.partitionEntropyRate_mixture`:
  `h_m(T, ξ) = a h_μ(T, ξ) + (1 - a) h_ν(T, ξ)`.
* `TauCeti.measureEntropy_mixture_le`: `h_m(T) ≤ a h_μ(T) + (1 - a) h_ν(T)`.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Problem 4.6, p. 130.
-/

public section

open MeasureTheory Real Filter Topology
open scoped ENNReal

namespace TauCeti

/-- `negMulLog` is subadditive on `[0, ∞)`: `negMulLog (x + y) ≤ negMulLog x + negMulLog y`. -/
theorem negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog (x + y) ≤ negMulLog x + negMulLog y := by
  have key : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → -(x * log (x + y)) ≤ -(x * log x) := by
    intro x y hx hy
    rcases hx.eq_or_lt with rfl | hx'
    · simp
    · exact neg_le_neg (mul_le_mul_of_nonneg_left (log_le_log hx' (by linarith)) hx)
  have h1 := key hx hy
  have h2 := key hy hx
  rw [add_comm y x] at h2
  have e : negMulLog (x + y) = -(x * log (x + y)) + -(y * log (x + y)) := by
    rw [negMulLog]
    ring
  rw [e, negMulLog, negMulLog]
  linarith

variable {X ι : Type*} {mX : MeasurableSpace X} {μ ν : Measure X} {a : ℝ≥0∞}

/-- The real mass of a set under a mixture of finite measures. -/
theorem measureReal_mixture [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ha : a ≤ 1) (s : Set X) :
    (a • μ + (1 - a) • ν).real s = a.toReal * μ.real s + (1 - a).toReal * ν.real s := by
  have ha' : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hm : (a • μ + (1 - a) • ν) s = a * μ s + (1 - a) * ν s := by simp
  rw [measureReal_def, hm, ENNReal.toReal_add (ENNReal.mul_ne_top ha' (measure_ne_top μ s))
      (ENNReal.mul_ne_top (by simp) (measure_ne_top ν s)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, measureReal_def, measureReal_def]

/-- A mixture of probability measures with weights `a` and `1 - a` is a probability measure. -/
theorem isProbabilityMeasure_mixture [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ha : a ≤ 1) : IsProbabilityMeasure (a • μ + (1 - a) • ν) :=
  ⟨by simp [add_tsub_cancel_of_le ha]⟩

/-- A map preserving `μ` and `ν` preserves their mixtures. -/
theorem measurePreserving_mixture {T : X → X} (hμ : MeasurePreserving T μ μ)
    (hν : MeasurePreserving T ν ν) (a : ℝ≥0∞) :
    MeasurePreserving T (a • μ + (1 - a) • ν) (a • μ + (1 - a) • ν) := by
  refine ⟨hμ.measurable, ?_⟩
  rw [Measure.map_add _ _ hμ.measurable, Measure.map_smul, Measure.map_smul, hμ.map_eq,
    hν.map_eq]
  all_goals exact hμ.measurable.aemeasurable

private lemma toReal_add_toReal_sub (ha : a ≤ 1) : a.toReal + (1 - a).toReal = 1 := by
  rw [← ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.one_ne_top ha) (by simp),
    add_tsub_cancel_of_le ha, ENNReal.toReal_one]

private lemma toReal_le_one_of_le (ha : a ≤ 1) : a.toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top ha

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Concavity.** The entropy of a label under a mixture is at least the mixture of its
entropies: `a H_μ(ξ) + (1 - a) H_ν(ξ) ≤ H_{a μ + (1 - a) ν}(ξ)`. -/
theorem mul_add_mul_le_countablePartitionEntropy_mixture (ha : a ≤ 1) (ξ : X → ι) :
    a * countablePartitionEntropy μ ξ + (1 - a) * countablePartitionEntropy ν ξ ≤
      countablePartitionEntropy (a • μ + (1 - a) • ν) ξ := by
  have ha' : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  simp only [countablePartitionEntropy_def, ← ENNReal.tsum_mul_left, ← tsum_add]
  refine tsum_le_tsum fun i ↦ ?_
  have hp0 := measureReal_nonneg (μ := μ) (s := ξ ⁻¹' {i})
  have hq0 := measureReal_nonneg (μ := ν) (s := ξ ⁻¹' {i})
  have hp := negMulLog_nonneg hp0 (measureReal_le_one (μ := μ))
  have hq := negMulLog_nonneg hq0 (measureReal_le_one (μ := ν))
  calc a * ENNReal.ofReal (negMulLog (μ.real (ξ ⁻¹' {i}))) +
        (1 - a) * ENNReal.ofReal (negMulLog (ν.real (ξ ⁻¹' {i})))
      = ENNReal.ofReal (a.toReal * negMulLog (μ.real (ξ ⁻¹' {i})) +
          (1 - a).toReal * negMulLog (ν.real (ξ ⁻¹' {i}))) := by
        rw [ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hp)
          (mul_nonneg ENNReal.toReal_nonneg hq), ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha',
          ENNReal.ofReal_toReal (by simp)]
    _ ≤ ENNReal.ofReal (negMulLog ((a • μ + (1 - a) • ν).real (ξ ⁻¹' {i}))) := by
        rw [measureReal_mixture ha]
        exact ENNReal.ofReal_le_ofReal (Real.concaveOn_negMulLog.2 hp0 hq0
          ENNReal.toReal_nonneg ENNReal.toReal_nonneg (toReal_add_toReal_sub ha))

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]

/-- **Bounded defect.** The entropy of a measurable label under a mixture exceeds the mixture of
its entropies by at most `negMulLog a + negMulLog (1 - a)`. -/
theorem countablePartitionEntropy_mixture_le (ha : a ≤ 1) {ξ : X → ι} (hξ : Measurable ξ) :
    countablePartitionEntropy (a • μ + (1 - a) • ν) ξ ≤
      a * countablePartitionEntropy μ ξ + (1 - a) * countablePartitionEntropy ν ξ +
        ENNReal.ofReal (negMulLog a.toReal + negMulLog (1 - a).toReal) := by
  have ha' : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have hα0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
  have hβ0 : 0 ≤ (1 - a).toReal := ENNReal.toReal_nonneg
  have hα := negMulLog_nonneg hα0 (toReal_le_one_of_le ha)
  have hβ := negMulLog_nonneg hβ0 (toReal_le_one_of_le tsub_le_self)
  have hcell : ∀ i, ENNReal.ofReal (negMulLog ((a • μ + (1 - a) • ν).real (ξ ⁻¹' {i}))) ≤
      a * ENNReal.ofReal (negMulLog (μ.real (ξ ⁻¹' {i}))) +
        (1 - a) * ENNReal.ofReal (negMulLog (ν.real (ξ ⁻¹' {i}))) +
          (ENNReal.ofReal (negMulLog a.toReal) * μ (ξ ⁻¹' {i}) +
            ENNReal.ofReal (negMulLog (1 - a).toReal) * ν (ξ ⁻¹' {i})) := fun i ↦ by
    have hp0 := measureReal_nonneg (μ := μ) (s := ξ ⁻¹' {i})
    have hq0 := measureReal_nonneg (μ := ν) (s := ξ ⁻¹' {i})
    have hp := negMulLog_nonneg hp0 (measureReal_le_one (μ := μ))
    have hq := negMulLog_nonneg hq0 (measureReal_le_one (μ := ν))
    have hreal : negMulLog ((a • μ + (1 - a) • ν).real (ξ ⁻¹' {i})) ≤
        a.toReal * negMulLog (μ.real (ξ ⁻¹' {i})) +
          (1 - a).toReal * negMulLog (ν.real (ξ ⁻¹' {i})) +
          (negMulLog a.toReal * μ.real (ξ ⁻¹' {i}) +
            negMulLog (1 - a).toReal * ν.real (ξ ⁻¹' {i})) := by
      rw [measureReal_mixture ha]
      refine (negMulLog_add_le (mul_nonneg hα0 hp0) (mul_nonneg hβ0 hq0)).trans_eq ?_
      rw [negMulLog_mul, negMulLog_mul]
      ring
    refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hα0, ENNReal.ofReal_mul hβ0, ENNReal.ofReal_mul hα,
      ENNReal.ofReal_mul hβ, ENNReal.ofReal_toReal ha', ENNReal.ofReal_toReal (by simp),
      ofReal_measureReal, ofReal_measureReal]
  have hA : ∑' i, μ (ξ ⁻¹' {i}) = 1 := by
    simpa using (tsum_univ (f := fun i ↦ μ (ξ ⁻¹' {i}))).symm.trans
      (tsum_measure_preimage_singleton Set.countable_univ fun i _ ↦ hξ (measurableSet_singleton i))
  have hB : ∑' i, ν (ξ ⁻¹' {i}) = 1 := by
    simpa using (tsum_univ (f := fun i ↦ ν (ξ ⁻¹' {i}))).symm.trans
      (tsum_measure_preimage_singleton Set.countable_univ fun i _ ↦ hξ (measurableSet_singleton i))
  rw [countablePartitionEntropy_def]
  refine (tsum_le_tsum hcell).trans_eq ?_
  rw [tsum_add, tsum_add, tsum_add, ENNReal.tsum_mul_left,
    ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hA, hB, mul_one, mul_one,
    ← ENNReal.ofReal_add hα hβ]
  simp only [countablePartitionEntropy_def]

variable {T : X → X}

/-- **Affinity of entropy rates.** For a map preserving the probability measures `μ` and `ν` and
a measurable countable label `ξ`, the entropy rate under the mixture `a • μ + (1 - a) • ν` is
`a h_μ(T, ξ) + (1 - a) h_ν(T, ξ)`. -/
theorem partitionEntropyRate_mixture (ha : a ≤ 1) (hμ : MeasurePreserving T μ μ)
    (hν : MeasurePreserving T ν ν) {ξ : X → ι} (hξ : Measurable ξ) :
    partitionEntropyRate (a • μ + (1 - a) • ν) T ξ =
      a * partitionEntropyRate μ T ξ + (1 - a) * partitionEntropyRate ν T ξ := by
  have ha' : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ha
  have := isProbabilityMeasure_mixture (μ := μ) (ν := ν) ha
  set c := ENNReal.ofReal (negMulLog a.toReal + negMulLog (1 - a).toReal)
  have hb := measurable_iteratedPartitionLabel hμ.measurable hξ
  set g : ℕ → ℝ≥0∞ := fun n ↦
    a * (countablePartitionEntropy μ (iteratedPartitionLabel T ξ n) / n) +
      (1 - a) * (countablePartitionEntropy ν (iteratedPartitionLabel T ξ n) / n)
  have hg : Tendsto g atTop
      (𝓝 (a * partitionEntropyRate μ T ξ + (1 - a) * partitionEntropyRate ν T ξ)) :=
    (ENNReal.Tendsto.const_mul (tendsto_partitionEntropyRate hμ hξ) (Or.inr ha')).add
      (ENNReal.Tendsto.const_mul (tendsto_partitionEntropyRate hν hξ) (Or.inr (by simp)))
  have hc : Tendsto (fun n : ℕ ↦ c * (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr ENNReal.ofReal_ne_top)
  have hgc := hg.add hc
  rw [add_zero] at hgc
  have hsplit : ∀ n : ℕ, (a * countablePartitionEntropy μ (iteratedPartitionLabel T ξ n) +
      (1 - a) * countablePartitionEntropy ν (iteratedPartitionLabel T ξ n)) / n = g n :=
    fun n ↦ by simp only [g, ENNReal.add_div, mul_div_assoc]
  refine tendsto_nhds_unique (tendsto_partitionEntropyRate (measurePreserving_mixture hμ hν a) hξ)
    (tendsto_of_tendsto_of_tendsto_of_le_of_le hg hgc (fun n ↦ ?_) (fun n ↦ ?_))
  · rw [← hsplit]
    exact ENNReal.div_le_div_right
      (mul_add_mul_le_countablePartitionEntropy_mixture ha _) _
  · refine (ENNReal.div_le_div_right
      (countablePartitionEntropy_mixture_le ha (hb n)) _).trans_eq ?_
    rw [ENNReal.add_div, hsplit, div_eq_mul_inv]

/-- An entropy that is finite under the mixture is finite under each component of positive
weight. -/
private lemma countablePartitionEntropy_ne_top_of_mixture {b : ℝ≥0∞} {H H' : ℝ≥0∞}
    (hb : b ≠ 0) (hle : b * H ≤ H') (hH' : H' ≠ ∞) : H ≠ ∞ := by
  rintro rfl
  rw [ENNReal.mul_top hb, top_le_iff] at hle
  exact hH' hle

/-- **Upper bound for mixtures.** For a map preserving the probability measures `μ` and `ν`,
`h_{a μ + (1 - a) ν}(T) ≤ a h_μ(T) + (1 - a) h_ν(T)`. -/
theorem measureEntropy_mixture_le (ha : a ≤ 1) (hμ : MeasurePreserving T μ μ)
    (hν : MeasurePreserving T ν ν) :
    measureEntropy (a • μ + (1 - a) • ν) T ≤
      a * measureEntropy μ T + (1 - a) * measureEntropy ν T := by
  refine measureEntropy_le_iff.2 fun ξ hξ hfin ↦ ?_
  rw [partitionEntropyRate_mixture ha hμ hν hξ]
  have hlow := mul_add_mul_le_countablePartitionEntropy_mixture (μ := μ) (ν := ν) ha ξ
  refine add_le_add ?_ ?_
  · rcases eq_or_ne a 0 with rfl | ha0
    · simp
    gcongr
    exact partitionEntropyRate_le_measureEntropy hξ
      (countablePartitionEntropy_ne_top_of_mixture ha0 (le_add_right le_rfl |>.trans hlow) hfin)
  · rcases eq_or_ne (1 - a) 0 with h0 | hb0
    · simp [h0]
    gcongr
    exact partitionEntropyRate_le_measureEntropy hξ
      (countablePartitionEntropy_ne_top_of_mixture hb0 (le_add_left le_rfl |>.trans hlow) hfin)

end TauCeti
