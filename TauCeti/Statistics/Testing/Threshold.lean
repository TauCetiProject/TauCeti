/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Quantile
public import TauCeti.Statistics.Experiments.Tests

/-!
# Sizes of threshold tests

The threshold test `thresholdTest T c γ` rejects when the statistic `T` exceeds `c` and rejects
with probability `γ` when `T = c`. Under a finite measure `P` its integral, the size of the test
when `P` is a null law, is `P(T > c) + γ P(T = c)`. For a probability `P` and a real statistic `T`
every size `β ∈ (0, 1)` is attained: take for `c` the `(1 - β)`-quantile of the law of `T`, which
traps `1 - β` between `P(T < c)` and `P(T ≤ c)`, and randomize at `c` to fill the gap.

## Main results

* `TauCeti.integral_thresholdTest`: the size `P(T > c) + γ P(T = c)` of a threshold test.
* `TauCeti.exists_integral_thresholdTest_quantile_eq`: every size `β ∈ (0, 1)` is the size of a
  threshold test at the `(1 - β)`-quantile of the law of `T`, with randomization in `[0, 1]`.
* `TauCeti.exists_isSimilarTest_thresholdTest_quantile`: the same in a parametric family, as a
  test similar of size `β` at a null parameter `θ₀`.

## References

* M. J. Schervish, *Theory of Statistics*, Springer (1995), Theorem 4.56 and its proof,
  pp. 240–241.
* J. Pfanzagl, *Parametric Statistical Theory*, de Gruyter (1994), Lemma 4.3.3(i), pp. 133–134.

The results are adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Inference/NeymanPearson.lean`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

variable {X : Type*} [MeasurableSpace X]

/-- The **size of a threshold test**: under a finite measure `P` the integral of
`thresholdTest T c γ` is `P(T > c) + γ P(T = c)`. -/
theorem integral_thresholdTest {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [MeasurableSpace α] [OpensMeasurableSpace α] (P : Measure X)
    [IsFiniteMeasure P] {T : X → α} (hT : AEMeasurable T P) (c : α) (γ : ℝ) :
    ∫ x, thresholdTest T c γ x ∂P = P.real (T ⁻¹' Ioi c) + γ * P.real (T ⁻¹' {c}) := by
  have h₁ : MeasurableSet (Ioi c) := measurableSet_Ioi
  have h₂ : MeasurableSet {c} := measurableSet_singleton c
  have hsplit : thresholdTest (id : α → α) c γ =
      (Ioi c).indicator (fun _ ↦ (1 : ℝ)) + ({c} : Set α).indicator (fun _ ↦ γ) := by
    ext y
    rcases lt_trichotomy y c with h | h | h
    · simp [h, h.not_gt, h.ne]
    · simp [h]
    · simp [h, h.ne']
  have hm : Measurable (thresholdTest (id : α → α) c γ) := by
    rw [hsplit]
    exact (measurable_const.indicator h₁).add (measurable_const.indicator h₂)
  rw [show (fun x ↦ thresholdTest T c γ x) = fun x ↦ thresholdTest id c γ (T x) by
      simp [thresholdTest_apply],
    ← integral_map hT hm.aestronglyMeasurable, hsplit, Pi.add_def, integral_add
      ((integrable_const _).indicator h₁) ((integrable_const _).indicator h₂),
    integral_indicator_const _ h₁, integral_indicator_const _ h₂,
    map_measureReal_apply_of_aemeasurable hT h₁, map_measureReal_apply_of_aemeasurable hT h₂]
  simp [mul_comm]

/-- **Threshold tests attain every size.** For a probability `P`, a real statistic `T` and
`β ∈ (0, 1)`, the threshold test at the `(1 - β)`-quantile `c` of the law of `T` has size `β`
under `P` for some randomization `γ ∈ [0, 1]` at `c`. -/
theorem exists_integral_thresholdTest_quantile_eq (P : Measure X) [IsProbabilityMeasure P]
    {T : X → ℝ} (hT : AEMeasurable T P) {β : ℝ} (hβ : β ∈ Ioo 0 1) :
    ∃ γ ∈ Icc (0 : ℝ) 1,
      ∫ x, thresholdTest T ((P.map T).quantile (1 - β)) γ x ∂P = β := by
  set ν := P.map T
  set c := ν.quantile (1 - β)
  have hlt : ν.real (Iio c) ≤ 1 - β := ν.measureReal_Iio_quantile_le (by linarith [hβ.2])
  have hle : 1 - β ≤ ν.real (Iic c) := by
    rw [← cdf_eq_real]
    exact ν.le_cdf_quantile (by linarith [hβ.1])
  have hgt : ν.real (Ioi c) = 1 - ν.real (Iic c) := by
    rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  have heq : ν.real (Iic c) = ν.real (Iio c) + ν.real {c} := by
    rw [← Iio_union_right, measureReal_union (by simp) (measurableSet_singleton c)]
  simp_rw [integral_thresholdTest P hT,
    ← map_measureReal_apply_of_aemeasurable hT measurableSet_Ioi,
    ← map_measureReal_apply_of_aemeasurable hT (measurableSet_singleton _)]
  change ∃ γ ∈ Icc (0 : ℝ) 1, ν.real (Ioi c) + γ * ν.real {c} = β
  rcases (measureReal_nonneg : 0 ≤ ν.real {c}).eq_or_lt with hpe | hpe
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [← hpe] at heq ⊢; linarith⟩
  · refine ⟨(β - ν.real (Ioi c)) / ν.real {c},
      ⟨div_nonneg (by linarith) hpe.le, (div_le_one hpe).2 (by linarith)⟩, ?_⟩
    field_simp
    ring

/-- **Similar threshold tests.** In a family `P` whose law at `θ₀` is a probability, a real
measurable statistic `T` and `β ∈ (0, 1)`, the threshold test at the `(1 - β)`-quantile of the
law of `T` under `P θ₀`, with a suitable randomization `γ ∈ [0, 1]`, is a test similar of size
`β` on `{θ₀}`. -/
theorem exists_isSimilarTest_thresholdTest_quantile {Θ : Type*} (P : Θ → Measure X) (θ₀ : Θ)
    [IsProbabilityMeasure (P θ₀)] {T : X → ℝ} (hT : Measurable T) {β : ℝ} (hβ : β ∈ Ioo 0 1) :
    ∃ γ ∈ Icc (0 : ℝ) 1,
      IsSimilarTest P {θ₀} β (thresholdTest T (((P θ₀).map T).quantile (1 - β)) γ) := by
  obtain ⟨γ, hγ, h⟩ := exists_integral_thresholdTest_quantile_eq (P θ₀) hT.aemeasurable hβ
  exact ⟨γ, hγ, .mk (isStatisticalTest_thresholdTest hT _ hγ) fun θ hθ ↦ by
    rw [mem_singleton_iff.1 hθ, testPower_def, h]⟩

end TauCeti
