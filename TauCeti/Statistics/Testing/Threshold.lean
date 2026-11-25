/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Quantile
public import TauCeti.Statistics.Experiments.Tests

/-!
# Threshold tests of every size

The threshold test `thresholdTest T c γ` rejects when the statistic `T` exceeds `c` and rejects
with probability `γ` when `T = c`. Its integral under a measure `P` is `P(T > c) + γ P(T = c)`
whenever the two events are null-measurable with finite measure
(`TauCeti.integral_thresholdTest`, in `TauCeti/Statistics/Experiments/Tests.lean`); for a
measurable `T`, `γ ∈ [0, 1]` and a probability null law `P`, it is the size of the test. For a
probability `P` and a real statistic `T` that is almost everywhere measurable under `P`, every
value `β ∈ (0, 1)` is such an integral: take for `c` the `(1 - β)`-quantile of the law of `T`,
which traps `1 - β` between `P(T < c)` and `P(T ≤ c)`, and randomize at `c` to fill the gap.

## Main results

* `TauCeti.exists_integral_thresholdTest_quantile_eq`: for an almost everywhere measurable real
  statistic, every `β ∈ (0, 1)` is the integral of a threshold test at the `(1 - β)`-quantile of
  the law of `T`, with randomization in `[0, 1]`.
* `TauCeti.exists_isSimilarTest_thresholdTest_quantile`: for a measurable real statistic in a
  parametric family, the same test is similar of size `β` at a null parameter `θ₀`.

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

/-- **Threshold tests attain every size.** For a probability `P`, a real statistic `T` that is
almost everywhere measurable under `P`, and `β ∈ (0, 1)`, the threshold test at the
`(1 - β)`-quantile `c` of the law of `T` has integral `β` under `P` for some randomization
`γ ∈ [0, 1]` at `c`. For a measurable `T` this is the size of the test under the null law `P`. -/
theorem exists_integral_thresholdTest_quantile_eq {P : Measure X} [IsProbabilityMeasure P]
    {T : X → ℝ} (hT : AEMeasurable T P) {β : ℝ} (hβ : β ∈ Ioo 0 1) :
    ∃ γ ∈ Icc (0 : ℝ) 1,
      ∫ x, thresholdTest T ((P.map T).quantile (1 - β)) γ x ∂P = β := by
  set ν := P.map T with hν
  set c := ν.quantile (1 - β)
  have hlt : ν.real (Iio c) ≤ 1 - β := ν.measureReal_Iio_quantile_le (by linarith [hβ.2])
  have hle : 1 - β ≤ cdf ν c := ν.le_cdf_quantile (by linarith [hβ.1])
  have hgt := ν.measureReal_Ioi_eq_one_sub_cdf c
  have heq : cdf ν c = ν.real (Iio c) + ν.real {c} := by
    rw [cdf_eq_real, ← Iio_union_right, measureReal_union (by simp) (measurableSet_singleton c)]
  -- The integral is `f γ` for the affine function `f γ = ν(T > c) + γ ν(T = c)`.
  have hint (γ : ℝ) : ∫ x, thresholdTest T c γ x ∂P = ν.real (Ioi c) + γ * ν.real {c} := by
    rw [integral_thresholdTest (hT.nullMeasurableSet_preimage measurableSet_Ioi)
      (hT.nullMeasurableSet_preimage (measurableSet_singleton c)) (measure_ne_top _ _)
      (measure_ne_top _ _), hν, map_measureReal_apply_of_aemeasurable hT measurableSet_Ioi,
      map_measureReal_apply_of_aemeasurable hT (measurableSet_singleton c)]
  -- `f 0 ≤ β ≤ f 1`, so the intermediate value theorem gives `γ ∈ [0, 1]` with `f γ = β`.
  have hβmem : β ∈ Icc (ν.real (Ioi c) + 0 * ν.real {c}) (ν.real (Ioi c) + 1 * ν.real {c}) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨γ, hγ, hfγ⟩ := intermediate_value_Icc zero_le_one
    (by fun_prop : Continuous fun γ : ℝ ↦ ν.real (Ioi c) + γ * ν.real {c}).continuousOn hβmem
  exact ⟨γ, hγ, (hint γ).trans hfγ⟩

/-- **Similar threshold tests.** In a family `P` whose law at `θ₀` is a probability, a real
measurable statistic `T` and `β ∈ (0, 1)`, the threshold test at the `(1 - β)`-quantile of the
law of `T` under `P θ₀`, with a suitable randomization `γ ∈ [0, 1]`, is a test similar of size
`β` on `{θ₀}`. -/
theorem exists_isSimilarTest_thresholdTest_quantile {Θ : Type*} (P : Θ → Measure X) (θ₀ : Θ)
    [IsProbabilityMeasure (P θ₀)] {T : X → ℝ} (hT : Measurable T) {β : ℝ} (hβ : β ∈ Ioo 0 1) :
    ∃ γ ∈ Icc (0 : ℝ) 1,
      IsSimilarTest P {θ₀} β (thresholdTest T (((P θ₀).map T).quantile (1 - β)) γ) := by
  obtain ⟨γ, hγ, h⟩ := exists_integral_thresholdTest_quantile_eq (P := P θ₀) hT.aemeasurable hβ
  exact ⟨γ, hγ, .mk (isStatisticalTest_thresholdTest hT _ hγ) fun θ hθ ↦ by
    rw [mem_singleton_iff.1 hθ, testPower_def, h]⟩

end TauCeti
