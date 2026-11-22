/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import TauCeti.MeasureTheory.MeasurableSpace.Metric

/-!
# Reduction of estimation to testing

Let `(Y, d)` be a pseudometric space, `θ : ι → Y` a family of parameters with
`2 s ≤ d (θ i) (θ j)` for `i ≠ j`, and `P : ι → Measure X` the corresponding observation laws.
An estimator is a Markov kernel `κ : Kernel X Y`. The open balls of radius `s` around the
parameters are pairwise disjoint, so sending a point of `Y` to the index of the ball containing it
(and to a fixed index `i₀` outside all balls) is a measurable map `ballIndex θ s i₀ : Y → ι`
(`TauCeti.ballIndex`, in `TauCeti.Topology.MetricSpace.SeparatedBalls`, and
`TauCeti.measurable_ballIndex`, in `TauCeti.MeasureTheory.MeasurableSpace.Metric`).
Composing `κ` with it gives a test `ψ : Kernel X ι` whose error under `P i` is at most the
probability that the estimate is at distance at least `s` from `θ i`:
`(ψ ∘ₘ P i) {i}ᶜ ≤ (κ ∘ₘ P i) {y | s ≤ d y (θ i)}`.
Together with Markov's inequality for a monotone loss of the distance
(`TauCeti.mul_measure_le_lintegral_edist`, in `TauCeti.MeasureTheory.Integral.Lebesgue.Dist`),
this turns lower bounds for the error of tests into lower bounds for the risk of estimators.

No finiteness or countability of the index set is needed: a union of open balls is open, so every
preimage under `ballIndex` is the union of an open set and a closed set.

For a finite, nonempty, linearly ordered index set and parameters that need not be separated,
`TauCeti.nearestIndex θ y`, in `TauCeti.MeasureTheory.MeasurableSpace.Metric`, is the least index
of a nearest parameter to `y`; it is measurable and
`dist (θ (nearestIndex θ y)) (θ j) ≤ 2 * dist y (θ j)` for every `j`.

## Main results

* `TauCeti.comp_map_ballIndex_compl_le`: the error of the test `κ.map (ballIndex θ s i₀)`.
* `TauCeti.le_max_measure_dist_ge_of_test`: every estimator is dominated by a test.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer (2009), (2.5) and (2.8),
  pp. 79–80.
* M. J. Wainwright, *High-Dimensional Statistics*, Cambridge University Press (2019),
  Proposition 15.1, pp. 487–488.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set

open scoped ENNReal

namespace TauCeti

variable {ι X Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [OpensMeasurableSpace Y] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- For `2 s`-separated parameters, the error of the test `κ.map (ballIndex θ s i₀)` at `i` is at
most the probability that the estimate `κ` is at distance at least `s` from `θ i`. -/
theorem comp_map_ballIndex_compl_le {θ : ι → Y} {s : ℝ}
    (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j)) (i₀ : ι) (κ : Kernel X Y) (μ : Measure X)
    (i : ι) : (κ.map (ballIndex θ s i₀) ∘ₘ μ) {i}ᶜ ≤ (κ ∘ₘ μ) {y | s ≤ dist y (θ i)} := by
  rw [← Measure.map_comp _ _ (measurable_ballIndex hθ i₀),
    Measure.map_apply (measurable_ballIndex hθ i₀) (measurableSet_singleton i).compl]
  exact measure_mono fun y hy ↦ le_dist_of_ballIndex_ne hθ hy

/-- **Reduction of estimation to testing.** For `2 s`-separated parameters `θ i`, every
estimator `κ` is dominated by a test `ψ`: the error of `ψ` under `P i` is at most the probability
under `P i` that the estimate is at distance at least `s` from `θ i`. -/
theorem le_max_measure_dist_ge_of_test [Nonempty ι] (P : ι → Measure X) (θ : ι → Y) {s : ℝ}
    (hs : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j)) (κ : Kernel X Y) [IsMarkovKernel κ] :
    ∃ ψ : Kernel X ι, IsMarkovKernel ψ ∧
      ∀ i, (ψ ∘ₘ P i) {i}ᶜ ≤ (κ ∘ₘ P i) {y | s ≤ dist y (θ i)} :=
  ⟨κ.map (ballIndex θ s (Classical.arbitrary ι)),
    Kernel.IsMarkovKernel.map κ (measurable_ballIndex hs _),
    fun i ↦ comp_map_ballIndex_compl_le hs _ κ (P i) i⟩

end TauCeti
