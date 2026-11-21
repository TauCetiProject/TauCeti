/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import TauCeti.MeasureTheory.Integral.Lebesgue.Dist

/-!
# Reduction of estimation to testing

Let `(Y, d)` be a pseudometric space, `θ : ι → Y` a family of parameters with
`2 s ≤ d (θ i) (θ j)` for `i ≠ j`, and `P : ι → Measure X` the corresponding observation laws.
An estimator is a Markov kernel `κ : Kernel X Y`. The open balls of radius `s` around the
parameters are pairwise disjoint, so sending a point of `Y` to the index of the ball containing it
(and to a fixed index `i₀` outside all balls) is a measurable map `ballIndex θ s i₀ : Y → ι`.
Composing `κ` with it gives a test `ψ : Kernel X ι` whose error under `P i` is at most the
probability that the estimate is at distance at least `s` from `θ i`:
`(ψ ∘ₘ P i) {i}ᶜ ≤ (κ ∘ₘ P i) {y | s ≤ d y (θ i)}`.
Together with Markov's inequality for a monotone loss of the distance
(`TauCeti.mul_measure_le_lintegral_edist`, in `TauCeti.MeasureTheory.Integral.Lebesgue.Dist`),
this turns lower bounds for the error of tests into lower bounds for the risk of estimators.

No finiteness or countability of the index set is needed: a union of open balls is open, so every
preimage under `ballIndex` is the union of an open set and a closed set.

For a finite, nonempty, linearly ordered index set and parameters that need not be separated,
`nearestIndex θ y` is the least index of a nearest parameter to `y`; it is measurable and
`dist (θ (nearestIndex θ y)) (θ j) ≤ 2 * dist y (θ j)` for every `j`.

## Main definitions

* `TauCeti.ballIndex θ s i₀`: the index of the ball of radius `s` containing a point, or `i₀`.
* `TauCeti.nearestIndex θ`: the least index of a nearest parameter.

## Main results

* `TauCeti.le_dist_of_ballIndex_ne`: if the parameters are `2 s`-separated and
  `ballIndex θ s i₀ y ≠ i`, then `s ≤ dist y (θ i)`.
* `TauCeti.measurable_ballIndex`: `ballIndex θ s i₀` is measurable.
* `TauCeti.comp_map_ballIndex_compl_le`: the error of the test `κ.map (ballIndex θ s i₀)`.
* `TauCeti.le_max_measure_dist_ge_of_test`: every estimator is dominated by a test.
* `TauCeti.measurable_nearestIndex`, `TauCeti.dist_nearestIndex_le` and
  `TauCeti.dist_nearestIndex_le_two_mul`: the nearest-parameter map is measurable, minimizes the
  distance, and lands within twice the distance to any parameter.

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

variable {ι X Y : Type*} [PseudoMetricSpace Y]

open scoped Classical in
/-- The index of the open ball of radius `s` around a parameter `θ i` that contains `y`, and `i₀`
when `y` lies in no such ball. For `2 s`-separated parameters the balls are pairwise disjoint, so
the index is unique (`ballIndex_eq_of_mem_ball`). -/
def ballIndex (θ : ι → Y) (s : ℝ) (i₀ : ι) (y : Y) : ι :=
  if h : ∃ i, y ∈ ball (θ i) s then h.choose else i₀

open scoped Classical in
theorem ballIndex_def (θ : ι → Y) (s : ℝ) (i₀ : ι) (y : Y) :
    ballIndex θ s i₀ y = if h : ∃ i, y ∈ ball (θ i) s then h.choose else i₀ := (rfl)

/-- For `2 s`-separated parameters, the open balls of radius `s` around them meet only when
they are equal. -/
private theorem eq_of_mem_ball_of_mem_ball {θ : ι → Y} {s : ℝ}
    (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j)) {y : Y} {i j : ι}
    (hi : y ∈ ball (θ i) s) (hj : y ∈ ball (θ j) s) : i = j := by
  by_contra hij
  exact (ball_disjoint_ball (by linarith [hθ i j hij])).ne_of_mem hi hj rfl

/-- A point in the ball around `θ i` has index `i`. -/
theorem ballIndex_eq_of_mem_ball {θ : ι → Y} {s : ℝ}
    (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j)) (i₀ : ι) {y : Y} {i : ι}
    (hy : y ∈ ball (θ i) s) : ballIndex θ s i₀ y = i := by
  have h : ∃ j, y ∈ ball (θ j) s := ⟨i, hy⟩
  rw [ballIndex, dite_eq_left h]
  exact eq_of_mem_ball_of_mem_ball hθ h.choose_spec hy

/-- A point in no ball has the default index. -/
@[simp]
theorem ballIndex_eq_of_forall_notMem {θ : ι → Y} {s : ℝ} (i₀ : ι) {y : Y}
    (hy : ∀ i, y ∉ ball (θ i) s) : ballIndex θ s i₀ y = i₀ := by
  rw [ballIndex, dite_eq_right (by simpa using hy)]

/-- For `2 s`-separated parameters, a point whose index is not `i` is at distance at least `s`
from `θ i`. -/
theorem le_dist_of_ballIndex_ne {θ : ι → Y} {s : ℝ}
    (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j)) {i₀ : ι} {y : Y} {i : ι}
    (h : ballIndex θ s i₀ y ≠ i) : s ≤ dist y (θ i) :=
  not_lt.1 fun hy ↦ h (ballIndex_eq_of_mem_ball hθ i₀ (mem_ball.2 hy))

/-- For `2 s`-separated parameters, the preimage of a set `A` of indices under `ballIndex` is the
union of the balls with index in `A`, together with the complement of all balls when `i₀ ∈ A`. -/
theorem ballIndex_preimage {θ : ι → Y} {s : ℝ} (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j))
    (i₀ : ι) (A : Set ι) :
    ballIndex θ s i₀ ⁻¹' A =
      (⋃ i ∈ A, ball (θ i) s) ∪ ({_y | i₀ ∈ A} ∩ ⋂ i, (ball (θ i) s)ᶜ) := by
  ext y
  by_cases hy : ∃ i, y ∈ ball (θ i) s
  · obtain ⟨i, hi⟩ := hy
    simp only [mem_preimage, ballIndex_eq_of_mem_ball hθ i₀ hi, mem_union, mem_iUnion₂,
      mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_compl_iff]
    refine ⟨fun hA ↦ .inl ⟨i, hA, hi⟩, ?_⟩
    rintro (⟨j, hj, hyj⟩ | ⟨-, hy⟩)
    · rwa [eq_of_mem_ball_of_mem_ball hθ hi hyj]
    · exact (hy i hi).elim
  · push Not at hy
    simp [hy]

/-- For `2 s`-separated parameters, `ballIndex θ s i₀` is measurable, for every σ-algebra on the
index set. -/
@[fun_prop]
theorem measurable_ballIndex [MeasurableSpace Y] [OpensMeasurableSpace Y] [MeasurableSpace ι]
    {θ : ι → Y} {s : ℝ} (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j)) (i₀ : ι) :
    Measurable (ballIndex θ s i₀) := fun A _ ↦ by
  rw [ballIndex_preimage hθ i₀ A]
  exact (isOpen_biUnion fun i _ ↦ isOpen_ball).measurableSet.union
    ((MeasurableSet.const _).inter
      (isClosed_iInter fun i ↦ isOpen_ball.isClosed_compl).measurableSet)

section NearestIndex

variable [Fintype ι] [Nonempty ι] [LinearOrder ι]

open scoped Classical in
/-- The index of a nearest parameter to `y`: the least `i`, for the linear order of `ι`, such that
`dist y (θ i) ≤ dist y (θ j)` for every `j`. -/
def nearestIndex (θ : ι → Y) (y : Y) : ι :=
  (Finset.univ.filter fun i ↦ ∀ j, dist y (θ i) ≤ dist y (θ j)).min' <| by
    obtain ⟨i, -, hi⟩ :=
      Finset.univ.exists_min_image (fun i ↦ dist y (θ i)) Finset.univ_nonempty
    exact ⟨i, by simpa using hi⟩

open scoped Classical in
theorem nearestIndex_def (θ : ι → Y) (y : Y) :
    nearestIndex θ y = (Finset.univ.filter fun i ↦ ∀ j, dist y (θ i) ≤ dist y (θ j)).min' (by
      obtain ⟨i, -, hi⟩ :=
        Finset.univ.exists_min_image (fun i ↦ dist y (θ i)) Finset.univ_nonempty
      exact ⟨i, by simpa using hi⟩) := (rfl)

/-- `nearestIndex θ y = i` exactly when `θ i` is a nearest parameter to `y` and every index of a
nearest parameter is at least `i`. -/
theorem nearestIndex_eq_iff {θ : ι → Y} {y : Y} {i : ι} :
    nearestIndex θ y = i ↔ (∀ j, dist y (θ i) ≤ dist y (θ j)) ∧
      ∀ j, (∀ k, dist y (θ j) ≤ dist y (θ k)) → i ≤ j := by
  simp [nearestIndex_def, Finset.min'_eq_iff]

/-- `θ (nearestIndex θ y)` is a nearest parameter to `y`. -/
theorem dist_nearestIndex_le (θ : ι → Y) (y : Y) (j : ι) :
    dist y (θ (nearestIndex θ y)) ≤ dist y (θ j) :=
  (nearestIndex_eq_iff.1 rfl).1 j

/-- The nearest parameter to `y` is within twice the distance from `y` to `θ j` of `θ j`. -/
theorem dist_nearestIndex_le_two_mul (θ : ι → Y) (y : Y) (j : ι) :
    dist (θ (nearestIndex θ y)) (θ j) ≤ 2 * dist y (θ j) := by
  calc dist (θ (nearestIndex θ y)) (θ j) ≤ dist y (θ (nearestIndex θ y)) + dist y (θ j) :=
        dist_triangle_left _ _ _
    _ ≤ 2 * dist y (θ j) := by linarith [dist_nearestIndex_le θ y j]

/-- `nearestIndex θ` is measurable, for every σ-algebra on the index set: each fibre is a finite
Boolean combination of the closed sets `{y | dist y (θ j) ≤ dist y (θ k)}`. -/
@[fun_prop]
theorem measurable_nearestIndex [MeasurableSpace Y] [OpensMeasurableSpace Y] [MeasurableSpace ι]
    (θ : ι → Y) : Measurable (nearestIndex θ) := by
  have hmin (j : ι) : MeasurableSet {y | ∀ k, dist y (θ j) ≤ dist y (θ k)} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun k ↦ measurableSet_le
      (continuous_id.dist continuous_const).measurable
      (continuous_id.dist continuous_const).measurable
  refine measurable_to_countable' fun i ↦ ?_
  have hpre : nearestIndex θ ⁻¹' {i} = {y | ∀ k, dist y (θ i) ≤ dist y (θ k)} ∩
      ⋂ j, ({y | ∀ k, dist y (θ j) ≤ dist y (θ k)}ᶜ ∪ {_y | i ≤ j}) := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, nearestIndex_eq_iff, mem_inter_iff,
      mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, imp_iff_not_or]
  rw [hpre]
  exact (hmin i).inter (MeasurableSet.iInter fun j ↦ (hmin j).compl.union (.const _))

end NearestIndex

variable [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace Y] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]

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
