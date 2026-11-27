/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.InvariantProbabilities

/-!
# Empirical measures of orbits

* `TauCeti.integral_empiricalMeasure_eq_birkhoffAverage_real`: Mathlib's
  `MeasureTheory.integral_empiricalMeasure_eq_birkhoffaverage` with the Birkhoff average taken
  over `ℝ` rather than `NNReal`.
* `TauCeti.norm_integral_comp_sub_integral_empiricalMeasure_le`: a uniform, quantitative form of
  Mathlib's `MeasureTheory.tendsto_integral_comp_sub_integral_empiricalMeasure_of_isBoundedUnder`:
  for a function `g` bounded by `C`, the integrals of `g ∘ T` and `g` against the empirical
  measure of an orbit of length `n + 1` differ by at most `2 * C / (n + 1)`, whatever the starting
  point.
* `TauCeti.mem_invariantProbabilities_of_mapClusterPt_empiricalMeasure`: for a continuous map,
  a cluster point along a filter `F ≤ atTop` of the empirical measures of orbits of lengths
  `n + 1` with arbitrary starting points `x n` is invariant, as in Mathlib's proof of the
  Krylov–Bogolyubov theorem.
-/

public section

open MeasureTheory Filter Topology

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integral of `g` against the empirical measure of the orbit of `x` of length `n + 1` is the
real Birkhoff average of `g` at `x`. -/
theorem integral_empiricalMeasure_eq_birkhoffAverage_real [CompleteSpace E] (T : X → X)
    (g : X → E) (x : X) (n : ℕ) :
    ∫ y, g y ∂(empiricalMeasure T x n) = birkhoffAverage ℝ T g (n + 1) x := by
  rw [integral_empiricalMeasure_eq_birkhoffaverage,
    birkhoffAverage_apply_congr_ring (R := NNReal) ℝ]

/-- The empirical measure of the orbit of `x` of length `n + 1` integrates `g ∘ T - g` to
`(g (T^[n + 1] x) - g x) / (n + 1)`, which is at most `2 * C / (n + 1)` in norm when `g` is
bounded by `C`. -/
theorem norm_integral_comp_sub_integral_empiricalMeasure_le (T : X → X) {g : X → E} {C : ℝ}
    (hg : ∀ y, ‖g y‖ ≤ C) (x : X) (n : ℕ) :
    ‖(∫ y, (g ∘ T) y ∂(empiricalMeasure T x n)) - ∫ y, g y ∂(empiricalMeasure T x n)‖ ≤
      2 * C / (n + 1) := by
  by_cases hE : CompleteSpace E
  swap
  · rw [integral_of_not_completeSpace hE, integral_of_not_completeSpace hE, sub_zero, norm_zero]
    have := (norm_nonneg (g x)).trans (hg x)
    positivity
  rw [integral_empiricalMeasure_eq_birkhoffAverage_real,
    integral_empiricalMeasure_eq_birkhoffAverage_real, birkhoffAverage_comp_apply,
    ← dist_eq_norm, dist_birkhoffAverage_apply_birkhoffAverage]
  push_cast
  gcongr
  have h1 := hg (T^[n + 1] x)
  have h2 := hg x
  exact (dist_le_norm_add_norm _ _).trans (by linarith)

/-- For a continuous map `T` of a space with `HasOuterApproxClosed` (for instance a
pseudometrizable space), a cluster point along a filter `F ≤ atTop` of the empirical measures of
the orbits of `x n` of lengths `n + 1` is a `T`-invariant probability measure. -/
theorem mem_invariantProbabilities_of_mapClusterPt_empiricalMeasure [TopologicalSpace X]
    [BorelSpace X] [HasOuterApproxClosed X] {T : X → X} (hT : Continuous T) {F : Filter ℕ}
    (hF : F ≤ atTop) {x : ℕ → X} {ν : ProbabilityMeasure X}
    (hν : MapClusterPt ν F fun n ↦ (empiricalMeasure T (x n) n).toProbabilityMeasure) :
    ν ∈ invariantProbabilities T := by
  refine (mem_invariantProbabilities_iff_map_eq hT.measurable).mpr
    (ProbabilityMeasure.toMeasure_injective ?_)
  rw [ProbabilityMeasure.toMeasure_map]
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g ↦ ?_
  rw [integral_map hT.aemeasurable g.continuous.aestronglyMeasurable]
  refine ProbabilityMeasure.integral_comp_eq_integral_of_mapClusterPt hT hν ?_
  have h0 : Tendsto (fun n : ℕ ↦ 2 * ‖g‖ / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    refine ((tendsto_const_div_atTop_nhds_zero_nat (2 * ‖g‖)).comp
      (tendsto_add_atTop_nat 1)).congr fun n ↦ ?_
    simp
  simp only [Measure.coe_toProbabilityMeasure]
  exact (squeeze_zero_norm (fun n ↦ norm_integral_comp_sub_integral_empiricalMeasure_le T
    g.norm_coe_le_norm (x n) n) h0).mono_left hF

end TauCeti
