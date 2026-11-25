/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Ball
public import TauCeti.Analysis.BoundedVariation.RelativeSmoothApproximation
public import TauCeti.Analysis.BoundedVariation.Space

/-!
# The exterior of a ball: finite perimeter without bounded variation

Let `E` be a nontrivial finite-dimensional real inner product space with an additive Haar measure
`μ`, of dimension `n`, and let `s = (closedBall c r)ᶜ` with `r > 0`. This is the first Check of
§5.1 of `TauCetiRoadmap/GeometricMeasureTheory/README.md`:

* `s` has infinite volume (`measure_compl_closedBall`) and perimeter `n r^{n-1} μ(B(0, 1))`
  (`perimeter_compl_closedBall`), which is `n ω_n` for the unit ball;
* its indicator is not in `BV(E)` (`not_memBV_indicator_compl_closedBall`), so a definition of
  finite perimeter as membership of the indicator in `BV` would exclude it;
* the relative smooth approximation `TauCeti.exists_contDiffOn_perimeter_approximation` covers it,
  with perimeters converging to that finite value (`exists_perimeter_approximation`), while the
  whole-space approximation `MeasureTheory.NullMeasurableSet.exists_smooth_perimeter_approximation`
  needs finite volume.
-/

@[expose] public section

open MeasureTheory Set Metric Filter Module TopologicalSpace Function
open scoped ENNReal Topology ContDiff symmDiff

namespace TauCeti.Examples.RelativeApproximationExterior

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {c : E} {r : ℝ}

/-- The exterior of a closed ball has infinite volume. -/
theorem measure_compl_closedBall [Nontrivial E] : μ (closedBall c r)ᶜ = ⊤ := by
  rw [measure_compl measurableSet_closedBall measure_closedBall_lt_top.ne,
    measure_univ_of_isAddLeftInvariant μ]
  exact ENNReal.top_sub measure_closedBall_lt_top.ne

/-- The exterior of a closed ball of radius `r > 0` has the perimeter of the ball,
`n r^{n-1} μ(B(0, 1))`. -/
theorem perimeter_compl_closedBall (hr : 0 < r) :
    perimeter μ ⊤ (closedBall c r)ᶜ =
      finrank ℝ E * ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * μ (ball 0 1) := by
  rw [perimeter_compl, perimeter_closedBall hr]

/-- The exterior of a closed ball has finite perimeter. -/
theorem perimeter_compl_closedBall_lt_top (hr : 0 < r) : perimeter μ ⊤ (closedBall c r)ᶜ < ⊤ := by
  rw [perimeter_compl_closedBall hr]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ENNReal.ofReal_lt_top)
    measure_ball_lt_top

/-- The indicator of the exterior of a closed ball is not of bounded variation on `E`: it is not
integrable. -/
theorem not_memBV_indicator_compl_closedBall [Nontrivial E] :
    ¬ MemBV μ ⊤ ((closedBall c r)ᶜ.indicator 1) := by
  rw [memBV_iff]
  rintro ⟨hint, -⟩
  have h : IntegrableOn (1 : E → ℝ) (closedBall c r)ᶜ μ :=
    (integrable_indicator_iff measurableSet_closedBall.compl).1 (by simpa using hint)
  rw [Pi.one_def, integrableOn_const_iff] at h
  simp [measure_compl_closedBall] at h

/-- **The relative approximation covers the exterior of a ball.** There are functions smooth on
`E` with regular levels in `(0, 1)` whose superlevel sets converge to the exterior of the ball in
measure and whose perimeters converge to its finite perimeter. -/
theorem exists_perimeter_approximation (hr : 0 < r) :
    ∃ (u : ℕ → E → ℝ) (t : ℕ → ℝ),
      (∀ n, ContDiffOn ℝ ∞ (u n) (⊤ : Opens E) ∧ t n ∈ Ioo 0 1 ∧
        ∀ x ∈ (⊤ : Opens E), u n x = t n → Surjective (fderiv ℝ (u n) x)) ∧
      Tendsto (fun n ↦ μ (({x | t n < u n x} ∆ (closedBall c r)ᶜ) ∩ (⊤ : Opens E))) atTop
        (𝓝 0) ∧
      Tendsto (fun n ↦ perimeter μ ⊤ {x | t n < u n x}) atTop
        (𝓝 (finrank ℝ E * ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * μ (ball 0 1))) := by
  rw [← perimeter_compl_closedBall (c := c) hr]
  exact exists_contDiffOn_perimeter_approximation
    measurableSet_closedBall.compl.nullMeasurableSet ⊤

end TauCeti.Examples.RelativeApproximationExterior
