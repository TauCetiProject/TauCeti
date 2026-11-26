/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Ball
public import TauCeti.Analysis.BoundedVariation.RelativeSmoothApproximation
public import TauCeti.Analysis.BoundedVariation.Space
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The exterior of a ball: finite perimeter without bounded variation

Let `E` be a nontrivial finite-dimensional real inner product space with an additive Haar measure
`μ`, of dimension `n`, and let `s = (closedBall c r)ᶜ` with `r > 0`. This example shows that the
relative smooth approximation handles a set of infinite volume and finite perimeter:

* `s` has infinite volume (`MeasureTheory.Measure.addHaar_compl_eq_top_of_isBounded`) and, like
  the ball (`TauCeti.perimeter_compl`, `TauCeti.perimeter_closedBall`), perimeter
  `n r^{n-1} μ(B(0, 1))`, which is `n ω_n` for the unit ball when `μ` is Lebesgue measure;
* its indicator is not in `BV(E)` (`not_memBV_indicator_compl_closedBall`), so a definition of
  finite perimeter as membership of the indicator in `BV` would exclude it;
* the relative smooth approximation
  `MeasureTheory.NullMeasurableSet.exists_contDiffOn_perimeter_approximation` covers it, with
  perimeters converging to that finite value (`exists_perimeter_approximation`), while the
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

/-- The indicator of the exterior of a closed ball is not of bounded variation on `E`: it is not
integrable. -/
theorem not_memBV_indicator_compl_closedBall [Nontrivial E] :
    ¬ MemBV μ ⊤ ((closedBall c r)ᶜ.indicator 1) := by
  rw [memBV_iff]
  rintro ⟨hint, -⟩
  have h : IntegrableOn (1 : E → ℝ) (closedBall c r)ᶜ μ :=
    (integrable_indicator_iff measurableSet_closedBall.compl).1 (by simpa using hint)
  rw [Pi.one_def, integrableOn_const_iff] at h
  simp [μ.addHaar_compl_eq_top_of_isBounded isBounded_closedBall] at h

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
  rw [← perimeter_closedBall (c := c) hr, ← perimeter_compl]
  exact measurableSet_closedBall.compl.nullMeasurableSet.exists_contDiffOn_perimeter_approximation ⊤

end TauCeti.Examples.RelativeApproximationExterior
