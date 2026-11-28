/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.CutByBall.Basic
public import TauCeti.Geometry.Euclidean.Volume.Polar

/-!
# Cutting a set by a ball: the Hausdorff form

Let `E` be a finite-dimensional real inner product space of dimension `n`, with its volume, and
let `s ⊆ E` be Lebesgue-measurable. For every centre `x₀` and almost every radius `r > 0`, cutting
`s` by the ball `ball x₀ r` adds at most the `(n - 1)`-dimensional Hausdorff measure of the slice of
`s` by the sphere:

`P(s ∩ ball x₀ r) ≤ P(s; ball x₀ r) + Hⁿ⁻¹(s ∩ sphere x₀ r)` in `[0, ∞]`

(`TauCeti.ae_perimeter_inter_ball_le_add_euclideanHausdorffMeasure`). This is the truncation
inequality for perimeter (Maggi, Lemma 15.12). It combines the estimate
`P(s ∩ ball x₀ r) ≤ P(s; ball x₀ r) + m'(r)`, where `m(ρ) = |s ∩ ball x₀ ρ|`
(`TauCeti.ae_perimeter_inter_ball_le`), with polar integration, which identifies `m'(r)` with
`Hⁿ⁻¹(s ∩ sphere x₀ r)` at almost every radius (`TauCeti.ae_hasDerivAt_measureReal_inter_ball`).
Neither finite perimeter nor finite volume of `s` is assumed.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 15,
  Lemma 15.12 (intersections of sets of finite perimeter with balls).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {s : Set E}

/-- **Cutting by a ball, with Hausdorff measure of the slice.** For a Lebesgue-measurable `s` and
almost every radius `r`,

`P(s ∩ ball x₀ r) ≤ P(s; ball x₀ r) + Hⁿ⁻¹(s ∩ sphere x₀ r)`. -/
theorem ae_perimeter_inter_ball_le_add_euclideanHausdorffMeasure
    (hs : NullMeasurableSet s volume) (x₀ : E) :
    ∀ᵐ r, perimeter volume ⊤ (s ∩ ball x₀ r) ≤
      perimeter volume ⟨ball x₀ r, isOpen_ball⟩ s + μHE[finrank ℝ E - 1] (s ∩ sphere x₀ r) := by
  filter_upwards [ae_perimeter_inter_ball_le hs x₀, ae_hasDerivAt_measureReal_inter_ball x₀ hs]
    with r hP hm
  rw [hm.deriv, measureReal_def] at hP
  exact hP.trans (add_le_add_right ENNReal.ofReal_toReal_le _)

end TauCeti
