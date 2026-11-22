/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.Analysis.Convex.CCHypersurface.Basic
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Additive-Haar nullity of `c - c` and Lipschitz hypersurfaces

In a finite-dimensional real inner product space `E`, both Lipschitz hypersurfaces and `c - c`
hypersurfaces are Borel measurable graphs over an orthogonal hyperplane `(ℝ ∙ e)ᗮ`, and therefore
have additive-Haar measure zero (`TauCeti.IsLipschitzHypersurface.addHaar_eq_zero`,
`TauCeti.IsCCHypersurface.addHaar_eq_zero`) by `TauCeti.addHaar_setOf_inner_eq_eq_zero`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

section Measurability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E]

/-- Every `c - c` hypersurface is Borel measurable. -/
theorem IsCCHypersurface.measurableSet {s : Set E} (hs : IsCCHypersurface s) :
    MeasurableSet s := hs.isClosed.measurableSet

/-- Every Lipschitz hypersurface is Borel measurable. -/
theorem IsLipschitzHypersurface.measurableSet {s : Set E} (hs : IsLipschitzHypersurface s) :
    MeasurableSet s := hs.isClosed.measurableSet

end Measurability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Every Lipschitz hypersurface has measure zero for any additive Haar measure on `E`. -/
theorem IsLipschitzHypersurface.addHaar_eq_zero (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {s : Set E} (hs : IsLipschitzHypersurface s) : μ s = 0 := by
  have hmeas := hs.measurableSet
  rcases isLipschitzHypersurface_def.1 hs with ⟨e, he, _, h, _, rfl⟩
  exact addHaar_setOf_inner_eq_eq_zero μ he h hmeas

/-- Every `c - c` hypersurface has measure zero for any additive Haar measure on `E`. -/
theorem IsCCHypersurface.addHaar_eq_zero (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    {s : Set E} (hs : IsCCHypersurface s) : μ s = 0 := by
  have hmeas := hs.measurableSet
  rcases isCCHypersurface_def.1 hs with ⟨e, he, f, g, _, _, _, _, rfl⟩
  exact addHaar_setOf_inner_eq_eq_zero μ he (fun y => f y - g y) hmeas

end TauCeti
