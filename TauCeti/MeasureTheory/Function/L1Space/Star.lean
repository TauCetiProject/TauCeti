/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrability of the pointwise `star`

Since `star` preserves norms in a normed star group, a function is integrable exactly when its
pointwise `star` is. For complex-valued functions this says that a function and its complex
conjugate are integrable together.

## Main statements

* `MeasureTheory.integrable_star_iff`: `star f` is integrable if and only if `f` is.
-/

public section

namespace MeasureTheory

/-- A function into a normed star group is integrable exactly when its pointwise `star` is, since
`star` preserves norms. -/
theorem integrable_star_iff {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    [StarAddMonoid F] [NormedStarGroup F] {μ : Measure X} {f : X → F} :
    Integrable (star f) μ ↔ Integrable f μ := by
  have key (g : X → F) (hg : Integrable g μ) : Integrable (star g) μ :=
    hg.congr' (continuous_star.comp_aestronglyMeasurable hg.1)
      (.of_forall fun x ↦ (norm_star (g x)).symm)
  exact ⟨fun h ↦ star_star f ▸ key _ h, key f⟩

end MeasureTheory
