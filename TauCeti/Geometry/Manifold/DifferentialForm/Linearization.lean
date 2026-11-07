/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization

/-!
# Linearization of differential forms as bundle sections

The derivative of a differential form's preferred fibre coordinates is the derivative of
`RoughForm.inChartAt`. Together with `TauCeti.surjective_sectionLinearization_iff`, this
identifies regular zeros of a form with surjectivity of its coordinate derivative.
The result applies to forms of every degree, without a closedness assumption.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 6 (transversality).
-/

public section

open Bundle Filter Set
open scoped Manifold Topology ContDiff

namespace TauCeti.RoughForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {φ : RoughForm I M F k} {x : M}

/-- The derivative of a form's preferred fibre coordinates equals the derivative of its
chart expression. -/
theorem mvfderiv_trivializationAt_eq_fderiv_inChartAt
    (hφ : DifferentiableAt ℝ (φ.inChartAt x) (extChartAt I x x)) :
    mvfderiv I (fun y ↦ (trivializationAt (E [⋀^Fin k]→L[ℝ] F)
      (fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] F) x ⟨y, φ y⟩).2) x =
      fderiv ℝ (φ.inChartAt x) (extChartAt I x x) := by
  have hs := mdifferentiableAt_form_of_differentiableWithinAt_inChartAt_self
    hφ.differentiableWithinAt
  have hc := (mdifferentiableAt_section I φ).mp hs
  have heq := φ.trivializationAt_snd_eventuallyEq_inChartAt x
  rw [I.range_eq_univ, nhdsWithin_univ] at heq
  rw [hc.mvfderiv, I.range_eq_univ, fderivWithin_univ]
  -- The tangent space at the source is the model space; the coefficient bundle is trivial.
  convert! heq.fderiv_eq using 1

end TauCeti.RoughForm
