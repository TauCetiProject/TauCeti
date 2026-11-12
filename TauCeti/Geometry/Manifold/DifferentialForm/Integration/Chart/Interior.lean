/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Integration in a chart containing the interior

A convex model's boundary has Haar measure zero. A chart containing every intrinsic interior
point therefore computes the whole top-form integral, even if it omits endpoints or corner faces.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {k : ℕ}

/-- A preferred chart containing all intrinsic interior points computes the actual integral.
No regularity of the integrable form or measurable structure on the manifold is required. -/
theorem integralTopForm_eq_chartIntegral_of_interior_subset
    (l : Manifold.OrientationLift I M (Fin k)) (φ : RoughForm I M ℝ k)
    (hi : IntegrableTopForm φ) (α : M)
    (hs : I.interior M ⊆ (extChartAt I α).source) :
    integralTopForm (Manifold.Orientation.mk l) φ = l.chartIntegral φ α := by
  apply integralTopForm_eq_chartIntegral_of_ae_support l φ hi α
  apply (isNullSet_boundary (I := I)).mono
  intro x hx
  exact (I.isBoundaryPoint_iff_not_isInteriorPoint x).mpr (fun hi ↦ hx.2 (hs hi))

end TauCeti
