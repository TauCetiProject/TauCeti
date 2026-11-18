/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Complex.Orientation

/-!
# A real Euclidean model for a complex curve

The real orthonormal basis `(1, i)` identifies the complex chart model with the real
Euclidean plane. This keeps the chart carrier `ℂ` while making its tangent model the
same real vector space as the round two-sphere.
-/

@[expose] public section

noncomputable section

open Complex
open scoped ContDiff Manifold

namespace TauCeti

/-- The complex-line chart model transported to the real Euclidean plane. -/
def complexPlaneRealModel : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) ℂ :=
  𝓘(ℝ, ℂ).transContinuousLinearEquiv
    orthonormalBasisOneI.repr.toContinuousLinearEquiv

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ∞ X]

/-- A smooth complex curve also has smooth real Euclidean two-dimensional charts. -/
instance isManifold_complexPlaneRealModel : IsManifold complexPlaneRealModel ∞ X := by
  unfold complexPlaneRealModel
  infer_instance

variable [IsManifold 𝓘(ℂ) 1 X]

/-- The complex orientation read in the real Euclidean two-dimensional model. -/
def complexPlaneOrientation : Manifold.Orientation complexPlaneRealModel X (Fin 2) := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let o := (complexManifoldOrientation ℂ X).transContinuousLinearEquiv e
  exact o.reindex (finCongr (by simp))

end TauCeti
