/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.Measure

/-!
# Boundary restriction and null sets on manifolds

This file supplies the measure-theoretic and differential-form interfaces needed at the boundary of
an oriented manifold with boundary. The imported manifold measure API defines null sets chartwise
and proves boundary nullness
for finite-dimensional models with corners. Rough forms on a manifold with boundary restrict to the
boundary manifold by pulling back along the subtype inclusion.
-/

public section

open Set
open MeasureTheory
open scoped Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) 1 M]
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {j : ℕ}

/-- Restrict a rough form on a half-space manifold to its boundary manifold by pulling it back
along the subtype inclusion. -/
noncomputable def boundaryRestriction (φ : RoughForm (𝓡∂ (n + 1)) M F j) :
    RoughForm 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary M) F j :=
  mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) Subtype.val φ

/-- Evaluation of boundary restriction is evaluation of the original form on the tangent map of the
boundary inclusion. -/
@[simp]
theorem boundaryRestriction_apply (φ : RoughForm (𝓡∂ (n + 1)) M F j)
    (x : (𝓡∂ (n + 1)).boundary M) (v : Fin j → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    boundaryRestriction φ x v = φ x (fun i ↦ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (𝓡∂ (n + 1)) Subtype.val x (v i)) := by
  simp [boundaryRestriction]

end TauCeti
