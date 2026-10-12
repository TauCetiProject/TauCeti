/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts

/-!
# Outward-pointing vectors at the boundary

For a manifold modeled on Mathlib's Euclidean half-space, this file records the sign convention
for an outward tangent vector.  Mathlib puts the boundary coordinate in slot `0`; outward vectors
therefore have a negative slot-`0` derivative.  The definition uses the preferred chart through
`mfderiv`; coordinate independence requires suitable differentiable chart compatibility and an
invariance theorem.  This is the interface used by the boundary orientation and Stokes
constructions.

The sign convention follows J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition
15.33, adapted to Mathlib's convention that the constrained coordinate is in slot `0`.

The standard half-space supplies a concrete witness: the constant negative first-coordinate
vector is outward at every boundary point.
-/

public section

open Set
open scoped Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- A tangent vector at a boundary point points outward when its preferred half-space coordinate
has negative derivative.  The zeroth coordinate is the constrained coordinate of
`EuclideanHalfSpace`; this sign convention agrees with the outward-first boundary orientation. -/
def IsOutwardPointing (x : M) (v : TangentSpace (𝓡∂ (n + 1)) x) : Prop :=
  x ∈ (𝓡∂ (n + 1)).boundary M ∧
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (extChartAt (𝓡∂ (n + 1)) x x)
      (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (extChartAt (𝓡∂ (n + 1)) x) x v)) 0 < 0

/-- An outward-pointing vector is based at the boundary, with negative zeroth coordinate
derivative in the preferred half-space chart. -/
@[grind =]
theorem isOutwardPointing_iff {x : M} {v : TangentSpace (𝓡∂ (n + 1)) x} :
    IsOutwardPointing x v ↔
      x ∈ (𝓡∂ (n + 1)).boundary M ∧
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (extChartAt (𝓡∂ (n + 1)) x x)
          (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
            (extChartAt (𝓡∂ (n + 1)) x) x v)) 0 < 0 := Iff.rfl

namespace IsOutwardPointing

/-- An outward-pointing vector is based at a boundary point. -/
theorem mem_boundary {x : M} {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : IsOutwardPointing x v) : x ∈ (𝓡∂ (n + 1)).boundary M :=
  isOutwardPointing_iff.mp hv |>.1

/-- The preferred-chart derivative of an outward-pointing vector is negative in slot `0`. -/
theorem coordinate_deriv_neg {x : M} {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : IsOutwardPointing x v) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (extChartAt (𝓡∂ (n + 1)) x x)
      (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (extChartAt (𝓡∂ (n + 1)) x) x v)) 0 < 0 :=
  isOutwardPointing_iff.mp hv |>.2

/-- Positive rescaling preserves the outward half-space of tangent vectors. -/
theorem smul_pos {x : M} {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : IsOutwardPointing x v) {c : ℝ} (hc : 0 < c) :
    IsOutwardPointing x (c • v) := by
  rcases hv with ⟨hx, hv⟩
  refine ⟨hx, ?_⟩
  rw [ContinuousLinearMap.map_smul, map_smul]
  simpa [smul_eq_mul] using mul_neg_of_pos_of_neg hc hv

/-- The sum of two outward vectors is outward. -/
theorem add {x : M} {v w : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : IsOutwardPointing x v) (hw : IsOutwardPointing x w) :
    IsOutwardPointing x (v + w) := by
  rcases hv with ⟨hx, hv⟩
  rcases hw with ⟨-, hw⟩
  refine ⟨hx, ?_⟩
  rw [ContinuousLinearMap.map_add, map_add]
  simpa using add_neg hv hw

/-- An outward vector is nonzero. -/
theorem ne_zero {x : M} {v : TangentSpace (𝓡∂ (n + 1)) x}
    (hv : IsOutwardPointing x v) : v ≠ 0 := by
  intro hzero
  subst hzero
  rcases hv with ⟨-, hv⟩
  rw [ContinuousLinearMap.map_zero, map_zero] at hv
  exact (lt_irrefl 0) (by simp at hv)

end IsOutwardPointing

/-- On the standard half-space, the constant vector `-e₀` is outward at every boundary point. -/
theorem isOutwardPointing_standard_halfSpace
    {x : EuclideanHalfSpace (n + 1)}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary (EuclideanHalfSpace (n + 1))) :
    IsOutwardPointing (n := n) x (-EuclideanSpace.single 0 1) := by
  refine ⟨hx, ?_⟩
  rw [mfderiv_extChartAt_self]
  -- The tangent space of the model space is definitionally the model space, and
  -- `NormedSpace.fromTangentSpace` is its canonical definitional identification.
  change (-EuclideanSpace.single (𝕜 := ℝ) 0 1) 0 < 0
  simp

end TauCeti
