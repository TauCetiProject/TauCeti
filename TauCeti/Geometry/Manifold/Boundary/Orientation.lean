/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.VectorField.Regularity
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

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
open Bundle
open scoped Manifold ContDiff

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

/-- A smooth vector field is outward-pointing when each of its boundary values points out of the
half-space. Smoothness is recorded as regularity of the corresponding tangent-bundle section, so
the predicate does not depend on a choice of tangent-bundle trivialization. -/
def IsOutwardPointingField {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) ∞ M]
    (V : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x) : Prop :=
  ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% V) ∧
    ∀ x ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing x (V x)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]
  {V : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x}

/-- Characterization of a smooth outward-pointing field by its smoothness and boundary values. -/
@[grind =]
theorem isOutwardPointingField_iff :
    IsOutwardPointingField V ↔
      ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% V) ∧
        ∀ x ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing x (V x) :=
  Iff.rfl

namespace IsOutwardPointingField

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]
  {V : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x}

/-- Construct a smooth outward-pointing field from its smoothness and boundary values. -/
theorem intro
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% V))
    (hout : ∀ x ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing x (V x)) :
    IsOutwardPointingField V :=
  ⟨hV, hout⟩

/-- The field component of an outward-pointing field is smooth. -/
theorem contMDiff (hV : IsOutwardPointingField V) :
    ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (T% V) :=
  hV.1

/-- Every boundary value of an outward-pointing field points out. -/
theorem isOutwardPointing (hV : IsOutwardPointingField V) {x : M}
    (hx : x ∈ (𝓡∂ (n + 1)).boundary M) :
    IsOutwardPointing x (V x) :=
  hV.2 x hx

/-- The sum of two smooth outward-pointing fields is outward-pointing. -/
theorem add {W : ∀ x : M, TangentSpace (𝓡∂ (n + 1)) x}
    (hV : IsOutwardPointingField V) (hW : IsOutwardPointingField W) :
    IsOutwardPointingField (fun x ↦ V x + W x) := by
  refine ⟨hV.contMDiff.add_section hW.contMDiff, ?_⟩
  intro x hx
  exact (hV.isOutwardPointing hx).add (hW.isOutwardPointing hx)

/-- Multiplication by a smooth positive scalar preserves an outward-pointing field. -/
theorem smul {f : M → ℝ} (hV : IsOutwardPointingField V)
    (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ∞ f)
    (hpos : ∀ x ∈ (𝓡∂ (n + 1)).boundary M, 0 < f x) :
    IsOutwardPointingField (fun x ↦ f x • V x) := by
  refine ⟨hf.smul_section hV.1, fun x hx ↦ (hV.2 x hx).smul_pos (hpos x hx)⟩

end IsOutwardPointingField

/-- The constant negative normal field on the standard Euclidean half-space. -/
noncomputable def standardOutwardVectorField (n : ℕ) :
    ∀ x : EuclideanHalfSpace (n + 1), TangentSpace (𝓡∂ (n + 1)) x :=
  fun _ ↦ -EuclideanSpace.single 0 1

/-- The standard field has constant negative zeroth coordinate. -/
@[simp]
theorem standardOutwardVectorField_apply (n : ℕ)
    (x : EuclideanHalfSpace (n + 1)) :
    standardOutwardVectorField n x = -EuclideanSpace.single 0 1 := by
  rfl

/-- The standard negative normal field is smooth as a tangent-bundle section. -/
theorem contMDiff_standardOutwardVectorField (n : ℕ) :
    ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (T% (standardOutwardVectorField n)) := by
  have h := contMDiff_tangentBundleModelSpaceHomeomorph_symm_prodMk_const
    (𝓡∂ (n + 1)) (-EuclideanSpace.single 0 1) ∞
  apply h.congr
  intro x
  simp only [tangentBundleModelSpaceHomeomorph_coe_symm, TotalSpace.toProd]
  rfl

/-- The standard Euclidean half-space has a smooth outward-pointing field. -/
theorem isOutwardPointingField_standard_halfSpace (n : ℕ) :
    IsOutwardPointingField (standardOutwardVectorField n) := by
  refine ⟨contMDiff_standardOutwardVectorField n, fun x hx ↦ ?_⟩
  exact isOutwardPointing_standard_halfSpace (n := n) (x := x) hx

end TauCeti
