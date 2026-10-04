/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Inversion commutes with isometries and reverses orientation

Inversion in a sphere (`EuclideanGeometry.inversion c R`) is defined from the distance to the
centre and the vector from the centre, both of which an affine isometry preserves. So an affine
isometry carries the inversion in a sphere to the inversion in the image sphere, and a linear
isometry fixing the centre commutes with the inversion. This is the compatibility used to compare
inversion charts of the closed unit balls of two inner product spaces along a linear isometry.

For a nonzero radius `R`, the derivative of the inversion at a point `x ≠ c` is a positive
multiple of the reflection in the hyperplane orthogonal to `x - c` (`hasFDerivAt_inversion`), so
in finite dimension its determinant is negative: inversion reverses orientation. A transition
between two inversion charts whose linear isometries lie in the same orientation class is a
composite of two inversions and a linear isometry of positive determinant, so it preserves
orientation. This is how the inversion charts of the closed unit ball attached to the isometries
of one orientation class give an oriented atlas.

## Main results

* `AffineIsometry.map_inversion`: an affine isometry carries inversion in the sphere of centre `c`
  and radius `R` to inversion in the sphere of centre `f c` and radius `R`.
* `LinearIsometry.map_inversion`: the same for a linear isometry.
* `EuclideanGeometry.det_fderiv_inversion_neg`: the derivative of an inversion has negative
  determinant.
-/

public section

open EuclideanGeometry

variable {V V₂ P P₂ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂]
  [NormedAddTorsor V₂ P₂]

/-- An affine isometry carries the inversion in the sphere of centre `c` and radius `R` to the
inversion in the sphere of centre `f c` and radius `R`. -/
theorem AffineIsometry.map_inversion (f : P →ᵃⁱ[ℝ] P₂) (c : P) (R : ℝ) (x : P) :
    f (inversion c R x) = inversion (f c) R (f x) := by
  simp only [inversion, f.map_vadd, f.linearIsometry.map_smul, f.map_vsub, f.dist_map]

/-- A linear isometry carries the inversion in the sphere of centre `c` and radius `R` to the
inversion in the sphere of centre `f c` and radius `R`. -/
theorem LinearIsometry.map_inversion (f : V →ₗᵢ[ℝ] V₂) (c : V) (R : ℝ) (x : V) :
    f (inversion c R x) = inversion (f c) R (f x) :=
  f.toAffineIsometry.map_inversion c R x

namespace EuclideanGeometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Inversion reverses orientation**: away from its centre, the derivative of the inversion in a
sphere of nonzero radius has negative determinant. The derivative is `(R / dist x c) ^ 2` times
the reflection in the hyperplane orthogonal to `x - c`, whose determinant is `-1`. -/
theorem det_fderiv_inversion_neg {c x : F} {R : ℝ} (hR : R ≠ 0) (hx : x ≠ c) :
    LinearMap.det (fderiv ℝ (inversion c R) x : F →ₗ[ℝ] F) < 0 := by
  have hK : Module.finrank ℝ (ℝ ∙ (x - c))ᗮᗮ = 1 := by
    rw [Submodule.orthogonal_orthogonal, finrank_span_singleton (sub_ne_zero.2 hx)]
  have hpos : 0 < (R / dist x c) ^ 2 := by
    have : R / dist x c ≠ 0 := div_ne_zero hR (dist_ne_zero.2 hx)
    positivity
  rw [(hasFDerivAt_inversion hx).fderiv, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul]
  -- The reflection, coerced to a continuous linear map and then to a linear map, is its
  -- underlying linear map.
  have hrefl : (((ℝ ∙ (x - c))ᗮ.reflection : F →L[ℝ] F) : F →ₗ[ℝ] F) =
      (ℝ ∙ (x - c))ᗮ.reflection.toLinearMap := (rfl)
  rw [hrefl, Submodule.det_reflection, hK, pow_one, mul_neg_one, neg_lt_zero]
  exact pow_pos hpos _

end EuclideanGeometry
