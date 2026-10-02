/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Geometry.Euclidean.Inversion.Basic

/-!
# Inversion commutes with isometries

Inversion in a sphere (`EuclideanGeometry.inversion c R`) is defined from the distance to the
centre and the vector from the centre, both of which an affine isometry preserves. So an affine
isometry carries the inversion in a sphere to the inversion in the image sphere, and a linear
isometry fixing the centre commutes with the inversion. This is the compatibility used to compare
inversion charts of the closed unit balls of two inner product spaces along a linear isometry.

## Main results

* `AffineIsometry.map_inversion`: an affine isometry carries inversion in the sphere of centre `c`
  and radius `R` to inversion in the sphere of centre `f c` and radius `R`.
* `LinearIsometry.map_inversion`: the same for a linear isometry.
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
