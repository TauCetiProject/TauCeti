/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Euclidean.Inversion
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Inversion in a sphere reverses orientation

Away from its centre, the derivative of the inversion of a finite-dimensional real inner product
space `E` in a sphere of nonzero radius has negative determinant
(`EuclideanGeometry.det_fderiv_inversion_neg`). So the inversion reverses every orientation of `E`
at every point other than the centre
(`TauCeti.Manifold.Orientation.isOrientationReversingAt_inversion`).

This is why the connected sum, which glues two punctured balls by the inversion, joins the
orientations of its summands only when the two balls induce opposite orientations of `E`.

## Main results

* `TauCeti.Manifold.Orientation.isOrientationReversingAt_inversion`: the inversion reverses every
  orientation of `E` away from the centre.
-/

public section

open Module EuclideanGeometry
open scoped Manifold

namespace TauCeti.Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

/-- **Inversion in a sphere reverses orientation.** For every orientation `o` of the
finite-dimensional real inner product space `E`, viewed as a manifold, the inversion in the sphere
of centre `c` and nonzero radius `R` reverses `o` at every point `v ≠ c`. -/
theorem isOrientationReversingAt_inversion (o : Manifold.Orientation 𝓘(ℝ, E) E ι) {c v : E}
    {R : ℝ} (hR : R ≠ 0) (hv : v ≠ c) : IsOrientationReversingAt o o (inversion c R) v :=
  isOrientationReversingAt_of_det_fderiv_neg o (det_fderiv_inversion_neg hR hv)

end TauCeti.Manifold.Orientation
