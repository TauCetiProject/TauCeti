/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Riccardo Brasca
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Sphere.Equator

/-!
# Intersections of great hyperspheres

`TauCeti.nonempty_sphereEquator_inter_sphereEquator_euclideanSpace_fin` specializes the general
equator intersection theorem to `S^(n+1)`: two great hyperspheres meet for `n ≥ 1`.
-/

public section

namespace TauCeti

/-- The great hyperspheres with normals `a` and `b` in `S^(n+1)` intersect for `n ≥ 1`.
The defining normals may be equal or zero. -/
theorem nonempty_sphereEquator_inter_sphereEquator_euclideanSpace_fin (n : ℕ) (hn : 0 < n)
    (a b : EuclideanSpace ℝ (Fin (n + 2))) :
    (sphereEquator a ∩ sphereEquator b).Nonempty := by
  apply nonempty_sphereEquator_inter_sphereEquator
  rw [finrank_euclideanSpace_fin]
  omega

end TauCeti
