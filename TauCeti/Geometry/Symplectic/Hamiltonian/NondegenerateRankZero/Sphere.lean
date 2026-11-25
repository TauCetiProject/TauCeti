/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.NondegenerateRankZero.Manifold
public import TauCeti.Geometry.Symplectic.Manifold.Sphere

/-!
# The poles of the height function on the two-sphere

Let `E` be an oriented real inner product space of dimension three, and give its unit sphere the
symplectic area form `vol(u, ·, ·)` (`Orientation.sphereVolumeForm`). For a unit vector `v`, the
height function `h_v(x) = ⟪x, v⟫` (`TauCeti.sphereHeight`) has exactly the two poles `±v` as
critical points.

Both poles are nondegenerate rank-zero points of `h_v` for the area form
(`Orientation.isNondegenerateRankZeroPoint_sphereHeight_self`,
`Orientation.isNondegenerateRankZeroPoint_sphereHeight_neg`). On a surface, nondegenerate
rank-zero points of a single Hamiltonian are the nondegenerate critical points of Morse theory
(`IsNondegenerate.isNondegenerateRankZeroPoint_iff_isManifoldNondegenerateCriticalPoint`, in the
namespace `TauCeti.SmoothTwoForm`), and the poles are nondegenerate critical points of `h_v`, a
maximum and a minimum.
-/

public section

open Metric Module
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2 + 1)]

open SmoothTwoForm.IsNondegenerate in
/-- The north pole `v` of the unit sphere is a nondegenerate rank-zero point of the height function
`x ↦ ⟪x, v⟫` for the area form of the sphere. -/
theorem _root_.Orientation.isNondegenerateRankZeroPoint_sphereHeight_self
    (o : Orientation ℝ E (Fin (2 + 1))) (v : sphere (0 : E) 1) :
    o.isSymplectic_sphereVolumeForm.isNondegenerate.IsNondegenerateRankZeroPoint
      (sphereHeight v) v :=
  (isNondegenerateRankZeroPoint_iff_isManifoldNondegenerateCriticalPoint
    finrank_euclideanSpace_fin).2 (isManifoldNondegenerateCriticalPoint_sphereHeight_self v)

open SmoothTwoForm.IsNondegenerate in
/-- The south pole `-v` of the unit sphere is a nondegenerate rank-zero point of the height function
`x ↦ ⟪x, v⟫` for the area form of the sphere. -/
theorem _root_.Orientation.isNondegenerateRankZeroPoint_sphereHeight_neg
    (o : Orientation ℝ E (Fin (2 + 1))) (v : sphere (0 : E) 1) :
    o.isSymplectic_sphereVolumeForm.isNondegenerate.IsNondegenerateRankZeroPoint
      (sphereHeight v) (-v) :=
  (isNondegenerateRankZeroPoint_iff_isManifoldNondegenerateCriticalPoint
    finrank_euclideanSpace_fin).2 (isManifoldNondegenerateCriticalPoint_sphereHeight_neg v)

end TauCeti
