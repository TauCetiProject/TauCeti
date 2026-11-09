/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Symplectic.Manifold.Surface

/-!
# The volume form of a two-sphere is symplectic

Let `E` be an oriented real inner product space of dimension three. The volume form
`vol(u, ·, ·)` of its unit sphere (`Orientation.sphereVolumeForm`) is a nowhere-vanishing two-form
on a surface, so it is closed and nondegenerate
(`TauCeti.SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two`): the two-sphere is a
symplectic manifold.

## Main results

* `Orientation.isSymplectic_sphereVolumeForm`: the volume form of a two-sphere is symplectic.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford University
  Press, 2017, Section 3.1 (area forms on surfaces).
-/

public section

open Metric Module
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2 + 1)]

/-- **The volume form of a two-sphere is symplectic.** On the unit sphere of an oriented
three-dimensional real inner product space, the volume form `vol(u, ·, ·)` is a nowhere-vanishing
two-form on a surface, hence closed and nondegenerate. -/
theorem _root_.Orientation.isSymplectic_sphereVolumeForm (o : Orientation ℝ E (Fin (2 + 1))) :
    SmoothTwoForm.IsSymplectic o.sphereVolumeForm :=
  (SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two finrank_euclideanSpace_fin).2
    o.sphereVolumeForm_apply_ne_zero

end TauCeti
