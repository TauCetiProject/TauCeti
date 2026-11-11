/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Dual

/-!
# Polars of absolutely convex hulls

The absolute polar for a bilinear pairing is unchanged by taking an absolutely
convex hull. For the continuous dual pairing, taking the closed absolutely convex
hull also leaves the polar unchanged. These identities let separation arguments
pass between a generating set and its closed disked hull.

In both cases the bipolar of the set is absolutely convex by Mathlib's
`LinearMap.polar_AbsConvex`, and for the continuous dual pairing it is also closed by
continuity of the functionals. So the bipolar contains the hull, and the tripolar
identity `LinearMap.tripolar_eq_polar` concludes. The second identity needs no
topological vector space structure on the space, only a topology.
-/

public section

open scoped ComplexOrder

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommMonoid E] [Module 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F]

/-- Taking the absolutely convex hull does not change the absolute polar of a
bilinear pairing. -/
@[simp]
theorem polar_absConvexHull (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (s : Set E) :
    B.polar (absConvexHull 𝕜 s) = B.polar s :=
  (B.polar_antitone subset_absConvexHull).antisymm <|
    (B.tripolar_eq_polar s).symm.trans_subset <|
      B.polar_antitone <| absConvexHull_min (B.subset_bipolar s) (polar_AbsConvex _)

end LinearMap

namespace StrongDual

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- Taking the closed absolutely convex hull does not change the absolute polar. -/
@[simp]
theorem polar_closedAbsConvexHull (s : Set E) :
    polar 𝕜 (closedAbsConvexHull 𝕜 s) = polar 𝕜 s := by
  rw [polar]
  set B := (topDualPairing 𝕜 E).flip
  have hclosed : IsClosed (B.flip.polar (B.polar s)) := by
    simp only [B, LinearMap.polar_eq_iInter, LinearMap.flip_apply, topDualPairing_apply]
    exact isClosed_biInter fun f _ ↦ isClosed_le f.continuous.norm continuous_const
  exact (B.polar_antitone subset_closedAbsConvexHull).antisymm <|
    (B.tripolar_eq_polar s).symm.trans_subset <| B.polar_antitone <|
      closedAbsConvexHull_min (B.subset_bipolar s) (LinearMap.polar_AbsConvex _) hclosed

end StrongDual
