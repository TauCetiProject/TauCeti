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

The results use Mathlib's `LinearMap.polar_AbsConvex` for the opposite polar and
continuity of the functionals for closure.
-/

public section

open Set Topology
open scoped ComplexOrder

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommMonoid E] [Module 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F]

/-- Taking the absolutely convex hull does not change the absolute polar of a
bilinear pairing. -/
@[simp]
theorem polar_absConvexHull (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (s : Set E) :
    B.polar (absConvexHull 𝕜 s) = B.polar s := by
  apply Subset.antisymm (B.polar_antitone subset_absConvexHull)
  intro f hf
  have h : absConvexHull 𝕜 s ⊆ B.flip.polar {f} := by
    refine absConvexHull_min ?_ (polar_AbsConvex _)
    rintro x hx g rfl
    exact hf x hx
  exact fun x hx ↦ h hx f (mem_singleton _)

end LinearMap

namespace StrongDual

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- Taking the closed absolutely convex hull does not change the absolute polar. -/
@[simp]
theorem polar_closedAbsConvexHull (s : Set E) :
    polar 𝕜 (closedAbsConvexHull 𝕜 s) = polar 𝕜 s := by
  rw [closedAbsConvexHull_eq_closure_absConvexHull]
  have heq : polar 𝕜 (absConvexHull 𝕜 s) = polar 𝕜 s :=
    (topDualPairing 𝕜 E).flip.polar_absConvexHull s
  refine Subset.antisymm
    (((topDualPairing 𝕜 E).flip.polar_antitone subset_closure).trans_eq heq) ?_
  intro f hf
  have hf' : f ∈ polar 𝕜 (absConvexHull 𝕜 s) := by
    rwa [heq]
  exact closure_minimal hf' (isClosed_le f.continuous.norm continuous_const)

end StrongDual
