/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The distance to a pointed cone

Let `C` be a pointed convex cone in a real normed space. Since `C` is closed under addition and
under multiplication by nonnegative scalars, the distance to `C` is subadditive and positively
homogeneous:

* `AddSubmonoidClass.infDist_add_le`: `dist(x + y, C) ≤ dist(x, C) + dist(y, C)`, for every
  additive submonoid `C`;
* `PointedCone.infDist_smul`: `dist(c x, C) = c dist(x, C)` for `c ≥ 0`.

Consequently the distance from a nonnegative combination `∑ cᵢ xᵢ` to `C` is at most
`∑ cᵢ dist(xᵢ, C)`. This is how an estimate on the distance of a sum of two-forms to a cone of
positive forms is split into estimates on the summands.
-/

public section

open Metric
open scoped Pointwise

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **The distance to an additive submonoid is subadditive**:
`dist(x + y, C) ≤ dist(x, C) + dist(y, C)`, since `C` is closed under addition. This applies to
pointed cones. -/
theorem AddSubmonoidClass.infDist_add_le {T : Type*} [SetLike T E] [AddSubmonoidClass T E]
    (C : T) (x y : E) :
    infDist (x + y) (C : Set E) ≤ infDist x (C : Set E) + infDist y (C : Set E) := by
  have hC : (C : Set E).Nonempty := ⟨0, zero_mem C⟩
  -- For `z, w ∈ C`, `z + w ∈ C` is at distance at most `dist x z + dist y w` from `x + y`.
  suffices h : infDist (x + y) (C : Set E) - infDist y (C : Set E) ≤ infDist x (C : Set E) by
    linarith
  refine (le_infDist hC).2 fun z hz ↦ ?_
  suffices h : infDist (x + y) (C : Set E) - dist x z ≤ infDist y (C : Set E) by linarith
  refine (le_infDist hC).2 fun w hw ↦ ?_
  have h₁ := infDist_le_dist_of_mem (x := x + y) (add_mem hz hw : z + w ∈ C)
  have h₂ : dist (x + y) (z + w) ≤ dist x z + dist y w := dist_add_add_le x y z w
  linarith

namespace PointedCone

variable [Module ℝ E] [NormSMulClass ℝ E] (C : PointedCone ℝ E)

/-- **The distance to a pointed cone is positively homogeneous**: `dist(c x, C) = c dist(x, C)`
for `c ≥ 0`, since `C` is invariant under multiplication by positive scalars. -/
theorem infDist_smul {c : ℝ} (hc : 0 ≤ c) (x : E) :
    infDist (c • x) (C : Set E) = c * infDist x (C : Set E) := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [zero_smul, zero_mul, infDist_zero_of_mem C.zero_mem]
  -- A positive multiple of `C` is `C` itself.
  have hcC : c • (C : Set E) = C := Set.ext fun z ↦ by
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
    exact ⟨fun h ↦ by simpa [smul_inv_smul₀ hc.ne'] using C.smul_mem hc.le h,
      C.smul_mem (inv_nonneg.2 hc.le)⟩
  have h := infDist_smul₀ c (C : Set E) x
  rwa [hcC, Real.norm_of_nonneg hc.le] at h

end PointedCone
