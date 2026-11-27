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
* `Metric.infDist_smul_of_smul_mem`: `dist(c x, C) = c dist(x, C)` for `c > 0` and any set `C`
  closed under multiplication by positive scalars, such as a closed cone of frequencies;
* `PointedCone.infDist_smul`: the same for `c ≥ 0` and a pointed cone `C`.

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

namespace Metric

variable [Module ℝ E] [NormSMulClass ℝ E]

/-- **The distance to a cone is positively homogeneous**: for a set `V` closed under
multiplication by positive scalars and `t > 0`, `dist(t x, V) = t dist(x, V)`. -/
theorem infDist_smul_of_smul_mem {V : Set E}
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V) {t : ℝ} (ht : 0 < t) (x : E) :
    infDist (t • x) V = t * infDist x V := by
  rcases V.eq_empty_or_nonempty with rfl | hV
  · simp
  have hle (s : ℝ) (hs : 0 < s) (y : E) : infDist (s • y) V ≤ s * infDist y V := by
    have hsub : s • V ⊆ V := by
      rintro _ ⟨ξ, hξ, rfl⟩
      exact hVcone s hs ξ hξ
    have h := infDist_le_infDist_of_subset hsub (hV.smul_set (a := s)) (x := s • y)
    rwa [infDist_smul₀, Real.norm_of_nonneg hs.le] at h
  refine le_antisymm (hle t ht x) ?_
  have h := hle t⁻¹ (inv_pos.2 ht) (t • x)
  rw [inv_smul_smul₀ ht.ne'] at h
  calc t * infDist x V ≤ t * (t⁻¹ * infDist (t • x) V) := by gcongr
    _ = infDist (t • x) V := by rw [mul_inv_cancel_left₀ ht.ne']

end Metric

namespace PointedCone

variable [Module ℝ E] [NormSMulClass ℝ E] (C : PointedCone ℝ E)

/-- **The distance to a pointed cone is positively homogeneous**: `dist(c x, C) = c dist(x, C)`
for `c ≥ 0`, since `C` is invariant under multiplication by positive scalars. -/
theorem infDist_smul {c : ℝ} (hc : 0 ≤ c) (x : E) :
    infDist (c • x) (C : Set E) = c * infDist x (C : Set E) := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [zero_smul, zero_mul, infDist_zero_of_mem C.zero_mem]
  exact infDist_smul_of_smul_mem (fun t ht ξ hξ ↦ C.smul_mem ht.le hξ) hc x

end PointedCone
