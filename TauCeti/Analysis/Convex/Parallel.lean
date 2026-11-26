/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import TauCeti.Topology.MetricSpace.Thickening

/-!
# Outer parallel sets of convex sets

For convex sets `A` and `B`, Minkowski addition and nonnegative scalar multiplication commute
with weighted interpolation:

`p • (A + s • B) + q • (A + t • B) = A + (p * s + q * t) • B`

when `p + q = 1`. Thus the family of outer parallel sets `A + t • B` is affine under
Minkowski interpolation. The specialization where `B` is the closed unit ball is the set identity
used to transfer Brunn--Minkowski concavity to the volumes of outer parallel bodies.

No nonemptiness or topological assumptions are needed: the result is an algebraic consequence of
convexity, combined with Mathlib's distributivity `smul_add` of scalar multiplication over
pointwise set addition.

In a real normed space, a convex set `K` containing the closed ball of radius `ρ > 0` about
`x₀` absorbs its outer parallel sets into its dilates about `x₀`:
`K + t • closedBall 0 1` lies in the image of `K` under the homothety with centre `x₀` and ratio
`(ρ + t) / ρ`. Since this ratio tends to `1` as `t → 0`, quantities that are monotone under
inclusion and scale under homotheties, such as the perimeter or the surface area, of the outer
parallel sets are controlled by those of `K` itself.

For a set `K` star-convex about `y`, moving away from `y` scales the distance to `K` at least
proportionally: `c * infDist x K ≤ infDist (y + c • (x - y)) K` for `c ≥ 1`. Hence for `t > 0` the
frontier of the closed parallel set `cthickening t K` is exactly the level set
`{x | infDist x K = t}` of the distance. For an arbitrary set only the inclusion `⊆` holds
(Mathlib's `Metric.frontier_cthickening_subset`): the closed `1`-neighbourhood of `{-1, 1}` in `ℝ`
is `[-2, 2]`, while `0` is at distance `1` from both points.

## Main results

* `Convex.add_smul_interpolation`: interpolation of two parallel convex sets with
  arbitrary nonnegative weights summing to one.
* `Convex.add_smul_interpolation_sub`: the same identity with weights `1 - u` and `u`.
* `Convex.add_smul_closedBall_subset_image_homothety`: outer parallel sets of a convex set with
  an interior ball lie in its dilates.
* `StarConvex.mul_infDist_le_infDist_add_smul_sub`: the distance to a star-convex set grows at
  least linearly along rays from its centre.
* `StarConvex.frontier_cthickening` and `Convex.frontier_cthickening`: the frontier of a closed
  parallel set of a star-convex or convex set is a level set of the distance.
-/

public section

open Set Metric Filter
open scoped Pointwise Topology

namespace Convex

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/-- Weighted interpolation between the parallel convex sets `A + s • B` and `A + t • B`
is the parallel set at the correspondingly weighted parameter. -/
theorem add_smul_interpolation {A B : Set E} (hA : Convex 𝕜 A) (hB : Convex 𝕜 B)
    {p q s t : 𝕜} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    p • (A + s • B) + q • (A + t • B) = A + (p * s + q * t) • B := by
  have hA' : p • A + q • A = A := by rw [← hA.add_smul hp hq, hpq, one_smul]
  have hB' : (p * s) • B + (q * t) • B = (p * s + q * t) • B :=
    (hB.add_smul (mul_nonneg hp hs) (mul_nonneg hq ht)).symm
  calc p • (A + s • B) + q • (A + t • B)
      = (p • A + q • A) + ((p * s) • B + (q * t) • B) := by
        simp only [smul_add, smul_smul]
        exact add_add_add_comm _ _ _ _
    _ = A + (p * s + q * t) • B := by rw [hA', hB']

/-- Convex-combination form of `Convex.add_smul_interpolation`, parametrized by
`u ∈ [0, 1]`. -/
theorem add_smul_interpolation_sub {A B : Set E} (hA : Convex 𝕜 A)
    (hB : Convex 𝕜 B) {u s t : 𝕜} (hu : u ∈ Icc 0 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (1 - u) • (A + s • B) + u • (A + t • B) =
      A + ((1 - u) * s + u * t) • B := by
  exact add_smul_interpolation hA hB (sub_nonneg.mpr hu.2) hu.1
    (sub_add_cancel 1 u) hs ht

section Normed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Outer parallel sets lie in dilates.** If a convex set `K` contains the closed ball of
radius `ρ > 0` about `x₀`, then for `t ≥ 0` its outer parallel set `K + t • closedBall 0 1` lies in
the image of `K` under the homothety with centre `x₀` and ratio `(ρ + t) / ρ`. -/
theorem add_smul_closedBall_subset_image_homothety {K : Set E} (hK : Convex ℝ K) {x₀ : E}
    {ρ t : ℝ} (hρ : 0 < ρ) (hρK : Metric.closedBall x₀ ρ ⊆ K) (ht : 0 ≤ t) :
    K + t • Metric.closedBall (0 : E) 1 ⊆ AffineMap.homothety x₀ ((ρ + t) / ρ) '' K := by
  rintro _ ⟨k, hk, _, ⟨b, hb, rfl⟩, rfl⟩
  set a := ρ / (ρ + t)
  have hρt : 0 < ρ + t := by positivity
  have ha1 : a ≤ 1 := (div_le_one hρt).2 (by linarith)
  have hxb : x₀ + ρ • b ∈ K := hρK <| by
    rw [mem_closedBall_zero_iff] at hb
    rw [Metric.mem_closedBall, dist_self_add_left, norm_smul, Real.norm_of_nonneg hρ.le]
    exact mul_le_of_le_one_right hρ.le hb
  -- The preimage of `k + t • b` is the convex combination `a • k + (1 - a) • (x₀ + ρ • b)`.
  refine ⟨a • k + (1 - a) • (x₀ + ρ • b),
    hK hk hxb (div_pos hρ hρt).le (sub_nonneg.2 ha1) (add_sub_cancel _ _), ?_⟩
  rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  match_scalars <;> simp only [a] <;> field_simp <;> ring

/-- **The distance to a star-convex set grows along rays from its centre.** If `K` is star-convex
about `y` and `c ≥ 1`, then the point `y + c • (x - y)` is at least `c` times as far from `K` as `x`
is. -/
theorem _root_.StarConvex.mul_infDist_le_infDist_add_smul_sub {K : Set E} {x y : E}
    (hK : StarConvex ℝ y K) {c : ℝ} (hc : 1 ≤ c) :
    c * infDist x K ≤ infDist (y + c • (x - y)) K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  refine (le_infDist hne).2 fun w hw => ?_
  -- The point `y + c⁻¹ • (w - y)` of `K` is `c` times closer to `x` than `w` is to the image
  -- `y + c • (x - y)` of `x`.
  have hw' : y + c⁻¹ • (w - y) ∈ K :=
    hK.add_smul_sub_mem hw (inv_nonneg.2 hc0.le) (inv_le_one_of_one_le₀ hc)
  have hdist : dist (y + c • (x - y)) w = c * dist x (y + c⁻¹ • (w - y)) := by
    have hvec : y + c • (x - y) - w = c • (x - (y + c⁻¹ • (w - y))) := by
      simp only [smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]
      abel
    rw [dist_eq_norm, dist_eq_norm, hvec, norm_smul, Real.norm_of_nonneg hc0.le]
  rw [hdist]
  exact mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem hw') hc0.le

/-- **The frontier of a closed parallel set of a star-convex set.** For a star-convex set `K` and
`t > 0`, the frontier of the closed `t`-neighbourhood of `K` is the set of points at distance
exactly `t` from `K`. -/
theorem _root_.StarConvex.frontier_cthickening {K : Set E} {y : E} (hK : StarConvex ℝ y K) {t : ℝ}
    (ht : 0 < t) : frontier (cthickening t K) = {x | infDist x K = t} := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp [ht.ne]
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hx' := frontier_cthickening_subset K hx
    simp only [mem_ofPred_eq] at hx' ⊢
    rw [infDist, hx', ENNReal.toReal_ofReal ht.le]
  -- The points beyond `x` on the ray from `y` are farther than `t` from `K`, so `x` is not
  -- interior.
  rw [mem_ofPred_eq] at hx
  rw [frontier_eq_closure_inter_closure, isClosed_cthickening.closure_eq]
  refine ⟨(TauCeti.mem_cthickening_iff_infDist_le hne ht.le).2 hx.le, ?_⟩
  have hlim : Tendsto (fun c : ℝ => y + c • (x - y)) (𝓝[>] 1) (𝓝 x) := by
    have : Continuous fun c : ℝ => y + c • (x - y) := by fun_prop
    simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun c (hc : 1 < c) => ?_)
  rw [TauCeti.compl_cthickening_eq_setOf_lt_infDist hne ht.le, mem_ofPred_eq]
  calc t < c * t := by nlinarith
    _ = c * infDist x K := by rw [hx]
    _ ≤ _ := hK.mul_infDist_le_infDist_add_smul_sub hc.le

/-- **The frontier of a closed parallel set of a convex set.** For a convex set `K` and `t > 0`,
the frontier of the closed `t`-neighbourhood of `K` is the set of points at distance exactly `t`
from `K`. -/
theorem frontier_cthickening {K : Set E} (hK : Convex ℝ K) {t : ℝ} (ht : 0 < t) :
    frontier (cthickening t K) = {x | infDist x K = t} := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · simp [ht.ne]
  exact (hK.starConvex hy).frontier_cthickening ht

end Normed

end Convex
