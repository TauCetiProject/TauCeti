/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

-- Proof-only: compactness of the convex hull of a finite set, the convexity of a closed
-- half-space, the variational inequality of a nearest point of a convex set, and the normalized
-- vector in the unit ball.
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.RCLike.Real
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.InnerProductSpace.Projection.MetricProj

/-!
# The maximum margin is the distance to the convex hull

Let `a : ι → E` be a nonempty finite family in a real inner product space. The margin of a
direction `w` on `a` is the least inner product `⟪w, a i⟫` (`TauCeti.margin`). This file proves
that the largest margin of a direction in the closed unit ball is the distance
`Metric.infDist 0 (convexHull ℝ (Set.range a))` from the origin to the convex hull of the family,
and that, when this distance is positive, a nearest point `c` of the hull gives the only
maximizing direction `‖c‖⁻¹ • c` (`TauCeti.isGreatest_margin`).

The upper bound holds because the half-space `{z | margin a w ≤ ⟪w, z⟫}` is convex and contains
the family, hence the hull, and `⟪w, c⟫ ≤ ‖c‖` for `‖w‖ ≤ 1`. The lower bound comes from the
variational inequality of a nearest point `c` of the hull, which gives `‖c‖ ^ 2 ≤ ⟪c, a i⟫` for
every `i`. A nearest point exists because the hull of a finite set is compact.

The closed unit ball cannot be replaced by the unit sphere: for the family `(1, -1)` in `ℝ` the
origin lies in the hull, the largest margin is `0`, attained only at `w = 0`, and every unit
direction has margin `-1`.

## Main definitions

* `TauCeti.margin a w`: the least inner product `⟪w, a i⟫` over a nonempty finite family `a`.

## Main results

* `TauCeti.le_margin_iff`, `TauCeti.margin_le_inner`, `TauCeti.exists_margin_eq_inner`: the
  margin is the least of the inner products `⟪w, a i⟫`.
* `TauCeti.margin_le_inner_of_mem_convexHull`: the margin is at most `⟪w, c⟫` for every point `c`
  of the convex hull of the family.
* `TauCeti.margin_le_infDist`: a direction in the closed unit ball has margin at most the
  distance from the origin to the convex hull.
* `TauCeti.margin_inv_norm_smul_eq`: a nearest point `c` of the hull to the origin gives the
  direction `‖c‖⁻¹ • c` of margin `‖c‖`.
* `TauCeti.eq_inv_norm_smul_of_margin_eq`: if `c` lies in the hull and `0 < ‖c‖`, the only
  direction in the closed unit ball with margin `‖c‖` is `‖c‖⁻¹ • c`.
* `TauCeti.isGreatest_margin`: the maximum margin over the closed unit ball is the distance from
  the origin to the convex hull, and for a positive distance the maximizing direction is unique.
-/

public section

open Finset Metric Set
open scoped RealInnerProductSpace

namespace TauCeti

variable {ι : Type*} [Fintype ι] [Nonempty ι]

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The margin of the direction `w` on a nonempty finite family `a`: the least inner product
`⟪w, a i⟫`. -/
noncomputable def margin (a : ι → E) (w : E) : ℝ :=
  univ.inf' univ_nonempty fun i => ⟪w, a i⟫

/-- A real number is at most the margin of `w` on `a` if and only if it is at most each inner
product `⟪w, a i⟫`. -/
@[simp]
theorem le_margin_iff {a : ι → E} {w : E} {r : ℝ} : r ≤ margin a w ↔ ∀ i, r ≤ ⟪w, a i⟫ := by
  simp [margin]

/-- The margin of `w` on `a` is at most each inner product `⟪w, a i⟫`. -/
theorem margin_le_inner (a : ι → E) (w : E) (i : ι) : margin a w ≤ ⟪w, a i⟫ :=
  le_margin_iff.1 le_rfl i

/-- The margin of `w` on `a` is attained: it is the inner product `⟪w, a i⟫` for some `i`. -/
theorem exists_margin_eq_inner (a : ι → E) (w : E) : ∃ i, margin a w = ⟪w, a i⟫ :=
  let ⟨i, _, h⟩ := exists_mem_eq_inf' univ_nonempty fun i => ⟪w, a i⟫
  ⟨i, h⟩

/-- The margin of `w` on `a` is at most `⟪w, c⟫` for every point `c` of the convex hull of the
family. -/
theorem margin_le_inner_of_mem_convexHull (a : ι → E) (w : E) {c : E}
    (hc : c ∈ convexHull ℝ (range a)) : margin a w ≤ ⟪w, c⟫ := by
  refine convexHull_min (t := {z | margin a w ≤ ⟪w, z⟫})
    (range_subset_iff.2 (margin_le_inner a w)) ?_ hc
  simpa only [real_inner_comm w] using convex_setOf_le_inner w (margin a w)

/-- A direction in the closed unit ball has margin at most the norm of each point of the convex
hull of the family. -/
theorem margin_le_norm_of_mem_convexHull (a : ι → E) {w : E} (hw : ‖w‖ ≤ 1) {c : E}
    (hc : c ∈ convexHull ℝ (range a)) : margin a w ≤ ‖c‖ :=
  (margin_le_inner_of_mem_convexHull a w hc).trans <|
    (real_inner_le_norm w c).trans (mul_le_of_le_one_left (norm_nonneg c) hw)

/-- A direction in the closed unit ball has margin at most the distance from the origin to the
convex hull of the family. -/
theorem margin_le_infDist (a : ι → E) {w : E} (hw : ‖w‖ ≤ 1) :
    margin a w ≤ infDist 0 (convexHull ℝ (range a)) :=
  (le_infDist (range_nonempty a).convexHull).2 fun c hc => by
    simpa only [dist_zero_left] using margin_le_norm_of_mem_convexHull a hw hc

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nearest point `c` of the convex hull of the family to the origin gives the direction
`‖c‖⁻¹ • c` of margin `‖c‖`. -/
theorem margin_inv_norm_smul_eq (a : ι → E) {c : E} (hc : c ∈ convexHull ℝ (range a))
    (hnorm : ‖c‖ = infDist 0 (convexHull ℝ (range a))) : margin a (‖c‖⁻¹ • c) = ‖c‖ := by
  refine le_antisymm (margin_le_norm_of_mem_convexHull a ?_ hc) (le_margin_iff.2 fun i => ?_)
  · exact mem_closedBall_zero_iff.1 (inv_norm_smul_mem_unitClosedBall c)
  · have hvar := inner_sub_sub_nonpos_of_norm_sub_eq_infDist (convex_convexHull ℝ (range a)) hc
      (by rwa [zero_sub, norm_neg]) (a i) (subset_convexHull ℝ (range a) (mem_range_self i))
    have hle : ‖c‖ ^ 2 ≤ ⟪c, a i⟫ := by
      rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at hvar
      linarith
    rw [real_inner_smul_left]
    calc ‖c‖ = ‖c‖⁻¹ * ‖c‖ ^ 2 := by rw [sq, ← mul_assoc, inv_mul_mul_self]
      _ ≤ ‖c‖⁻¹ * ⟪c, a i⟫ := mul_le_mul_of_nonneg_left hle (inv_nonneg.2 (norm_nonneg c))

/-- **Uniqueness of the maximizing direction.** If `c` is a point of the convex hull of the
family with `0 < ‖c‖`, then a direction in the closed unit ball with margin `‖c‖` is `‖c‖⁻¹ • c`.
-/
theorem eq_inv_norm_smul_of_margin_eq (a : ι → E) {c : E} (hc : c ∈ convexHull ℝ (range a))
    (hpos : 0 < ‖c‖) {w : E} (hw : ‖w‖ ≤ 1) (hmargin : margin a w = ‖c‖) : w = ‖c‖⁻¹ • c := by
  have h₁ : ‖c‖ ≤ ⟪w, c⟫ := hmargin ▸ margin_le_inner_of_mem_convexHull a w hc
  have h₂ := real_inner_le_norm w c
  have hw₁ : ‖w‖ = 1 := le_antisymm hw (le_of_mul_le_mul_right (by linarith) hpos)
  have hsmul : ‖c‖ • w = c := by
    rw [inner_eq_norm_mul_iff_real.1 (by rw [hw₁] at h₂ ⊢; linarith), hw₁, one_smul]
  exact (eq_inv_smul_iff₀ hpos.ne').2 hsmul

/-- **The maximum margin is the distance to the convex hull.** Over the closed unit ball, the
largest margin on a nonempty finite family is the distance from the origin to the convex hull of
the family. When this distance is positive, every point `c` of the hull at that distance gives
the only maximizing direction `‖c‖⁻¹ • c`. -/
theorem isGreatest_margin (a : ι → E) :
    IsGreatest (margin a '' closedBall 0 1) (infDist 0 (convexHull ℝ (range a))) ∧
      ∀ c ∈ convexHull ℝ (range a), ‖c‖ = infDist 0 (convexHull ℝ (range a)) →
        0 < ‖c‖ → ∀ w ∈ closedBall (0 : E) 1, margin a w = ‖c‖ → w = ‖c‖⁻¹ • c := by
  refine ⟨⟨?_, ?_⟩, fun c hc _ hpos w hw hmargin =>
    eq_inv_norm_smul_of_margin_eq a hc hpos (mem_closedBall_zero_iff.1 hw) hmargin⟩
  · obtain ⟨c, hc, hdist⟩ :=
      ((finite_range a).isCompact_convexHull (𝕜 := ℝ)).exists_infDist_eq_dist
        (range_nonempty a).convexHull 0
    rw [dist_zero_left] at hdist
    exact ⟨‖c‖⁻¹ • c, inv_norm_smul_mem_unitClosedBall c,
      by rw [margin_inv_norm_smul_eq a hc hdist.symm, hdist]⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact margin_le_infDist a (mem_closedBall_zero_iff.1 hw)

end Normed

end TauCeti
