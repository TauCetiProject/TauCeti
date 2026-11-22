/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Geometry.Convex.Cone.Basic

/-!
# The gauge of a convex set on its cone hull

Mathlib develops the gauge (Minkowski functional) `gauge s` mainly for absorbent sets `s`, for
which every point lies in some dilate `r • s` with `r > 0`. A convex set with `0` on its
boundary, such as a polytope having `0` as a vertex, is not absorbent: the points lying in some
dilate `r • s` form the cone hull `ConvexCone.hull ℝ s` (`ConvexCone.mem_hull_of_convex`), and
outside it the infimum defining the gauge is taken over the empty set. This file proves, on the
cone hull, the properties of the gauge that Mathlib proves for absorbent sets.

## Main results

* `TauCeti.gauge_add_le_of_mem_hull`: the gauge of a convex set is subadditive on its cone hull.
* `TauCeti.mem_smul_of_gauge_le_of_mem_hull`: for a closed bounded convex set `s` containing
  `0`, a point `x` of the cone hull with `gauge s x ≤ t` lies in `t • s`. In particular the
  infimum defining the gauge is attained there (`TauCeti.mem_gauge_smul_of_mem_hull`).
* `TauCeti.mem_hull_and_gauge_le_iff`: for such `s`, a point lies in the cone hull and has gauge
  at most `t` exactly when `0 ≤ t` and it lies in `t • s`.

In a polytope with `0` as a vertex these describe the height function of the cone over the
polytope, which is the gauge restricted to the cone: its sublevel sets are the dilates of the
polytope.
-/

public section

open scoped Pointwise

namespace TauCeti

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E} {x y : E} {t : ℝ}

/-- If `x` lies in the cone hull of a convex set `s` and `gauge s x < a`, then `x` lies in a
dilate `b • s` with `0 < b < a`. -/
theorem exists_lt_of_gauge_lt_of_mem_hull (hs : Convex ℝ s) (hx : x ∈ ConvexCone.hull ℝ s)
    {a : ℝ} (ha : gauge s x < a) : ∃ b, 0 < b ∧ b < a ∧ x ∈ b • s := by
  obtain ⟨b, ⟨hb, hxb⟩, hba⟩ :=
    exists_lt_of_csInf_lt (s := {r : ℝ | 0 < r ∧ x ∈ r • s})
      ((ConvexCone.mem_hull_of_convex hs).1 hx) ha
  exact ⟨b, hb, hba, hxb⟩

/-- The gauge of a convex set is subadditive on its cone hull. -/
theorem gauge_add_le_of_mem_hull (hs : Convex ℝ s) (hx : x ∈ ConvexCone.hull ℝ s)
    (hy : y ∈ ConvexCone.hull ℝ s) : gauge s (x + y) ≤ gauge s x + gauge s y := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨a, ha, ha', x', hx', rfl⟩ :=
    exists_lt_of_gauge_lt_of_mem_hull hs hx (lt_add_of_pos_right (gauge s x) (half_pos hε))
  obtain ⟨b, hb, hb', y', hy', rfl⟩ :=
    exists_lt_of_gauge_lt_of_mem_hull hs hy (lt_add_of_pos_right (gauge s y) (half_pos hε))
  calc
    gauge s (a • x' + b • y') ≤ a + b := gauge_le_of_mem (by positivity) <| by
      rw [hs.add_smul ha.le hb.le]
      exact Set.add_mem_add (Set.smul_mem_smul_set hx') (Set.smul_mem_smul_set hy')
    _ < gauge s (a • x') + gauge s (b • y') + ε := by linarith

/-- If `x` lies in the cone hull of a convex set `s` containing `0` and `gauge s x < r`, then
`x` lies in the dilate `r • s`. -/
theorem mem_smul_of_gauge_lt_of_mem_hull (hs : Convex ℝ s) (hs₀ : (0 : E) ∈ s)
    (hx : x ∈ ConvexCone.hull ℝ s) {r : ℝ} (hr : gauge s x < r) : x ∈ r • s := by
  obtain ⟨b, hb, hbr, hxb⟩ := exists_lt_of_gauge_lt_of_mem_hull hs hx hr
  have hr₀ : 0 < r := hb.trans hbr
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hb.ne'] at hxb
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr₀.ne']
  have h : r⁻¹ • x = (b / r) • b⁻¹ • x := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [h]
  exact (hs.starConvex hs₀).smul_mem hxb (by positivity) (div_le_one_of_le₀ hbr.le hr₀.le)

variable [TopologicalSpace E] [ContinuousSMul ℝ E] [T1Space E]

/-- For a closed bounded convex set `s` containing `0`, a point `x` of the cone hull of `s` with
`gauge s x ≤ t` lies in the dilate `t • s`. -/
theorem mem_smul_of_gauge_le_of_mem_hull (hs : Convex ℝ s) (hs₀ : (0 : E) ∈ s)
    (hsc : IsClosed s) (hsb : Bornology.IsVonNBounded ℝ s) (hx : x ∈ ConvexCone.hull ℝ s)
    (ht : gauge s x ≤ t) : x ∈ t • s := by
  have hmem (r : ℝ) (hr : t < r) : x ∈ r • s :=
    mem_smul_of_gauge_lt_of_mem_hull hs hs₀ hx (ht.trans_lt hr)
  rcases ((gauge_nonneg x).trans ht).eq_or_lt with rfl | htpos
  · -- `x` lies in every dilate `r • s` with `r > 0`; as `s` is bounded, `x = 0`
    rw [Set.zero_smul_set ⟨0, hs₀⟩, Set.mem_zero]
    by_contra hx0
    obtain ⟨r, hr, hsub⟩ := (hsb (isOpen_compl_singleton.mem_nhds (Ne.symm hx0))).exists_pos
    have hrx : x ∈ r⁻¹ • s := hmem _ (inv_pos.2 hr)
    have hx' : x ∈ r⁻¹ • r • ({x}ᶜ : Set E) :=
      Set.smul_set_mono (hsub r (by rw [Real.norm_of_nonneg hr.le])) hrx
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at hx'
    exact hx' rfl
  · -- `r⁻¹ • x ∈ s` for every `r > t`, and `s` is closed
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ htpos.ne']
    refine hsc.mem_of_tendsto (f := fun r : ℝ => r⁻¹ • x) (b := nhdsWithin t (Set.Ioi t)) ?_ ?_
    · exact (((continuousAt_inv₀ htpos.ne').smul continuousAt_const).tendsto).mono_left
        nhdsWithin_le_nhds
    · refine eventually_nhdsWithin_of_forall fun r hr => ?_
      have hr : t < r := hr
      exact (Set.mem_smul_set_iff_inv_smul_mem₀ (htpos.trans hr).ne' _ _).1 (hmem r hr)

/-- For a closed bounded convex set `s` containing `0`, the infimum defining the gauge is
attained on the cone hull: a point `x` of the cone hull lies in `gauge s x • s`. -/
theorem mem_gauge_smul_of_mem_hull (hs : Convex ℝ s) (hs₀ : (0 : E) ∈ s) (hsc : IsClosed s)
    (hsb : Bornology.IsVonNBounded ℝ s) (hx : x ∈ ConvexCone.hull ℝ s) : x ∈ gauge s x • s :=
  mem_smul_of_gauge_le_of_mem_hull hs hs₀ hsc hsb hx le_rfl

/-- For a closed bounded convex set `s` containing `0`, a point lies in the cone hull of `s` and
has gauge at most `t` exactly when `0 ≤ t` and it lies in the dilate `t • s`. -/
theorem mem_hull_and_gauge_le_iff (hs : Convex ℝ s) (hs₀ : (0 : E) ∈ s) (hsc : IsClosed s)
    (hsb : Bornology.IsVonNBounded ℝ s) :
    x ∈ ConvexCone.hull ℝ s ∧ gauge s x ≤ t ↔ 0 ≤ t ∧ x ∈ t • s := by
  refine ⟨fun ⟨hx, ht⟩ => ⟨(gauge_nonneg x).trans ht,
    mem_smul_of_gauge_le_of_mem_hull hs hs₀ hsc hsb hx ht⟩, fun ⟨ht, hx⟩ => ⟨?_,
    gauge_le_of_mem ht hx⟩⟩
  rcases ht.eq_or_lt with rfl | ht
  · rw [Set.zero_smul_set ⟨0, hs₀⟩, Set.mem_zero] at hx
    exact hx ▸ ConvexCone.subset_hull hs₀
  · exact (ConvexCone.mem_hull_of_convex hs).2 ⟨t, ht, hx⟩

end TauCeti
