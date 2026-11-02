/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Polygon.Basic
public import TauCeti.Analysis.Contour.Cycle.Basic
public import TauCeti.MeasureTheory.Function.CurveAction.Polygonal
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On.Polygonal
import TauCeti.Analysis.Green.Polygonal.Fan
import TauCeti.GroupTheory.Perm.Cycle.Enumeration

/-!
# Polygons and balanced families of segments as contour cycles

A polygon `poly : Polygon ℂ n` with `n ≠ 0` vertices is a cyclic list of points of the plane. Its
edges, traversed in order, form a closed polygonal curve: on `[k, k + 1]` it runs along the edge
from vertex `k` to vertex `k + 1`, the last edge returning to vertex `0`. This file packages that
curve as a one-generator contour cycle and computes its invariants edge by edge: its trace is the
boundary of the polygon, and its cycle integral and its winding numbers are the sums over the
edges of the corresponding segment quantities.

More generally, a finite family of oriented segments in which every point ends as many segments
as it starts assembles into a contour cycle. Choosing at each point a matching of the segments
ending there with those starting there gives a permutation of the segments, and each of its
orbits is a closed polygon. The sum of these polygon cycles has the sum of the segment integrals
and segment winding numbers as its integrals and winding numbers. This is how the boundary edges
of a union of grid squares around a compact set, left after the cancellation of shared edges,
become a contour cycle.

## Main definitions

* `Polygon.contourCurve poly`: the closed polygonal curve of `poly` on `[0, n]`.
* `Polygon.contourCycle poly`: the corresponding one-generator contour cycle.

## Main results

* `Polygon.trace_contourCycle`: the trace is the boundary of the polygon.
* `Polygon.integral_contourCycle`: the integral of a function continuous on the boundary is the
  sum of its integrals along the edges.
* `Polygon.windingNumber_contourCycle`: off the boundary, the winding number is the sum of the
  winding numbers of the edges.
* `TauCeti.Contour.Cycle.exists_windingNumber_integral_eq_sum_segments`: a balanced finite family
  of oriented segments is a contour cycle, with the sums of the segment winding numbers and
  segment integrals as its winding numbers and integrals.

## References

* W. Rudin, *Real and Complex Analysis*, third edition, Theorem 13.5.
* J. B. Conway, *Functions of One Complex Variable I*, second edition, Proposition VIII.1.1.
-/

public section

noncomputable section

open Set MeasureTheory Function Fin.NatCast

open scoped Finset

universe u

namespace TauCeti.Contour

variable {n : ℕ} [NeZero n] (poly : Polygon ℂ n)

/-- The vertex sequence `k ↦ poly k` of a polygon, indexed by `ℕ` and hence `n`-periodic. -/
private def vertexSeq : ℕ → ℂ :=
  fun k ↦ poly (k : Fin n)

/-- The raw closed polygonal curve of a polygon: the polygonal interpolation of its vertex
sequence on the integer grid of `[0, n]`. -/
private def polygonFun : ℝ → ℂ :=
  polygonalInterpolation 0 1 n (vertexSeq poly)

/-- On `[i, i + 1]` the polygonal curve runs along edge `i`. -/
private theorem polygonFun_natCast_add (i : Fin n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    polygonFun poly ((i : ℕ) + s) = poly.edgePath ℝ i s := by
  have ht : ((i : ℕ) : ℝ) + s ∈ Icc (0 + ((i : ℕ) : ℝ) * 1) (0 + ((i : ℕ) + 1) * 1) := by
    simp only [zero_add, mul_one, mem_Icc]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rw [polygonFun, polygonalInterpolation_eq_of_mem_Icc _ one_pos i.isLt ht]
  simp [Polygon.edgePath, AffineMap.lineMap_apply_module', vertexSeq, add_comm]

/-- The polygonal curve starts at vertex `0`. -/
private theorem polygonFun_zero : polygonFun poly 0 = poly 0 := by
  have h := polygonalInterpolation_apply_grid (a := 0) (N := n) (vertexSeq poly) one_pos
    (Nat.zero_le n)
  simpa [polygonFun, vertexSeq] using h

/-- The polygonal curve ends at vertex `0`. -/
private theorem polygonFun_natCast : polygonFun poly n = poly 0 := by
  have h := polygonalInterpolation_apply_grid (a := 0) (N := n) (vertexSeq poly) one_pos le_rfl
  simpa [polygonFun, vertexSeq] using h

/-- The polygonal curve is affine on each cell `[i, i + 1]`. -/
private theorem isPolygonalOnInterval_polygonFun :
    IsPolygonalOnInterval (polygonFun poly) 0 n := by
  simpa using isPolygonalOnInterval_of_eqOn_polygonalInterpolation (f := polygonFun poly)
    (NeZero.ne n) one_pos fun _ _ ↦ rfl

/-- The image of the parameter interval under the polygonal curve is the boundary of the
polygon. -/
private theorem image_polygonFun : polygonFun poly '' uIcc 0 n = poly.boundary ℝ := by
  rw [uIcc_of_le (Nat.cast_nonneg n)]
  ext z
  simp only [mem_image, Polygon.boundary, mem_iUnion, Polygon.edgeSet_eq_image_edgePath]
  constructor
  · rintro ⟨t, ⟨ht₀, htn⟩, rfl⟩
    -- The parameter `t` lies in the cell `[k, k + 1]` with `k = min ⌊t⌋₊ (n - 1)`.
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    set k := min ⌊t⌋₊ (n - 1) with hk
    have hkn : k < n := lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hn one_pos)
    have hkt : (k : ℝ) ≤ t := (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le ht₀)
    have htk : t ≤ k + 1 := by
      rcases le_total ⌊t⌋₊ (n - 1) with h | h
      · rw [hk, min_eq_left h]
        exact (Nat.lt_floor_add_one t).le
      · rw [hk, min_eq_right h, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (NeZero.ne n)),
          Nat.cast_one, sub_add_cancel]
        exact htn
    refine ⟨⟨k, hkn⟩, t - k, ⟨by linarith, by linarith⟩, ?_⟩
    rw [← polygonFun_natCast_add poly ⟨k, hkn⟩ ⟨by linarith, by linarith⟩]
    simp
  · rintro ⟨i, s, hs, rfl⟩
    have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
    exact ⟨(i : ℕ) + s, ⟨by linarith [hs.1, (Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ _)],
      by linarith [hs.2]⟩, polygonFun_natCast_add poly i hs⟩

/-- The closed polygonal curve of a polygon `poly` with `n ≠ 0` vertices, on the parameter
interval `[0, n]`: on `[k, k + 1]` it runs along the edge from vertex `k` to vertex `k + 1`, and
the last edge returns to vertex `0`. -/
def _root_.Polygon.contourCurve : PiecewiseC1ClosedCurve :=
  PiecewiseC1ClosedCurve.of (polygonFun poly)
    (isPolygonalOnInterval_polygonFun poly).isPiecewiseC1On
    ((polygonFun_zero poly).trans (polygonFun_natCast poly).symm)

/-- The polygonal curve starts at the parameter `0`. -/
@[simp]
theorem _root_.Polygon.contourCurve_a : poly.contourCurve.a = 0 := by
  rw [Polygon.contourCurve, PiecewiseC1ClosedCurve.of_a]

/-- The polygonal curve ends at the parameter `n`. -/
@[simp]
theorem _root_.Polygon.contourCurve_b : poly.contourCurve.b = n := by
  rw [Polygon.contourCurve, PiecewiseC1ClosedCurve.of_b]

/-- On `[i, i + 1]` the polygonal curve runs along edge `i` of the polygon. -/
theorem _root_.Polygon.contourCurve_natCast_add (i : Fin n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    poly.contourCurve ((i : ℕ) + s) = poly.edgePath ℝ i s := by
  have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  rw [Polygon.contourCurve, PiecewiseC1ClosedCurve.of_apply _ _ _
    (by rw [uIcc_of_le (Nat.cast_nonneg n)]
        exact ⟨by linarith [hs.1, (Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ _)], by linarith [hs.2]⟩),
    polygonFun_natCast_add poly i hs]

/-- The closed polygonal curve of a polygon `poly` with `n ≠ 0` vertices, as a one-generator
contour cycle. -/
def _root_.Polygon.contourCycle : Cycle :=
  FreeAbelianGroup.of poly.contourCurve

/-- The cycle of a polygon is the single generator given by its polygonal curve. -/
theorem _root_.Polygon.contourCycle_def :
    poly.contourCycle = FreeAbelianGroup.of poly.contourCurve := (rfl)

/-- The trace of the cycle of a polygon is the boundary of the polygon. -/
@[simp]
theorem _root_.Polygon.trace_contourCycle : Cycle.trace poly.contourCycle = poly.boundary ℝ := by
  rw [Polygon.contourCycle, Polygon.contourCurve, Cycle.trace_of_raw, image_polygonFun]

/-- **The integral over a polygon** of a function continuous on its boundary is the sum over the
edges `[v, w]` of `(w - v) • ∫ t in 0..1, f (v + t (w - v))`. -/
theorem _root_.Polygon.integral_contourCycle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : ContinuousOn f (poly.boundary ℝ)) :
    Cycle.integral f poly.contourCycle =
      ∑ i, (poly (finRotate n i) - poly i) • ∫ t in (0 : ℝ)..1, f (poly.edgePath ℝ i t) := by
  have hγ := (isPolygonalOnInterval_polygonFun poly).isPiecewiseC1On
  have hint := hγ.intervalIntegrable_deriv_smul_comp_of_mapsTo hf
    (mapsTo_iff_image_subset.2 (image_polygonFun poly).subset)
  rw [Polygon.contourCycle, Polygon.contourCurve, Cycle.integral_of_raw]
  -- Split the integral over `[0, n]` into the integrals over the cells `[i, i + 1]`.
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ ↦ (k : ℝ))
    (n := n) (μ := volume) (f := fun t ↦ deriv (polygonFun poly) t • f (polygonFun poly t))
    fun k hk ↦ hint.mono_set (uIcc_subset_uIcc
      (by rw [uIcc_of_le (Nat.cast_nonneg n)]; exact ⟨Nat.cast_nonneg k, by exact_mod_cast hk.le⟩)
      (by rw [uIcc_of_le (Nat.cast_nonneg n)]
          exact ⟨Nat.cast_nonneg _, by exact_mod_cast hk⟩))
  simp only [Nat.cast_zero] at hsplit
  rw [← hsplit, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- On the open cell, the curve is the affine edge `i`, with constant derivative.
  have hcell : ∀ t ∈ Icc ((i : ℕ) : ℝ) ((i : ℕ) + 1),
      polygonFun poly t = poly.edgePath ℝ i (t - (i : ℕ)) := fun t ht ↦ by
    rw [← polygonFun_natCast_add poly i ⟨by linarith [ht.1], by linarith [ht.2]⟩,
      add_sub_cancel]
  rw [Nat.cast_succ, intervalIntegral.integral_congr_uIoo (g := fun t ↦
    (poly (finRotate n i) - poly i) • f (poly.edgePath ℝ i (t - (i : ℕ)))) fun t ht ↦ ?_,
    intervalIntegral.integral_smul,
    intervalIntegral.integral_comp_sub_right (fun t ↦ f (poly.edgePath ℝ i t)), sub_self,
    add_sub_cancel_left]
  rw [uIoo_of_le (by linarith)] at ht
  have hnhds : polygonFun poly =ᶠ[nhds t]
      fun u ↦ (u - (i : ℕ)) • (poly (finRotate n i) - poly i) + poly i := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
    rw [hcell u hu, Polygon.edgePath, AffineMap.lineMap_apply_module']
  have hderiv : HasDerivAt (fun u : ℝ ↦ (u - (i : ℕ)) • (poly (finRotate n i) - poly i) + poly i)
      (poly (finRotate n i) - poly i) t := by
    simpa using (((hasDerivAt_id t).sub_const ((i : ℕ) : ℝ)).smul_const
      (poly (finRotate n i) - poly i)).add_const (poly i)
  simp only
  rw [hnhds.deriv_eq, hderiv.deriv, hcell t (Ioo_subset_Icc_self ht)]

/-- **The winding number of a polygon** about a point off its boundary is the sum of the winding
numbers of its edges. -/
theorem _root_.Polygon.windingNumber_contourCycle {z : ℂ} (hz : z ∉ poly.boundary ℝ) :
    Cycle.windingNumber z poly.contourCycle = ∑ i, windingNumber (poly.edgePath ℝ i) 0 1 z := by
  rw [Polygon.contourCycle, Polygon.contourCurve, Cycle.windingNumber_of_raw]
  have hseg (i : Fin n) (t : ℝ)
      (ht : t ∈ Icc (((i.castSucc : Fin (n + 1)) : ℕ) : ℝ) ((i.succ : Fin (n + 1)) : ℕ)) :
      polygonFun poly t = polygonFun poly (i.castSucc : Fin (n + 1)) +
        ((t - (i.castSucc : Fin (n + 1))) /
          ((i.succ : Fin (n + 1)) - (i.castSucc : Fin (n + 1)))) •
          (polygonFun poly (i.succ : Fin (n + 1)) -
            polygonFun poly (i.castSucc : Fin (n + 1))) := by
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_succ] at ht ⊢
    rw [polygonFun, polygonalInterpolation_eq_of_mem_Icc _ one_pos i.isLt (by simpa using ht)]
    have h₀ := polygonalInterpolation_apply_grid (a := 0) (N := n) (vertexSeq poly) one_pos
      i.isLt.le
    have h₁ := polygonalInterpolation_apply_grid (a := 0) (N := n) (vertexSeq poly) one_pos
      i.isLt
    simp only [zero_add, mul_one, Nat.cast_succ] at h₀ h₁
    rw [h₀, h₁]
    simp
  rw [TauCeti.Green.windingNumber_eq_sum_polygon_segments
    (s := fun j : Fin (n + 1) ↦ ((j : ℕ) : ℝ)) (fun _ _ hjk ↦ Nat.cast_lt.2 hjk)
    (by simp) (by simp) hseg (by rwa [image_polygonFun])]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h₀ := polygonFun_natCast_add poly i (s := 0) ⟨le_rfl, zero_le_one⟩
  have h₁ := polygonFun_natCast_add poly i (s := 1) ⟨zero_le_one, le_rfl⟩
  rw [add_zero] at h₀
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_succ]
  rw [h₀, h₁]
  congr 1
  ext t
  simp [Polygon.edgePath, AffineMap.lineMap_apply_module', add_comm]

namespace Cycle

/-- **The cycle of a balanced family of segments.** Let `E` be a finite set of oriented segments,
the pair `e` standing for the segment from `e.1` to `e.2`, such that every point ends as many
segments of `E` as it starts. Then the segments of `E` assemble into a contour cycle: its trace
lies in the union of the segments, its winding number about every point off that union is the sum
of the winding numbers of the segments, and its integral of every function continuous on that
union is the sum of the integrals along the segments. -/
theorem exists_windingNumber_integral_eq_sum_segments {E : Finset (ℂ × ℂ)}
    (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x}) :
    ∃ Γ : Cycle, trace Γ ⊆ ⋃ e ∈ E, segment ℝ e.1 e.2 ∧
      (∀ z ∉ ⋃ e ∈ E, segment ℝ e.1 e.2, windingNumber z Γ =
        ∑ e ∈ E, Contour.windingNumber (AffineMap.lineMap (k := ℝ) e.1 e.2) 0 1 z) ∧
      ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F},
        ContinuousOn f (⋃ e ∈ E, segment ℝ e.1 e.2) → integral f Γ =
          ∑ e ∈ E, (e.2 - e.1) • ∫ t in (0 : ℝ)..1, f (AffineMap.lineMap e.1 e.2 t) := by
  classical
  -- Pair the segments ending at each point with those starting there: this gives a permutation
  -- `σ` of the segments such that `σ e` starts where `e` ends.
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm E, ∀ e, (σ e : ℂ × ℂ).1 = (e : ℂ × ℂ).2 := by
    have hcard (p : ℂ × ℂ → Prop) [DecidablePred p] :
        Fintype.card {e : E // p e} = #{e ∈ E | p e} := by
      rw [Fintype.card_subtype, ← Finset.card_map (Embedding.subtype _)]
      congr 1
      ext e
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Embedding.subtype_apply, Subtype.exists, exists_and_left, exists_prop,
        exists_eq_right_right]
      exact and_comm
    have hfib (x : ℂ) : {e : E // (e : ℂ × ℂ).2 = x} ≃ {e : E // (e : ℂ × ℂ).1 = x} :=
      Fintype.equivOfCardEq (by rw [hcard (fun e ↦ e.2 = x), hcard (fun e ↦ e.1 = x), hE x])
    exact ⟨Equiv.ofFiberEquiv hfib, fun e ↦ Equiv.ofFiberEquiv_map hfib e⟩
  have hk (e : E) : NeZero (minimalPeriod σ e) :=
    ⟨(minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts e)).ne'⟩
  -- Each orbit of `σ` is a closed walk through consecutive segments: a polygon.
  let P (e : E) : Polygon ℂ (minimalPeriod σ e) := ⟨fun i ↦ ((σ^[i] e : E) : ℂ × ℂ).1⟩
  have hP (e : E) (i : Fin (minimalPeriod σ e)) : P e i = ((σ^[i] e : E) : ℂ × ℂ).1 := rfl
  have hPsucc (e : E) (i : Fin (minimalPeriod σ e)) :
      P e (finRotate _ i) = ((σ^[i] e : E) : ℂ × ℂ).2 := by
    have hval : ((i + 1 : Fin (minimalPeriod σ e)) : ℕ) = ((i : ℕ) + 1) % minimalPeriod σ e := by
      simp [Fin.val_add]
    rw [hP, finRotate_apply, hval, iterate_mod_minimalPeriod_eq, iterate_succ_apply', hσ]
  have hedge (e : E) (i : Fin (minimalPeriod σ e)) : (P e).edgePath ℝ i =
      AffineMap.lineMap ((σ^[i] e : E) : ℂ × ℂ).1 ((σ^[i] e : E) : ℂ × ℂ).2 := by
    rw [Polygon.edgePath, hP, hPsucc]
  have hbd (e : E) : (P e).boundary ℝ ⊆ ⋃ e ∈ E, segment ℝ e.1 e.2 := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz
    rw [Polygon.edgeSet_eq_image_edgePath, hedge, ← segment_eq_image_lineMap] at hi
    exact mem_biUnion (σ^[i] e).2 hi
  -- The cycle is the sum of the polygons of the orbits; sums over the segments are computed orbit
  -- by orbit.
  refine ⟨∑ q : Quotient (Equiv.Perm.SameCycle.setoid σ), (P q.out).contourCycle,
    (trace_sum_subset _ _).trans (iUnion₂_subset fun q _ ↦ ?_), fun z hz ↦ ?_, fun hf ↦ ?_⟩
  · rw [Polygon.trace_contourCycle]
    exact hbd _
  · rw [map_sum, ← Finset.sum_coe_sort E, ← Equiv.Perm.sum_quotient_sameCycle_sum_range σ]
    simp only [Equiv.Perm.coe_pow]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Polygon.windingNumber_contourCycle _ fun h ↦ hz (hbd _ h), ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hedge]
  · rw [map_sum, ← Finset.sum_coe_sort E, ← Equiv.Perm.sum_quotient_sameCycle_sum_range σ]
    simp only [Equiv.Perm.coe_pow]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [Polygon.integral_contourCycle _ (hf.mono (hbd _)), ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hedge, hPsucc, hP]

end Cycle

end TauCeti.Contour
