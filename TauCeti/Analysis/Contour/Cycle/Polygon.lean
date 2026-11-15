/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Polygon.Basic
public import TauCeti.Analysis.Contour.Cycle.Basic
public import TauCeti.Geometry.Polygon.Simple
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

* `Polygon.contourCurve poly`: the closed polygonal curve of `poly` on `[0, n]`, given by the
  boundary parametrization `Polygon.boundaryParam`.
* `Polygon.contourCycle poly`: the corresponding one-generator contour cycle.
* `TauCeti.Contour.Cycle.ofBalancedSegments`: the contour cycle assembled from a balanced finite
  family of oriented segments.

## Main results

* `Polygon.trace_contourCycle`: the trace is the boundary of the polygon.
* `Polygon.integral_contourCycle`: the integral of a function continuous on the boundary is the
  sum of its integrals along the edges.
* `Polygon.windingNumber_contourCycle`: off the boundary, the winding number is the sum of the
  winding numbers of the edges.
* `TauCeti.Contour.Cycle.trace_ofBalancedSegments_subset`,
  `TauCeti.Contour.Cycle.windingNumber_ofBalancedSegments`,
  `TauCeti.Contour.Cycle.integral_ofBalancedSegments`: a balanced finite family of oriented
  segments forms a contour cycle with the sums of the segment winding numbers and segment
  integrals as its winding numbers and integrals.

## References

* W. Rudin, *Real and Complex Analysis*, third edition, Theorem 13.5.
* J. B. Conway, *Functions of One Complex Variable I*, second edition, Proposition VIII.1.1.
-/

public section

noncomputable section

open Set MeasureTheory Function Fin.NatCast

open scoped Finset

namespace TauCeti.Contour

variable {n : ℕ} [NeZero n] (poly : Polygon ℂ n)

/-- The boundary parametrization reaches the end point of edge `i` at time `i + 1`. -/
private theorem boundaryParam_natCast_add_one (i : Fin n) :
    poly.boundaryParam ((i : ℕ) + 1) = poly (finRotate n i) := by
  simpa [Polygon.edgePath] using poly.boundaryParam_natCast_add i (s := 1) ⟨zero_le_one, le_rfl⟩

/-- On each cell `[i, i + 1]` the boundary parametrization is the affine interpolation of its
values at the end points, in the form used by polygonal curves. -/
private theorem boundaryParam_eq_of_mem_cell (i : Fin n) (t : ℝ)
    (ht : t ∈ Icc (((i.castSucc : Fin (n + 1)) : ℕ) : ℝ) ((i.succ : Fin (n + 1)) : ℕ)) :
    poly.boundaryParam t = poly.boundaryParam (i.castSucc : Fin (n + 1)) +
      ((t - (i.castSucc : Fin (n + 1))) /
        ((i.succ : Fin (n + 1)) - (i.castSucc : Fin (n + 1)))) •
        (poly.boundaryParam (i.succ : Fin (n + 1)) -
          poly.boundaryParam (i.castSucc : Fin (n + 1))) := by
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_succ] at ht ⊢
  rw [← add_sub_cancel ((i : ℕ) : ℝ) t,
    poly.boundaryParam_natCast_add i ⟨by linarith [ht.1], by linarith [ht.2]⟩,
    poly.boundaryParam_natCast, boundaryParam_natCast_add_one]
  simp [Polygon.edgePath, AffineMap.lineMap_apply_module', add_comm]

/-- On the cell `[i, i + 1]` the boundary parametrization runs along edge `i`. -/
private theorem boundaryParam_eq_edgePath_sub (i : Fin n) {t : ℝ}
    (ht : t ∈ Icc ((i : ℕ) : ℝ) ((i : ℕ) + 1)) :
    poly.boundaryParam t = poly.edgePath ℝ i (t - (i : ℕ)) := by
  rw [← poly.boundaryParam_natCast_add i ⟨by linarith [ht.1], by linarith [ht.2]⟩,
    add_sub_cancel]

/-- On the open cell `(i, i + 1)` the boundary parametrization has the edge vector of edge `i`
as its derivative. -/
private theorem hasDerivAt_boundaryParam (i : Fin n) {t : ℝ}
    (ht : t ∈ Ioo ((i : ℕ) : ℝ) ((i : ℕ) + 1)) :
    HasDerivAt poly.boundaryParam (poly (finRotate n i) - poly i) t := by
  have hderiv : HasDerivAt (fun u : ℝ ↦ (u - (i : ℕ)) • (poly (finRotate n i) - poly i) + poly i)
      (poly (finRotate n i) - poly i) t := by
    simpa using (((hasDerivAt_id t).sub_const ((i : ℕ) : ℝ)).smul_const
      (poly (finRotate n i) - poly i)).add_const (poly i)
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
  rw [boundaryParam_eq_edgePath_sub poly i hu, Polygon.edgePath, AffineMap.lineMap_apply_module']

/-- The boundary parametrization is polygonal on `[0, n]`, with the integers as vertices. -/
theorem _root_.Polygon.isPolygonalOnInterval_boundaryParam :
    IsPolygonalOnInterval poly.boundaryParam 0 n :=
  ⟨n, Nat.pos_of_ne_zero (NeZero.ne n), fun j ↦ ((j : ℕ) : ℝ), fun _ _ hjk ↦ Nat.cast_lt.2 hjk,
    by simp, by simp, boundaryParam_eq_of_mem_cell poly⟩

/-- The image of the parameter interval under the boundary parametrization is the boundary of the
polygon. -/
theorem _root_.Polygon.image_boundaryParam :
    poly.boundaryParam '' uIcc 0 n = poly.boundary ℝ := by
  refine ((image_subset_range _ _).trans poly.range_boundaryParam.subset).antisymm fun z hz ↦ ?_
  obtain ⟨t, ht, rfl⟩ := poly.exists_mem_Ico_boundaryParam_eq hz
  rw [uIcc_of_le (Nat.cast_nonneg n)]
  exact mem_image_of_mem _ (Ico_subset_Icc_self ht)

/-- The closed polygonal curve of a polygon `poly` with `n ≠ 0` vertices, on the parameter
interval `[0, n]`: on `[k, k + 1]` it runs along the edge from vertex `k` to vertex `k + 1`, and
the last edge returns to vertex `0`. It is the boundary parametrization `poly.boundaryParam`
restricted to `[0, n]`. -/
def _root_.Polygon.contourCurve : PiecewiseC1ClosedCurve :=
  PiecewiseC1ClosedCurve.of poly.boundaryParam
    poly.isPolygonalOnInterval_boundaryParam.isPiecewiseC1On
    (by simpa using (poly.periodic_boundaryParam 0).symm)

/-- The polygonal curve of a polygon is its boundary parametrization, bundled on `[0, n]`. -/
theorem _root_.Polygon.contourCurve_def :
    poly.contourCurve = PiecewiseC1ClosedCurve.of poly.boundaryParam
      poly.isPolygonalOnInterval_boundaryParam.isPiecewiseC1On
      (by simpa using (poly.periodic_boundaryParam 0).symm) := (rfl)

/-- The polygonal curve starts at the parameter `0`. -/
@[simp]
theorem _root_.Polygon.contourCurve_a : poly.contourCurve.a = 0 := by
  rw [Polygon.contourCurve, PiecewiseC1ClosedCurve.of_a]

/-- The polygonal curve ends at the parameter `n`. -/
@[simp]
theorem _root_.Polygon.contourCurve_b : poly.contourCurve.b = n := by
  rw [Polygon.contourCurve, PiecewiseC1ClosedCurve.of_b]

/-- On `[0, n]` the polygonal curve is the boundary parametrization of the polygon. -/
theorem _root_.Polygon.contourCurve_apply {t : ℝ} (ht : t ∈ Icc (0 : ℝ) n) :
    poly.contourCurve t = poly.boundaryParam t := by
  rw [Polygon.contourCurve, PiecewiseC1ClosedCurve.of_apply _ _ _
    (by rwa [uIcc_of_le (Nat.cast_nonneg n)])]

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
  rw [Polygon.contourCycle, Polygon.contourCurve, Cycle.trace_of_raw, Polygon.image_boundaryParam]

/-- **The integral over a polygon** of a function continuous on its boundary is the sum over the
edges `[v, w]` of `(w - v) • ∫ t in 0..1, f (v + t (w - v))`. -/
theorem _root_.Polygon.integral_contourCycle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : ContinuousOn f (poly.boundary ℝ)) :
    Cycle.integral f poly.contourCycle =
      ∑ i, (poly (finRotate n i) - poly i) • ∫ t in (0 : ℝ)..1, f (poly.edgePath ℝ i t) := by
  have hγ := poly.isPolygonalOnInterval_boundaryParam.isPiecewiseC1On
  have hint := hγ.intervalIntegrable_deriv_smul_comp_of_mapsTo hf
    (mapsTo_iff_image_subset.2 poly.image_boundaryParam.subset)
  rw [Polygon.contourCycle, Polygon.contourCurve, Cycle.integral_of_raw]
  -- Split the integral over `[0, n]` into the integrals over the cells `[i, i + 1]`.
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ ↦ (k : ℝ))
    (n := n) (μ := volume) (f := fun t ↦ deriv poly.boundaryParam t • f (poly.boundaryParam t))
    fun k hk ↦ hint.mono_set (uIcc_subset_uIcc
      (by rw [uIcc_of_le (Nat.cast_nonneg n)]; exact ⟨Nat.cast_nonneg k, by exact_mod_cast hk.le⟩)
      (by rw [uIcc_of_le (Nat.cast_nonneg n)]
          exact ⟨Nat.cast_nonneg _, by exact_mod_cast hk⟩))
  simp only [Nat.cast_zero] at hsplit
  rw [← hsplit, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- On the open cell, the curve is the affine edge `i`, with constant derivative.
  rw [Nat.cast_succ, intervalIntegral.integral_congr_uIoo (g := fun t ↦
    (poly (finRotate n i) - poly i) • f (poly.edgePath ℝ i (t - (i : ℕ)))) fun t ht ↦ ?_,
    intervalIntegral.integral_smul,
    intervalIntegral.integral_comp_sub_right (fun t ↦ f (poly.edgePath ℝ i t)), sub_self,
    add_sub_cancel_left]
  rw [uIoo_of_le (by linarith)] at ht
  simp only
  rw [(hasDerivAt_boundaryParam poly i ht).deriv,
    boundaryParam_eq_edgePath_sub poly i (Ioo_subset_Icc_self ht)]

/-- **The winding number of a polygon** about a point off its boundary is the sum of the winding
numbers of its edges. -/
theorem _root_.Polygon.windingNumber_contourCycle {z : ℂ} (hz : z ∉ poly.boundary ℝ) :
    Cycle.windingNumber z poly.contourCycle = ∑ i, windingNumber (poly.edgePath ℝ i) 0 1 z := by
  rw [Polygon.contourCycle, Polygon.contourCurve, Cycle.windingNumber_of_raw]
  rw [TauCeti.Green.windingNumber_eq_sum_polygon_segments
    (s := fun j : Fin (n + 1) ↦ ((j : ℕ) : ℝ)) (fun _ _ hjk ↦ Nat.cast_lt.2 hjk)
    (by simp) (by simp) (boundaryParam_eq_of_mem_cell poly) (by rwa [Polygon.image_boundaryParam])]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_succ]
  rw [poly.boundaryParam_natCast, boundaryParam_natCast_add_one]
  congr 1
  ext t
  simp [Polygon.edgePath, AffineMap.lineMap_apply_module', add_comm]

namespace Cycle

section BalancedSegments

variable {E : Finset (ℂ × ℂ)}

private theorem exists_perm_of_balanced (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x}) :
    ∃ σ : Equiv.Perm E, ∀ e, (σ e : ℂ × ℂ).1 = (e : ℂ × ℂ).2 := by
  classical
  have hcard (p : ℂ × ℂ → Prop) [DecidablePred p] :
      Fintype.card {e : E // p e} = #{e ∈ E | p e} := by
    simp [Fintype.card_subtype, Finset.filter_attach]
  have hfib (x : ℂ) : {e : E // (e : ℂ × ℂ).2 = x} ≃ {e : E // (e : ℂ × ℂ).1 = x} :=
    Fintype.equivOfCardEq (by rw [hcard (fun e ↦ e.2 = x), hcard (fun e ↦ e.1 = x), hE x])
  exact ⟨Equiv.ofFiberEquiv hfib, fun e ↦ Equiv.ofFiberEquiv_map hfib e⟩

private def balancedPerm (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x}) : Equiv.Perm E :=
  (exists_perm_of_balanced hE).choose

private theorem balancedPerm_fst (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x}) (e : E) :
    (balancedPerm hE e : ℂ × ℂ).1 = (e : ℂ × ℂ).2 :=
  (exists_perm_of_balanced hE).choose_spec e

private instance instNeZeroMinimalPeriodBalancedPerm
    (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x}) (e : E) :
    NeZero (minimalPeriod (balancedPerm hE) e) :=
  ⟨(minimalPeriod_pos_of_mem_periodicPts ((balancedPerm hE).injective.mem_periodicPts e)).ne'⟩

private def balancedOrbitPolygon (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x}) (e : E) :
    Polygon ℂ (minimalPeriod (balancedPerm hE) e) :=
  ⟨fun i ↦ (((balancedPerm hE)^[i] e : E) : ℂ × ℂ).1⟩

private theorem balancedOrbitPolygon_apply (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x})
    (e : E) (i : Fin (minimalPeriod (balancedPerm hE) e)) :
    balancedOrbitPolygon hE e i = (((balancedPerm hE)^[i] e : E) : ℂ × ℂ).1 := rfl

private theorem balancedOrbitPolygon_succ (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x})
    (e : E) (i : Fin (minimalPeriod (balancedPerm hE) e)) :
    balancedOrbitPolygon hE e (finRotate _ i) = (((balancedPerm hE)^[i] e : E) : ℂ × ℂ).2 := by
  have hval : ((i + 1 : Fin (minimalPeriod (balancedPerm hE) e)) : ℕ) =
      ((i : ℕ) + 1) % minimalPeriod (balancedPerm hE) e := by
    simp [Fin.val_add]
  rw [balancedOrbitPolygon_apply, finRotate_apply, hval, iterate_mod_minimalPeriod_eq,
    iterate_succ_apply', balancedPerm_fst]

private theorem balancedOrbitPolygon_edgePath (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x})
    (e : E) (i : Fin (minimalPeriod (balancedPerm hE) e)) :
    (balancedOrbitPolygon hE e).edgePath ℝ i =
      AffineMap.lineMap (((balancedPerm hE)^[i] e : E) : ℂ × ℂ).1
        (((balancedPerm hE)^[i] e : E) : ℂ × ℂ).2 := by
  rw [Polygon.edgePath, balancedOrbitPolygon_succ]
  rfl

private theorem balancedOrbitPolygon_boundary_subset
    (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x}) (e : E) :
    (balancedOrbitPolygon hE e).boundary ℝ ⊆ ⋃ e ∈ E, segment ℝ e.1 e.2 := by
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.1 hz
  rw [Polygon.edgeSet_eq_image_edgePath, balancedOrbitPolygon_edgePath,
    ← segment_eq_image_lineMap] at hi
  exact mem_biUnion ((balancedPerm hE)^[i] e).2 hi

/-- **The contour cycle of a balanced family of segments.** Given a finite set `E` of oriented
segments in which every point ends as many segments as it starts, matching incoming and outgoing
segments decomposes `E` into closed polygonal orbits; `ofBalancedSegments hE` is the sum of the
corresponding polygon cycles. -/
def ofBalancedSegments (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x}) : Cycle := by
  classical
  exact ∑ q : Quotient (Equiv.Perm.SameCycle.setoid (balancedPerm hE)),
    (balancedOrbitPolygon hE q.out).contourCycle

/-- The trace of `ofBalancedSegments` lies in the union of the segments of `E`. -/
theorem trace_ofBalancedSegments_subset (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x}) :
    trace (ofBalancedSegments hE) ⊆ ⋃ e ∈ E, segment ℝ e.1 e.2 := by
  classical
  refine (trace_sum_subset _ _).trans (iUnion₂_subset fun q _ ↦ ?_)
  rw [Polygon.trace_contourCycle]
  exact balancedOrbitPolygon_boundary_subset hE q.out

/-- Off the union of the segments, the winding number of `ofBalancedSegments` is the sum of the
winding numbers of the segments. -/
theorem windingNumber_ofBalancedSegments (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x})
    {z : ℂ} (hz : z ∉ ⋃ e ∈ E, segment ℝ e.1 e.2) :
    windingNumber z (ofBalancedSegments hE) =
      ∑ e ∈ E, Contour.windingNumber (AffineMap.lineMap (k := ℝ) e.1 e.2) 0 1 z := by
  classical
  rw [ofBalancedSegments, map_sum, ← Finset.sum_coe_sort E,
    ← Equiv.Perm.sum_quotient_sameCycle_sum_range (balancedPerm hE)]
  simp only [Equiv.Perm.coe_pow]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [Polygon.windingNumber_contourCycle _ fun h ↦
      hz (balancedOrbitPolygon_boundary_subset hE q.out h),
    ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [balancedOrbitPolygon_edgePath]

/-- The integral over `ofBalancedSegments` of any continuous vector-valued function on the union of
the segments is the sum of its integrals along the segments, in any universe. -/
theorem integral_ofBalancedSegments (hE : ∀ x, #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x})
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F}
    (hf : ContinuousOn f (⋃ e ∈ E, segment ℝ e.1 e.2)) :
    integral f (ofBalancedSegments hE) =
      ∑ e ∈ E, (e.2 - e.1) • ∫ t in (0 : ℝ)..1, f (AffineMap.lineMap e.1 e.2 t) := by
  classical
  rw [ofBalancedSegments, map_sum, ← Finset.sum_coe_sort E,
    ← Equiv.Perm.sum_quotient_sameCycle_sum_range (balancedPerm hE)]
  simp only [Equiv.Perm.coe_pow]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [Polygon.integral_contourCycle _ (hf.mono (balancedOrbitPolygon_boundary_subset hE q.out)),
    ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [balancedOrbitPolygon_edgePath, balancedOrbitPolygon_succ]
    rfl

end BalancedSegments

end Cycle

end TauCeti.Contour
