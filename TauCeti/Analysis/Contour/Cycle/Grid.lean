/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Basic
public import TauCeti.Analysis.Contour.Grid
import Mathlib.Topology.Algebra.Module.Cardinality
import TauCeti.Analysis.Contour.Cycle.Polygon
import TauCeti.Analysis.Contour.Cycle.Winding
import TauCeti.Analysis.Contour.Winding.Number.Segment.Bounds
import TauCeti.Analysis.Contour.Winding.StarConvex
import TauCeti.Analysis.Green.Polygonal.Geometry

/-!
# A cycle winding once around a compact set

Let `K` be a compact subset of an open set `G ⊆ ℂ`. This file constructs a contour cycle `Γ` in
`G \ K` that winds once around every point of `K` and is null-homologous in `G`. Such cycles are
the contours of the Cauchy integral formula for compact sets and of the holomorphic functional
calculus, where `K` is the spectrum of an element of a Banach algebra and `G` is the domain of
the function applied to it.

The construction is the classical one by grid squares. For `δ > 0`, take the closed squares of
side `δ` of the lattice `δ (ℤ + ℤ i)` that meet `K`, and the four positively oriented edges of
each. An edge shared by two of these squares occurs once in each direction; discarding all such
pairs leaves the edges whose square across the edge misses `K`. These lie in the union of the
squares and avoid `K`. Every lattice point still ends as many of the remaining edges as it
starts, so they assemble into a contour cycle. Off the grid lines, the winding number of that
cycle is the sum of the winding numbers of the boundaries of the squares, since the discarded
pairs cancel, and so it is `1` on the union of the squares and `0` outside it. Local constancy of
winding numbers off the trace extends this to the points of `K` and to the points outside the
union. For small `δ` the union lies in `G`.

## Main results

* `TauCeti.Contour.exists_cycle_trace_subset_gridCover`: for `δ > 0` and bounded `K`, there is a
  cycle in `gridCover δ K \ K` winding once around every point of `K` and not at all around any
  point outside `gridCover δ K`.
* `IsCompact.exists_cycle_windingNumber_eq_one`: for a compact subset `K` of an open set `G`,
  there is a cycle in `G \ K`, null-homologous in `G`, winding once around every point of `K`.

## References

* W. Rudin, *Real and Complex Analysis*, third edition, Theorem 13.5.
* J. B. Conway, *Functions of One Complex Variable I*, second edition, Proposition VIII.1.1.
-/

public section

noncomputable section

open Set Metric Function Complex

open scoped Finset

namespace TauCeti.Contour

variable {δ : ℝ} {K : Set ℂ} {z : ℂ}

/-! ### Lattice squares and their edges -/

/-- The corners of the unit lattice square with lower left corner `p`, counterclockwise. -/
private def corner (p : ℤ × ℤ) : Fin 4 → ℤ × ℤ :=
  ![p, p + (1, 0), p + (1, 1), p + (0, 1)]

/-- The unit lattice square on the other side of the edge of the square `p` from corner `i` to
corner `i + 1`. -/
private def neighbour (p : ℤ × ℤ) : Fin 4 → ℤ × ℤ :=
  ![p - (0, 1), p + (1, 0), p + (0, 1), p - (1, 0)]

/-- The edge from corner `i` to corner `i + 1` of the square `p`, traversed backwards, is the edge
from corner `i + 2` to corner `i + 3` of its neighbour across that edge. -/
private theorem corner_neighbour (p : ℤ × ℤ) (i : Fin 4) :
    corner (neighbour p i) (i + 2) = corner p (i + 1) ∧
      corner (neighbour p i) (i + 2 + 1) = corner p i := by
  fin_cases i <;> constructor <;> ext <;> simp [corner, neighbour]

/-- Crossing an edge twice returns to the original square. -/
private theorem neighbour_neighbour (p : ℤ × ℤ) (i : Fin 4) :
    neighbour (neighbour p i) (i + 2) = p := by
  fin_cases i <;> ext <;> simp [neighbour]

/-- An oriented lattice edge determines the square to its left and its position in that square. -/
private theorem injective_corner :
    Injective fun t : (ℤ × ℤ) × Fin 4 ↦ (corner t.1 t.2, corner t.1 (t.2 + 1)) := by
  rintro ⟨p, i⟩ ⟨q, j⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h₁, h₂⟩ := h
  fin_cases i <;> fin_cases j <;>
    simp [corner, Prod.ext_iff] at h₁ h₂ ⊢ <;> omega

/-- The edges `(p, i)` of the squares `p ∈ S` whose neighbouring square across the edge is not
in `S`: the edges left after cancelling the pairs of opposite edges shared by two squares. -/
private def boundaryEdges (S : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × Fin 4) :=
  {t ∈ S ×ˢ Finset.univ | neighbour t.1 t.2 ∉ S}

/-- Exchanging every edge shared by two squares of `S` with its opposite edge: a sum over the
shared edges is unchanged when the summand is replaced by one that agrees with it on opposite
edges. -/
private theorem sum_shared_edges {M : Type*} [AddCommMonoid M] (S : Finset (ℤ × ℤ))
    (F G : (ℤ × ℤ) × Fin 4 → M) (h : ∀ t, G (neighbour t.1 t.2, t.2 + 2) = F t) :
    ∑ t ∈ S ×ˢ Finset.univ with neighbour t.1 t.2 ∈ S, F t =
      ∑ t ∈ S ×ˢ Finset.univ with neighbour t.1 t.2 ∈ S, G t := by
  have hinv (t : (ℤ × ℤ) × Fin 4) :
      (neighbour (neighbour t.1 t.2) (t.2 + 2), t.2 + 2 + 2) = t := by
    rw [neighbour_neighbour, add_assoc, show (2 + 2 : Fin 4) = 0 from rfl, add_zero]
  refine Finset.sum_nbij' (fun t ↦ (neighbour t.1 t.2, t.2 + 2))
    (fun t ↦ (neighbour t.1 t.2, t.2 + 2)) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    (fun t _ ↦ hinv t) (fun t _ ↦ hinv t) fun t _ ↦ (h t).symm
  all_goals
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at ht ⊢
    exact ⟨ht.2, by rw [neighbour_neighbour]; exact ht.1⟩

/-- **The remaining edges are balanced**: summed over the boundary edges, a function of the end
points agrees with the same function of the starting points. -/
private theorem sum_boundaryEdges_corner_succ (S : Finset (ℤ × ℤ)) (f : ℤ × ℤ → ℕ) :
    ∑ t ∈ boundaryEdges S, f (corner t.1 (t.2 + 1)) =
      ∑ t ∈ boundaryEdges S, f (corner t.1 t.2) := by
  -- Every square boundary is balanced: rotating the four corners permutes them.
  have hall : ∑ t ∈ S ×ˢ Finset.univ, f (corner t.1 (t.2 + 1)) =
      ∑ t ∈ S ×ˢ Finset.univ, f (corner t.1 t.2) := by
    rw [Finset.sum_product, Finset.sum_product]
    exact Finset.sum_congr rfl fun p _ ↦
      (Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ ↦ rfl)
  -- The shared edges come in opposite pairs, so they are balanced too.
  have hshared := sum_shared_edges S (fun t ↦ f (corner t.1 (t.2 + 1)))
    (fun t ↦ f (corner t.1 t.2)) fun t ↦ congrArg f (corner_neighbour t.1 t.2).1
  rw [← Finset.sum_filter_add_sum_filter_not (S ×ˢ Finset.univ)
      (fun t ↦ neighbour t.1 t.2 ∈ S) (fun t ↦ f (corner t.1 (t.2 + 1))),
    ← Finset.sum_filter_add_sum_filter_not (S ×ˢ Finset.univ)
      (fun t ↦ neighbour t.1 t.2 ∈ S) (fun t ↦ f (corner t.1 t.2)), hshared] at hall
  exact add_left_cancel hall

/-! ### Grid edges in the plane -/

/-- The lattice point `q` of the grid `δ (ℤ + ℤ i)`. -/
private def gridPoint (δ : ℝ) (q : ℤ × ℤ) : ℂ :=
  ⟨δ * q.1, δ * q.2⟩

@[simp]
private theorem gridPoint_re (q : ℤ × ℤ) : (gridPoint δ q).re = δ * q.1 :=
  rfl

@[simp]
private theorem gridPoint_im (q : ℤ × ℤ) : (gridPoint δ q).im = δ * q.2 :=
  rfl

/-- For `δ ≠ 0`, distinct lattice points give distinct grid points. -/
private theorem injective_gridPoint (hδ : δ ≠ 0) : Injective (gridPoint δ) := by
  intro q q' h
  have hre := congrArg re h
  have him := congrArg im h
  simp only [gridPoint_re, gridPoint_im, mul_right_inj' hδ, Int.cast_inj] at hre him
  exact Prod.ext hre him

/-- The edge from corner `t.2` to corner `t.2 + 1` of the grid square `t.1`, as a pair of points
of the plane. -/
private def gridEdge (δ : ℝ) (t : (ℤ × ℤ) × Fin 4) : ℂ × ℂ :=
  (gridPoint δ (corner t.1 t.2), gridPoint δ (corner t.1 (t.2 + 1)))

/-- For `δ ≠ 0`, distinct edges of grid squares are distinct oriented segments. -/
private theorem injective_gridEdge (hδ : δ ≠ 0) : Injective (gridEdge δ) :=
  fun _ _ h ↦ injective_corner (Prod.map_injective.2
    ⟨injective_gridPoint hδ, injective_gridPoint hδ⟩ h)

/-- The opposite of an edge is the corresponding edge of the neighbouring square. -/
private theorem gridEdge_neighbour (t : (ℤ × ℤ) × Fin 4) :
    gridEdge δ (neighbour t.1 t.2, t.2 + 2) = (gridEdge δ t).swap := by
  simp only [gridEdge, Prod.swap_prod_mk, (corner_neighbour t.1 t.2).1,
    (corner_neighbour t.1 t.2).2]

/-- The corners of a grid square lie in it. -/
private theorem gridPoint_corner_mem_gridSquare (hδ : 0 ≤ δ) (p : ℤ × ℤ) (i : Fin 4) :
    gridPoint δ (corner p i) ∈ gridSquare δ p := by
  fin_cases i <;> simp [mem_gridSquare, corner] <;> constructor <;> nlinarith

/-- An edge of a grid square lies in that square. -/
private theorem segment_gridEdge_subset (hδ : 0 ≤ δ) (t : (ℤ × ℤ) × Fin 4) :
    segment ℝ (gridEdge δ t).1 (gridEdge δ t).2 ⊆ gridSquare δ t.1 :=
  (convex_gridSquare δ t.1).segment_subset (gridPoint_corner_mem_gridSquare hδ _ _)
    (gridPoint_corner_mem_gridSquare hδ _ _)

/-- An edge of a grid square also lies in the neighbouring square across it. -/
private theorem segment_gridEdge_subset_neighbour (hδ : 0 ≤ δ) (t : (ℤ × ℤ) × Fin 4) :
    segment ℝ (gridEdge δ t).1 (gridEdge δ t).2 ⊆ gridSquare δ (neighbour t.1 t.2) := by
  have h := segment_gridEdge_subset hδ (neighbour t.1 t.2, t.2 + 2)
  rwa [gridEdge_neighbour, Prod.fst_swap, Prod.snd_swap, segment_symm] at h

/-! ### Points off the grid lines -/

/-- A point lies off the grid lines of `δ (ℤ + ℤ i)` when neither its real nor its imaginary part
is an integer multiple of `δ`. -/
private def OffGrid (δ : ℝ) (z : ℂ) : Prop :=
  (∀ m : ℤ, z.re ≠ δ * m) ∧ ∀ m : ℤ, z.im ≠ δ * m

/-- Every ball contains points off the grid lines. -/
private theorem exists_offGrid_mem_ball (δ : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ w ∈ ball z r, OffGrid δ w := by
  -- Move diagonally from `z` by a real amount `t` avoiding countably many values.
  have hC : (range (fun m : ℤ ↦ δ * m - z.re) ∪ range fun m : ℤ ↦ δ * m - z.im).Countable :=
    (countable_range _).union (countable_range _)
  obtain ⟨t, ht, htr⟩ := (hC.dense_compl ℝ).exists_between (half_pos hr)
  refine ⟨z + (t + t * I), ?_, fun m h ↦ ht (Or.inl ⟨m, ?_⟩), fun m h ↦ ht (Or.inr ⟨m, ?_⟩)⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    calc ‖(t : ℂ) + t * I‖ ≤ ‖(t : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 2 * t := by simp [abs_of_pos htr.1]; ring
      _ < r := by linarith [htr.2]
  · linarith [show (z + (t + t * I)).re = z.re + t by simp]
  · linarith [show (z + (t + t * I)).im = z.im + t by simp]

/-- A point off the grid lines lies on no grid edge: each edge stays on a horizontal or a
vertical grid line. -/
private theorem OffGrid.notMem_segment (hz : OffGrid δ z) (t : (ℤ × ℤ) × Fin 4) :
    z ∉ segment ℝ (gridEdge δ t).1 (gridEdge δ t).2 := by
  obtain ⟨p, i⟩ := t
  intro h
  fin_cases i
  · exact hz.2 p.2 (((convex_singleton _).linear_preimage imLm).segment_subset
      (by simp [gridEdge, corner]) (by simp [gridEdge, corner]) h)
  · exact hz.1 (p.1 + 1) (((convex_singleton _).linear_preimage reLm).segment_subset
      (by simp [gridEdge, corner]) (by simp [gridEdge, corner]) h)
  · exact hz.2 (p.2 + 1) (((convex_singleton _).linear_preimage imLm).segment_subset
      (by simp [gridEdge, corner]) (by simp [gridEdge, corner]) h)
  · exact hz.1 p.1 (((convex_singleton _).linear_preimage reLm).segment_subset
      (by simp [gridEdge, corner]) (by simp [gridEdge, corner]) h)

/-- Off the grid lines, a point lies in exactly one closed grid square, whose index is given by
the integer parts of its coordinates. -/
private theorem OffGrid.mem_gridSquare_iff (hδ : 0 < δ) (hz : OffGrid δ z) {p : ℤ × ℤ} :
    z ∈ gridSquare δ p ↔ p = (⌊z.re / δ⌋, ⌊z.im / δ⌋) := by
  have key (x : ℝ) (hx : ∀ m : ℤ, x ≠ δ * m) (n : ℤ) :
      x ∈ Icc (δ * n) (δ * (n + 1)) ↔ n = ⌊x / δ⌋ := by
    rw [eq_comm, Int.floor_eq_iff, le_div_iff₀ hδ, div_lt_iff₀ hδ, mul_comm (n : ℝ),
      mul_comm ((n : ℝ) + 1)]
    refine ⟨fun h ↦ ⟨h.1, h.2.lt_of_ne ?_⟩, fun h ↦ ⟨h.1, h.2.le⟩⟩
    simpa using hx (n + 1)
  rw [mem_gridSquare, key _ hz.1, key _ hz.2, Prod.ext_iff]

/-! ### Winding numbers of grid squares -/

/-- The straight path from `a` to `b` in the form used by the segment winding lemmas. -/
private theorem coe_lineMap (a b : ℂ) :
    ⇑(AffineMap.lineMap a b : ℝ →ᵃ[ℝ] ℂ) = fun t : ℝ ↦ a + t • (b - a) := by
  funext t
  rw [AffineMap.lineMap_apply_module', add_comm]

/-- The winding number about `z` of the edge `t` of the grid. -/
private def edgeWinding (δ : ℝ) (z : ℂ) (t : (ℤ × ℤ) × Fin 4) : ℂ :=
  windingNumber (AffineMap.lineMap (k := ℝ) (gridEdge δ t).1 (gridEdge δ t).2) 0 1 z

/-- Off the grid lines, opposite edges have opposite winding numbers. -/
private theorem OffGrid.edgeWinding_neighbour (hz : OffGrid δ z) (t : (ℤ × ℤ) × Fin 4) :
    edgeWinding δ z (neighbour t.1 t.2, t.2 + 2) = -edgeWinding δ z t := by
  rw [edgeWinding, edgeWinding, gridEdge_neighbour, Prod.fst_swap, Prod.snd_swap, coe_lineMap,
    coe_lineMap, windingNumber_segment_swap (hz.notMem_segment t)]

/-- The boundary of the grid square `p` as a polygon with four vertices. -/
private def gridPolygon (δ : ℝ) (p : ℤ × ℤ) : Polygon ℂ 4 :=
  ⟨fun i ↦ gridPoint δ (corner p i)⟩

/-- The edges of the polygon of a grid square are its grid edges. -/
private theorem edgePath_gridPolygon (p : ℤ × ℤ) (i : Fin 4) :
    (gridPolygon δ p).edgePath ℝ i =
      AffineMap.lineMap (gridEdge δ (p, i)).1 (gridEdge δ (p, i)).2 := by
  rw [Polygon.edgePath, finRotate_apply]
  rfl

/-- The boundary of the polygon of a grid square is the union of its grid edges. -/
private theorem boundary_gridPolygon (p : ℤ × ℤ) :
    (gridPolygon δ p).boundary ℝ =
      ⋃ i, segment ℝ (gridEdge δ (p, i)).1 (gridEdge δ (p, i)).2 := by
  refine iUnion_congr fun i ↦ ?_
  rw [Polygon.edgeSet_eq_image_edgePath, edgePath_gridPolygon, ← segment_eq_image_lineMap]

/-- Off the grid lines, the winding number of the boundary of a grid square is the sum of the
winding numbers of its edges, and it is an integer. -/
private theorem OffGrid.exists_int_sum_edgeWinding (hz : OffGrid δ z) (p : ℤ × ℤ) :
    ∃ n : ℤ, Cycle.windingNumber z (gridPolygon δ p).contourCycle = n ∧
      ∑ i, edgeWinding δ z (p, i) = n := by
  have hzb : z ∉ (gridPolygon δ p).boundary ℝ := by
    rw [boundary_gridPolygon, mem_iUnion]
    exact fun ⟨i, hi⟩ ↦ hz.notMem_segment (p, i) hi
  obtain ⟨n, hn⟩ := Cycle.exists_int_windingNumber_of_not_mem_trace
    (gridPolygon δ p).contourCycle (by rwa [Polygon.trace_contourCycle])
  refine ⟨n, hn, ?_⟩
  rw [← hn, Polygon.windingNumber_contourCycle _ hzb]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [edgeWinding, edgePath_gridPolygon]

/-- A grid square winds once around each point of its interior that lies off the grid lines. -/
private theorem OffGrid.sum_edgeWinding_eq_one (hδ : 0 < δ) (hz : OffGrid δ z) (p : ℤ × ℤ)
    (hre : z.re ∈ Ioo (δ * p.1) (δ * (p.1 + 1))) (him : z.im ∈ Ioo (δ * p.2) (δ * (p.2 + 1))) :
    ∑ i, edgeWinding δ z (p, i) = 1 := by
  obtain ⟨n, -, hn⟩ := hz.exists_int_sum_edgeWinding p
  -- `z` lies strictly to the left of each edge, which contributes a real part in `(0, 1/2)`.
  have hleft (i : Fin 4) : (edgeWinding δ z (p, i)).re ∈ Ioo 0 (1 / 2) := by
    rw [edgeWinding, coe_lineMap]
    refine windingNumber_segment_re_mem_Ioo ?_
    rw [Green.im_div_sub_eq_triangleDet]
    refine div_pos ?_ ?_ <;> fin_cases i <;>
      simp [Green.triangleDet_def, gridEdge, corner, normSq_apply] at hre him ⊢ <;>
      nlinarith [hre.1, hre.2, him.1, him.2]
  have hsum := congrArg re hn
  simp only [Fin.sum_univ_four, add_re, intCast_re] at hsum
  have h0 := hleft 0
  have h1 := hleft 1
  have h2 := hleft 2
  have h3 := hleft 3
  have hpos : (0 : ℝ) < n := by linarith [h0.1, h1.1, h2.1, h3.1]
  have hlt : (n : ℝ) < 2 := by linarith [h0.2, h1.2, h2.2, h3.2]
  have hn1 : n = 1 := by
    have := Int.cast_pos.1 hpos
    have : n < 2 := by exact_mod_cast hlt
    omega
  rw [hn, hn1, Int.cast_one]

/-- A grid square does not wind around any point outside it that lies off the grid lines. -/
private theorem OffGrid.sum_edgeWinding_eq_zero (hδ : 0 < δ) (hz : OffGrid δ z) {p : ℤ × ℤ}
    (hp : z ∉ gridSquare δ p) :
    ∑ i, edgeWinding δ z (p, i) = 0 := by
  obtain ⟨n, hwind, hn⟩ := hz.exists_int_sum_edgeWinding p
  have hin : Cycle.IsIn (gridPolygon δ p).contourCycle (gridSquare δ p) := by
    rw [Cycle.isIn_iff, Polygon.trace_contourCycle, boundary_gridPolygon]
    exact iUnion_subset fun i ↦ segment_gridEdge_subset hδ.le (p, i)
  have hnull := Cycle.isNullHomologous_of_starConvex
    ((convex_gridSquare δ p).starConvex (gridPoint_corner_mem_gridSquare hδ.le p 0)) hin
  rw [hn, ← hwind, Cycle.isNullHomologous_iff.1 hnull z hp]

/-- **Cancellation of shared edges.** Off the grid lines, the sum of the winding numbers of the
boundary edges of a finite set `S` of grid squares is `1` if the point lies in a square of `S`,
and `0` otherwise. -/
private theorem OffGrid.sum_boundaryEdges_edgeWinding (hδ : 0 < δ) (hz : OffGrid δ z)
    (S : Finset (ℤ × ℤ)) :
    ∑ t ∈ boundaryEdges S, edgeWinding δ z t =
      if (⌊z.re / δ⌋, ⌊z.im / δ⌋) ∈ S then 1 else 0 := by
  -- The shared edges come in opposite pairs, whose winding numbers cancel.
  have hshared : ∑ t ∈ S ×ˢ Finset.univ with neighbour t.1 t.2 ∈ S, edgeWinding δ z t = 0 := by
    have h := sum_shared_edges S (edgeWinding δ z) (fun t ↦ -edgeWinding δ z t)
      fun t ↦ by rw [hz.edgeWinding_neighbour, neg_neg]
    rw [Finset.sum_neg_distrib] at h
    exact self_eq_neg.1 h
  -- The square boundaries sum to the indicator of their union.
  have hall : ∑ t ∈ S ×ˢ Finset.univ, edgeWinding δ z t =
      if (⌊z.re / δ⌋, ⌊z.im / δ⌋) ∈ S then 1 else 0 := by
    rw [Finset.sum_product, ← Finset.sum_ite_eq' S _ fun _ ↦ (1 : ℂ)]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    split_ifs with hp
    · subst hp
      have hre := mem_Icc_mul_floor_div hδ z.re
      have him := mem_Icc_mul_floor_div hδ z.im
      exact hz.sum_edgeWinding_eq_one hδ _
        ⟨hre.1.lt_of_ne (hz.1 _).symm, hre.2.lt_of_ne (by simpa using hz.1 (⌊z.re / δ⌋ + 1))⟩
        ⟨him.1.lt_of_ne (hz.2 _).symm, him.2.lt_of_ne (by simpa using hz.2 (⌊z.im / δ⌋ + 1))⟩
    · exact hz.sum_edgeWinding_eq_zero hδ fun h ↦ hp ((hz.mem_gridSquare_iff hδ).1 h)
  rw [← Finset.sum_filter_add_sum_filter_not (S ×ˢ Finset.univ)
    (fun t ↦ neighbour t.1 t.2 ∈ S), hshared, zero_add] at hall
  exact hall

/-! ### The cycle -/

/-- The union of the boundary edges of a finite set `S` of grid squares. -/
private def boundaryEdgeSet (δ : ℝ) (S : Finset (ℤ × ℤ)) : Set ℂ :=
  ⋃ t ∈ boundaryEdges S, segment ℝ (gridEdge δ t).1 (gridEdge δ t).2

/-- **The boundary edges of a finite set of grid squares form a cycle.** Its trace lies on those
edges, and off the grid lines its winding number is `1` on the squares of `S` and `0` elsewhere. -/
private theorem exists_cycle_boundaryEdges (hδ : 0 < δ) (S : Finset (ℤ × ℤ)) :
    ∃ Γ : Cycle, Cycle.trace Γ ⊆ boundaryEdgeSet δ S ∧ ∀ w, OffGrid δ w →
      Cycle.windingNumber w Γ = if (⌊w.re / δ⌋, ⌊w.im / δ⌋) ∈ S then 1 else 0 := by
  classical
  set E := (boundaryEdges S).image (gridEdge δ)
  have hinj : InjOn (gridEdge δ) (boundaryEdges S) := (injective_gridEdge hδ.ne').injOn
  -- Every point of the plane ends as many of the edges as it starts.
  have hbal (x : ℂ) : #{e ∈ E | e.2 = x} = #{e ∈ E | e.1 = x} := by
    simp only [E, Finset.filter_image]
    rw [Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _)),
      Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _)), Finset.card_filter,
      Finset.card_filter]
    exact sum_boundaryEdges_corner_succ S fun q ↦ if gridPoint δ q = x then 1 else 0
  have hE : ⋃ e ∈ E, segment ℝ e.1 e.2 = boundaryEdgeSet δ S := by
    simp only [E, boundaryEdgeSet, Finset.set_biUnion_finset_image]
  obtain ⟨Γ, htrace, hwind, -⟩ := Cycle.exists_windingNumber_integral_eq_sum_segments.{0} hbal
  refine ⟨Γ, hE ▸ htrace, fun w hw ↦ ?_⟩
  have hwU : w ∉ boundaryEdgeSet δ S := by
    simp only [boundaryEdgeSet, mem_iUnion, not_exists]
    exact fun t _ ↦ hw.notMem_segment t
  rw [hwind w (hE ▸ hwU), Finset.sum_image hinj]
  exact hw.sum_boundaryEdges_edgeWinding hδ S

/-- **A grid cycle around a bounded set.** For `δ > 0` and a bounded set `K`, there is a contour
cycle whose trace lies in the union `gridCover δ K` of the grid squares of side `δ` meeting `K`
and avoids `K`, which winds once around every point of `K` and does not wind around any point
outside `gridCover δ K`. -/
theorem exists_cycle_trace_subset_gridCover (hδ : 0 < δ) (hK : Bornology.IsBounded K) :
    ∃ Γ : Cycle, Cycle.trace Γ ⊆ gridCover δ K \ K ∧
      (∀ z ∈ K, Cycle.windingNumber z Γ = 1) ∧
      ∀ z ∉ gridCover δ K, Cycle.windingNumber z Γ = 0 := by
  classical
  set S := (finite_gridIndices hδ hK).toFinset
  obtain ⟨Γ, htrace, hoff⟩ := exists_cycle_boundaryEdges hδ S
  set U := boundaryEdgeSet δ S
  -- The boundary edges lie in a square of `S` and in a square outside `S`, which misses `K`.
  have hU {x : ℂ} (hx : x ∈ U) : x ∈ gridCover δ K ∧ x ∉ K := by
    simp only [U, boundaryEdgeSet, mem_iUnion, exists_prop] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    simp only [boundaryEdges, S, Finset.mem_filter, Finset.mem_product, Set.Finite.mem_toFinset,
      Finset.mem_univ, and_true] at ht
    exact ⟨mem_gridCover.2 ⟨t.1, ht.1, segment_gridEdge_subset hδ.le t hxt⟩, fun hxK ↦
      ht.2 (mem_gridIndices.2 ⟨x, segment_gridEdge_subset_neighbour hδ.le t hxt, hxK⟩)⟩
  have hUclosed : IsClosed U :=
    isClosed_biUnion_finset fun t _ ↦ by
      rw [segment_eq_image_lineMap]
      exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  -- Off the grid lines, the winding number is the indicator of `gridCover δ K`.
  have hind {w : ℂ} (hw : OffGrid δ w) :
      Cycle.windingNumber w Γ = if w ∈ gridCover δ K then 1 else 0 := by
    rw [hoff w hw]
    congr 1
    simp only [S, Set.Finite.mem_toFinset, mem_gridCover]
    exact propext ⟨fun h ↦ ⟨_, h, ((hw.mem_gridSquare_iff hδ).2 rfl)⟩,
      fun ⟨p, hp, hwp⟩ ↦ (hw.mem_gridSquare_iff hδ).1 hwp ▸ hp⟩
  -- Near a point off the trace, the winding number agrees with that at a nearby point off the
  -- grid lines.
  have hnear {z : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball z r ⊆ Uᶜ) :
      ∃ w ∈ ball z r, Cycle.windingNumber z Γ = if w ∈ gridCover δ K then 1 else 0 := by
    obtain ⟨w, hw, hwoff⟩ := exists_offGrid_mem_ball δ z hr
    refine ⟨w, hw, ?_⟩
    rw [← hind hwoff, Cycle.windingNumber_eq_of_mem_connectedComponentIn
      ((convex_ball z r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr)
        (show ball z r ⊆ (Cycle.trace Γ)ᶜ from fun x hx hxΓ ↦ hball hx (htrace hxΓ)) hw)]
  refine ⟨Γ, fun x hx ↦ hU (htrace hx), fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_interior.inter hUclosed.isOpen_compl) z
      ⟨subset_interior_gridCover hδ hz, fun h ↦ (hU h).2 hz⟩
    obtain ⟨w, hw, hzw⟩ := hnear hr fun x hx ↦ (hball hx).2
    simp [hzw, interior_subset (hball hw).1]
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1
      (isCompact_gridCover hδ hK).isClosed.isOpen_compl z hz
    obtain ⟨w, hw, hzw⟩ := hnear hr fun x hx hxU ↦ hball hx (hU hxU).1
    simp [hzw, show w ∉ gridCover δ K from hball hw]

end TauCeti.Contour

open TauCeti.Contour in
/-- **A cycle around a compact set.** If `K` is a compact subset of an open set `G ⊆ ℂ`, there is
a contour cycle in `G \ K` that is null-homologous in `G` and winds once around every point of
`K`. -/
theorem IsCompact.exists_cycle_windingNumber_eq_one {K G : Set ℂ} (hK : IsCompact K)
    (hG : IsOpen G) (hKG : K ⊆ G) :
    ∃ Γ : Cycle, Γ.IsIn (G \ K) ∧ Γ.IsNullHomologous G ∧ ∀ z ∈ K, Cycle.windingNumber z Γ = 1 := by
  obtain ⟨δ, hcover, hδ⟩ :=
    ((hK.eventually_gridCover_subset hG hKG).and self_mem_nhdsWithin).exists
  obtain ⟨Γ, htrace, hK1, hout⟩ := exists_cycle_trace_subset_gridCover hδ hK.isBounded
  exact ⟨Γ, Cycle.isIn_iff.2 fun x hx ↦ ⟨hcover (htrace hx).1, (htrace hx).2⟩,
    Cycle.isNullHomologous_iff.2 fun z hz ↦ hout z fun h ↦ hz (hcover h), hK1⟩
