/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Polygon.DeltaMove
public import TauCeti.Geometry.Polygon.Subdivision
public import TauCeti.KnotTheory.GaussCode.Polygon.Basic
import TauCeti.Analysis.Convex.Combination
import TauCeti.LinearAlgebra.AffineSpace.Triangle.Exit
import TauCeti.Order.Monotone.Basic

/-!
# Δ-moves that do not change the Gauss code

A Δ-move (`Polygon.IsDeltaMove`) replaces edge `i` of a polygonal knot `poly`, from vertex `i` to
the next vertex, by the two other sides of a triangle through a new vertex `c`: the polygon becomes
`poly.insertVertex i c`. In the argument that diagrams of combinatorially equivalent polygonal
knots are related by Reidemeister moves (Lickorish, Chapter 1; Burde–Zieschang, Chapter 1), the
Δ-moves are cut into small ones, and the effect of each on the diagram is read off from how the
projection of its triangle meets the rest of the diagram. This file treats the two cases in which
the diagram only changes by a planar isotopy, so that the Gauss code is unchanged.

**No strand meets the moved edges** (`Polygon.gaussCode_insertVertex_of_disjoint`): if, for the
projection along `d`, edge `i` of `poly` contains no double point, and the two sides through `c`
contain no double point of `poly.insertVertex i c`, then the two Gauss codes are equal whenever the
projection is regular for both polygons. The Δ-move condition itself is not needed: the hypotheses
only concern the edges that change. Under these hypotheses both polygons have the same double
points (`Polygon.doublePoints_insertVertex_of_disjoint`), lying on the edges they share, and away
from edge `i` the two traversals differ by an increasing change of time running along the same
edges (`Polygon.exists_strictMono_boundaryParam_insertVertex`). So the crossing times correspond in
order, at the same points and along edges with the same directions, and
`Polygon.gaussCode_eq_of_strictMono` applies.

**One strand slides across the triangle** (`Polygon.gaussCode_insertVertex_of_crossing`): suppose
that the triangle `D = a a' c`, with `a = poly i` and `a'` the next vertex, projects onto a
nondegenerate triangle `T`, that edge `j` crosses edge `i` in the diagram, and that apart from edges
`i` and `j` the polygon meets the prism over `T` only in `a` and `a'`. Read edge `j` in the
barycentric coordinates of `T` (Mathlib's `AffineBasis.coord`); along the edge they are affine
functions of the parameter. The edge enters `T` across the side `a a'` and its endpoints lie outside
`T`, so it leaves `T` across one of the two other sides, the projections of the new edges, at a
single point, which is not a vertex (`TauCeti.exists_triangle_exit`). So after the move edge `j`
crosses the new edges exactly once, at the point `y` of the new edges over the point `y'` where it
leaves `T`, and every other crossing is unchanged. The crossing has only slid along edge `j`, from
`x'` to `y'`, past no other crossing, and from `x` on edge `i` to `y`. It stays on the same side:
the segment from `x` to `y` lies in `D` and the segment from `x'` to `y'` on edge `j`, which `D`
does not meet, so their difference never crosses zero along the way
(`Affine.Simplex.pos_iff_pos_of_disjoint`). It keeps its sign: the determinant of the edge
directions with `d`, as a function of the direction of the moving strand, vanishes on `y - x`, and
this forces the old and new directions `a' - a` and `c - a` (or `a' - c`) to give determinants of
the same sign. The codes are then compared by `Polygon.gaussCode_eq_of_strictMonoOn`, which allows
crossing points to move.

## Main results

* `Polygon.gaussCode_insertVertex_of_disjoint`: a Δ-move whose moved edges carry no crossings does
  not change the Gauss code of a regular projection.
* `Polygon.gaussCode_insertVertex_of_crossing`: a Δ-move across which a single strand of the
  diagram slides does not change the Gauss code of a regular projection.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, for Δ-moves and the Reidemeister moves they induce on regular projections.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1,
  pp. 2–4, for triangle moves and their effect on link diagrams.
-/

public section

open Set Function AffineMap Module TauCeti

namespace Polygon

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P] {n : ℕ} [NeZero n]
  {poly : Polygon P n} {p₀ : P} {d : V}

/-- **A Δ-move away from the crossings does not change the Gauss code.** Let `poly` be a simple
polygon in a three-dimensional real affine space, and `poly.insertVertex i c` the simple polygon in
which edge `i` is replaced by the segments from vertex `i` to `c` and from `c` to the next vertex.
Suppose that the projection along `d` is regular for both polygons, that edge `i` of `poly`
contains no double point of `poly`, and that the two new segments contain no double point of
`poly.insertVertex i c`. Then the two polygons have the same Gauss code. The numbers of crossings
agree, and the codes are compared together with them. -/
theorem gaussCode_insertVertex_of_disjoint (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i : Fin n} {c : P}
    (hs' : (poly.insertVertex i c).IsSimple ℝ)
    (hπ' : (poly.insertVertex i c).IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (hu : Disjoint (poly.edgeSet ℝ i) (poly.doublePoints ℝ (projAlong ℝ p₀ d)))
    (hvw : Disjoint (affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i)))
      ((poly.insertVertex i c).doublePoints ℝ (projAlong ℝ p₀ d)))
    (b : Basis (Fin 3) ℝ V) :
    (⟨_, gaussCode hs' hπ' b⟩ : Σ m, BasedOrientedGaussCode m) = ⟨_, gaussCode hs hπ b⟩ := by
  obtain ⟨φ, hφ, hφt, -⟩ := exists_strictMono_boundaryParam_insertVertex poly i c
  refine gaussCode_eq_of_strictMono b hs hπ hs' hπ' (doublePoints_insertVertex_of_disjoint hu hvw)
    hφ fun t ht ↦ ?_
  obtain ⟨ht₁, ht₂⟩ := mem_crossingTimes.1 ht
  -- A crossing time is not on edge `i`, which carries no double point.
  have hti : edgeIndexAt n t ≠ i := by
    intro hti
    refine disjoint_left.1 hu ?_ ht₂
    rw [boundaryParam_eq_edgePath_edgeIndexAt, hti]
    exact ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, rfl⟩
  obtain ⟨h₁, h₂, h₃⟩ := hφt t ht₁ hti
  exact ⟨h₁, h₂, 1, one_pos, by rw [h₃, one_smul]⟩

/-! ### A strand sliding across the triangle -/

/-- **A strand sliding across the triangle of a Δ-move does not change the Gauss code.** Let `poly`
be a simple polygon in a three-dimensional real affine space, and `poly.insertVertex i c` the
simple polygon obtained from it by a Δ-move across the triangle `D` with vertices `a = poly i`,
`a' = poly (i + 1)` and `c`. Suppose that the projection `π` along `d` is regular for both
polygons and carries `D` onto a nondegenerate triangle, that edge `j` of `poly` crosses edge `i` in
the diagram, and that every point of another edge projecting into `π D` is `a` or `a'`. Then edge
`j` leaves `π D` across one of the projections of the two new edges, the move slides the crossing
of the two strands from edge `i` to that new edge, and the two polygons have the same Gauss code.
The numbers of crossings agree, and the codes are compared together with them. -/
theorem gaussCode_insertVertex_of_crossing (hs : poly.IsSimple ℝ)
    (hπ : poly.IsRegularProjection ℝ (projAlong ℝ p₀ d)) {i j : Fin n} {c : P}
    (hs' : (poly.insertVertex i c).IsSimple ℝ)
    (hπ' : (poly.insertVertex i c).IsRegularProjection ℝ (projAlong ℝ p₀ d))
    (hΔ : poly.IsDeltaMove ℝ i c)
    (hT : AffineIndependent ℝ ![projAlong ℝ p₀ d (poly i),
      projAlong ℝ p₀ d (poly (finRotate n i)), projAlong ℝ p₀ d c])
    (hprism : ∀ k, k ≠ i → k ≠ j → ∀ z ∈ poly.edgeSet ℝ k,
      projAlong ℝ p₀ d z ∈ projAlong ℝ p₀ d '' hΔ.triangle.closedInterior →
        z = poly i ∨ z = poly (finRotate n i))
    (hcross : ∃ x ∈ poly.edgeSet ℝ i, ∃ x' ∈ poly.edgeSet ℝ j, x ≠ x' ∧
      projAlong ℝ p₀ d x = projAlong ℝ p₀ d x')
    (b : Basis (Fin 3) ℝ V) :
    (⟨_, gaussCode hs' hπ' b⟩ : Σ m, BasedOrientedGaussCode m) = ⟨_, gaussCode hs hπ b⟩ := by
  /- The proof follows edge `j` in barycentric coordinates of the projected triangle until it
  leaves it at `y'`, lifts that point to the point `y` of the new edges, and then compares the two
  diagrams with `gaussCode_eq_of_strictMonoOn`: the crossing `xx`/`x'` of edges `i` and `j` becomes
  the crossing `y`/`y'`, every other crossing is kept, the crossing times are matched by the change
  of time `φ`, and the over/under data and the signs are checked at the moved crossing. -/
  obtain ⟨x, hx, x', hx', hxx', hπx⟩ := hcross
  set π := projAlong ℝ p₀ d with hπdef
  set q := poly.insertVertex i c with hqdef
  set D := hΔ.triangle.closedInterior with hDdef
  have hbdi : poly.edgeSet ℝ i ⊆ poly.boundary ℝ := subset_iUnion (poly.edgeSet ℝ) i
  have hbdj : poly.edgeSet ℝ j ⊆ poly.boundary ℝ := subset_iUnion (poly.edgeSet ℝ) j
  have hxDP : x ∈ poly.doublePoints ℝ π :=
    mem_doublePoints.2 ⟨hbdi hx, x', hbdj hx', hxx'.symm, hπx.symm⟩
  have hx'DP : x' ∈ poly.doublePoints ℝ π := mem_doublePoints.2 ⟨hbdj hx', x, hbdi hx, hxx', hπx⟩
  -- The two edges are distinct and not adjacent.
  have hji : j ≠ i := by
    rintro rfl
    exact hxx' (hπ.injOn_edgeSet j hx hx' hπx)
  -- Edges `i` and `j` cross only once in the diagram, at `x` over `x'`.
  have hsubx {z w₀ : P} (hz : z ∈ poly.edgeSet ℝ i) (hw₀ : w₀ ∈ poly.edgeSet ℝ j)
      (h : π z = π w₀) : z = x ∧ w₀ = x' := by
    have hzw : (z, w₀) ∈
        {p : P × P | p.1 ∈ poly.edgeSet ℝ i ∧ p.2 ∈ poly.edgeSet ℝ j ∧ π p.1 = π p.2} :=
      ⟨hz, hw₀, h⟩
    have hxx'm : (x, x') ∈
        {p : P × P | p.1 ∈ poly.edgeSet ℝ i ∧ p.2 ∈ poly.edgeSet ℝ j ∧ π p.1 = π p.2} :=
      ⟨hx, hx', hπx⟩
    exact Prod.mk.inj (hπ.subsingleton_setOf_mem_edgeSet hs hji.symm hzw hxx'm)
  have hjsucc : j ≠ finRotate n i := by
    rintro rfl
    have h1 := (hsubx (apply_finRotate_mem_edgeSet ℝ poly i)
      (apply_mem_edgeSet_self ℝ poly (finRotate n i)) rfl).1
    exact hπ.apply_notMem_doublePoints _ (h1.symm ▸ hxDP)
  have hisucc : i ≠ finRotate n j := by
    intro h
    have hij : poly i ∈ poly.edgeSet ℝ j := by
      rw [h]
      exact apply_finRotate_mem_edgeSet ℝ poly j
    have h1 := (hsubx (apply_mem_edgeSet_self ℝ poly i) hij rfl).1
    exact hπ.apply_notMem_doublePoints _ (h1.symm ▸ hxDP)
  have ha_j : poly i ∉ poly.edgeSet ℝ j := hs.apply_notMem_edgeSet hji.symm hisucc
  have ha'_j : poly (finRotate n i) ∉ poly.edgeSet ℝ j :=
    hs.apply_notMem_edgeSet hjsucc.symm fun h ↦ hji ((finRotate n).injective h).symm
  -- The crossing points lie in the interiors of their edges.
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨s₀, hs₀, rfl⟩ := hx'
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hπ.apply_notMem_doublePoints i (by simpa using hxDP)
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hπ.apply_notMem_doublePoints _ (by simpa using hxDP)
  have hs00 : s₀ ≠ 0 := by
    rintro rfl
    exact hπ.apply_notMem_doublePoints j (by simpa using hx'DP)
  have hs01 : s₀ ≠ 1 := by
    rintro rfl
    exact hπ.apply_notMem_doublePoints _ (by simpa using hx'DP)
  replace hr : r ∈ Ioo (0 : ℝ) 1 := ⟨hr.1.lt_of_ne' hr0, hr.2.lt_of_ne hr1⟩
  replace hs₀ : s₀ ∈ Ioo (0 : ℝ) 1 := ⟨hs₀.1.lt_of_ne' hs00, hs₀.2.lt_of_ne hs01⟩
  -- The plane of the projection, and barycentric coordinates for the projected triangle.
  have hd : d ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := projAlong_eq_projAlong_iff.1 hπx
    rw [smul_zero, eq_comm, vsub_eq_zero_iff_eq] at ht
    exact hxx' ht
  have : FiniteDimensional ℝ V := Module.Finite.of_basis b
  have hfinQ : finrank ℝ (V ⧸ ℝ ∙ d) = 2 := by
    have h := Submodule.finrank_quotient_add_finrank (ℝ ∙ d)
    rw [finrank_span_singleton hd, finrank_eq_card_basis b, Fintype.card_fin] at h
    omega
  have hspan : affineSpan ℝ (range ![π (poly i), π (poly (finRotate n i)), π c]) = ⊤ :=
    hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 (by rw [Fintype.card_fin, hfinQ])
  let β : AffineBasis (Fin 3) ℝ (V ⧸ ℝ ∙ d) := ⟨_, hT, hspan⟩
  have hβ : ⇑β = ![π (poly i), π (poly (finRotate n i)), π c] := rfl
  -- The vertices of `β` are the projections of the vertices of the triangle.
  have hβ0 : π (poly i) = β 0 := by simp [hβ]
  have hβ1 : π (poly (finRotate n i)) = β 1 := by simp [hβ]
  have hβ2 : π c = β 2 := by simp [hβ]
  -- Points of the triangle are recovered from the coordinates of their projections.
  have hπcomb (w : Fin 3 → ℝ) (hw : ∑ k, w k = 1) :
      π (Finset.univ.affineCombination ℝ hΔ.triangle.points w) =
        Finset.univ.affineCombination ℝ β w := by
    rw [Finset.map_affineCombination _ _ _ hw, IsDeltaMove.triangle_points]
    congr 1
  have hDrep {p : P} (hp : p ∈ D) :
      Finset.univ.affineCombination ℝ hΔ.triangle.points (fun k ↦ β.coord k (π p)) = p ∧
        ∀ k, 0 ≤ β.coord k (π p) := by
    obtain ⟨w, hw, hwI, rfl⟩ := hp
    have hc (k) : β.coord k (π (Finset.univ.affineCombination ℝ hΔ.triangle.points w)) = w k := by
      rw [hπcomb w hw, β.coord_apply_combination_of_mem (Finset.mem_univ k) hw]
    exact ⟨by simp only [hc], fun k ↦ by rw [hc]; exact (hwI k).1⟩
  have hinjD : InjOn π D := fun p₁ hp₁ p₂ hp₂ h ↦ by
    rw [← (hDrep hp₁).1, ← (hDrep hp₂).1, h]
  have hmemT (y : V ⧸ ℝ ∙ d) : y ∈ π '' D ↔ ∀ k, 0 ≤ β.coord k y := by
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨p, hp, rfl⟩
      exact (hDrep hp).2
    · have hsum := β.sum_coord_apply_eq_one y
      rw [Fin.sum_univ_three] at hsum
      have hw : ∑ k, β.coord k y = 1 := β.sum_coord_apply_eq_one y
      refine ⟨_, (Affine.Simplex.affineCombination_mem_closedInterior_iff hw).2
        fun k ↦ ⟨hy k, ?_⟩, ?_⟩
      · fin_cases k <;> simp <;> linarith [hy 0, hy 1, hy 2]
      · rw [hπcomb _ hw, β.affineCombination_coord_eq_self]
  -- The coordinates of a point of a side of the projected triangle.
  have hcl (k l l' : Fin 3) (t : ℝ) : β.coord k (lineMap (β l) (β l') t) =
      lineMap (if k = l then (1 : ℝ) else 0) (if k = l' then 1 else 0) t := by
    rw [(β.coord k).apply_lineMap, β.coord_apply, β.coord_apply]
  -- The coordinates `f k` along edge `j`.
  set f : Fin 3 → ℝ →ᵃ[ℝ] ℝ := fun k ↦ (β.coord k).comp (π.comp (poly.edgePath ℝ j)) with hfdef
  have hf (k : Fin 3) (s : ℝ) : f k s = β.coord k (π (poly.edgePath ℝ j s)) := rfl
  have hsum (s : ℝ) : f 0 s + f 1 s + f 2 s = 1 := by
    have h := β.sum_coord_apply_eq_one (π (poly.edgePath ℝ j s))
    rwa [Fin.sum_univ_three] at h
  have hπx' : π (poly.edgePath ℝ j s₀) = lineMap (β 0) (β 1) r := by
    rw [hβ]
    exact hπx.symm.trans (π.apply_lineMap _ _ r)
  have hf₀ : f 0 s₀ = 1 - r := by rw [hf, hπx', hcl]; simp [lineMap_apply_ring']; ring
  have hf₁ : f 1 s₀ = r := by rw [hf, hπx', hcl]; simp [lineMap_apply_ring']
  have hf₂ : f 2 s₀ = 0 := by rw [hf, hπx', hcl]; simp
  -- The endpoints of edge `j` project outside the triangle.
  have hvj : poly j ∈ poly.edgeSet ℝ j := apply_mem_edgeSet_self ℝ poly j
  have hvj' : poly (finRotate n j) ∈ poly.edgeSet ℝ j := apply_finRotate_mem_edgeSet ℝ poly j
  have hjj : finRotate n j ≠ j := fun h ↦ hs.hasNondegenerateEdges j (by rw [h])
  have hout₀ : π (poly j) ∉ π '' D := by
    intro hm
    set k := (finRotate n).symm j
    have hk : finRotate n k = j := (finRotate n).apply_symm_apply j
    have hki : k ≠ i := fun h ↦ hjsucc (by rw [← hk, h])
    have hkj : k ≠ j := fun h ↦ hjj (by rw [h] at hk; exact hk)
    rcases hprism k hki hkj _ (hk ▸ apply_finRotate_mem_edgeSet ℝ poly k) hm with h | h
    · exact ha_j (h ▸ hvj)
    · exact ha'_j (h ▸ hvj)
  have hout₁ : π (poly (finRotate n j)) ∉ π '' D := by
    intro hm
    rcases hprism _ hisucc.symm hjj _ (apply_mem_edgeSet_self ℝ poly (finRotate n j)) hm with
      h | h
    · exact ha_j (h ▸ hvj')
    · exact ha'_j (h ▸ hvj')
  have hout (s : ℝ) (hs : s ∈ ({0, 1} : Set ℝ)) : ¬ (0 ≤ f 0 s ∧ 0 ≤ f 1 s ∧ 0 ≤ f 2 s) := by
    rintro ⟨h0, h1, h2⟩
    have hm : π (poly.edgePath ℝ j s) ∈ π '' D := (hmemT _).2 fun k ↦ by fin_cases k <;> assumption
    rcases hs with rfl | rfl
    · exact hout₀ (by simpa [edgePath] using hm)
    · exact hout₁ (by simpa [edgePath] using hm)
  -- Edge `j` avoids the projections of the three vertices of the triangle.
  have hpj {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : poly.edgePath ℝ j s ∈ poly.edgeSet ℝ j :=
    ⟨s, hs, rfl⟩
  have hext {s : ℝ} (l : Fin 3) (h : ∀ k, f k s = if k = l then 1 else 0) :
      π (poly.edgePath ℝ j s) = β l :=
    β.ext_elem fun k ↦ by rw [← hf, h, β.coord_apply]
  have hA (s) (hs : s ∈ Icc (0 : ℝ) 1) : ¬ (f 1 s = 0 ∧ f 2 s = 0) := by
    rintro ⟨h1, h2⟩
    have h := hext (s := s) 0 fun k ↦ by fin_cases k <;> simp <;> linarith [hsum s]
    exact ha_j (hπ.eq_vertex_of_apply_eq i (hbdj (hpj hs)) h ▸ hpj hs)
  have hB (s) (hs : s ∈ Icc (0 : ℝ) 1) : ¬ (f 0 s = 0 ∧ f 2 s = 0) := by
    rintro ⟨h0, h2⟩
    have h := hext (s := s) 1 fun k ↦ by fin_cases k <;> simp <;> linarith [hsum s]
    exact ha'_j (hπ.eq_vertex_of_apply_eq _ (hbdj (hpj hs)) h ▸ hpj hs)
  have hjq : poly.edgeSet ℝ j ⊆ q.boundary ℝ := by
    rw [← edgeSet_insertVertex_succAbove poly i c hji]
    exact subset_iUnion (q.edgeSet ℝ) _
  have hcD : c ∈ D := by simpa using hΔ.triangle.point_mem_closedInterior 2
  have hC (s) (hs : s ∈ Icc (0 : ℝ) 1) : ¬ (f 0 s = 0 ∧ f 1 s = 0) := by
    rintro ⟨h0, h1⟩
    have h := hext (s := s) 2 fun k ↦ by fin_cases k <;> simp <;> linarith [hsum s]
    have hc : poly.edgePath ℝ j s = c := by
      have := hπ'.eq_vertex_of_apply_eq i.succ (hjq (hpj hs))
      rw [insertVertex_apply_succ_self] at this
      exact this h
    rcases hΔ.edgeSet_inter_closedInterior_subset hji ⟨hc ▸ hpj hs, hcD⟩ with h | h
    · exact hΔ.left_ne_apex h.symm
    · exact hΔ.apex_ne_right h
  obtain ⟨s₁, hs₁, hs₁₀, hpos₂, hside, huniq, hin⟩ :=
    exists_triangle_exit (f₀ := f 0) (f₁ := f 1) (f₂ := f 2) hsum hs₀ hf₂
      (by rw [hf₀]; linarith [hr.2]) (by rw [hf₁]; exact hr.1) hout hA hB hC
  have hs₁I : s₁ ∈ Icc (0 : ℝ) 1 := ⟨hs₁.1.le, hs₁.2.le⟩
  -- Multiplying by a positive real number does not change the sign.
  have hsignmul {a : ℝ} (ha : 0 < a) (b : ℝ) : SignType.sign (a * b) = SignType.sign b := by
    rw [sign_mul, sign_pos ha, one_mul]
  -- The determinant `L v = det (v, w, d)` against the direction `w` of edge `j`.
  set w := poly (finRotate n j) -ᵥ poly j with hwdef
  obtain ⟨L, hL⟩ : ∃ L : V →ₗ[ℝ] ℝ, ∀ v, L v = b.det ![v, w, d] := by
    refine ⟨b.det.toMultilinearMap.toLinearMap ![0, w, d] 0, fun v ↦ ?_⟩
    rw [MultilinearMap.toLinearMap_apply, AlternatingMap.coe_multilinearMap]
    congr 1
    funext k
    fin_cases k <;> rfl
  have hLw : L w = 0 := by
    rw [hL]
    exact b.det.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have hLd : L d = 0 := by
    rw [hL]
    exact b.det.map_eq_zero_of_eq _ (i := 0) (j := 2) rfl (by decide)
  have hLπ {u v : P} (h : π u = π v) : L (u -ᵥ v) = 0 := by
    obtain ⟨t, ht⟩ := projAlong_eq_projAlong_iff.1 h
    rw [← ht, map_smul, hLd, smul_zero]
  set xx := lineMap (poly i) (poly (finRotate n i)) r with hxxdef
  set x' := poly.edgePath ℝ j s₀ with hx'def
  set y' := poly.edgePath ℝ j s₁ with hy'def
  have hy'j : y' ∈ poly.edgeSet ℝ j := hpj hs₁I
  have hLyx {y : P} (hy : π y = π y') : L (y -ᵥ xx) = 0 := by
    have hy'x' : L (y' -ᵥ x') = 0 := by
      rw [hy'def, hx'def, edgePath, lineMap_apply, lineMap_apply, vadd_vsub_vadd_cancel_right,
        ← sub_smul, map_smul, hLw, smul_zero]
    rw [← vsub_add_vsub_cancel y y' xx, ← vsub_add_vsub_cancel y' x' xx, map_add, map_add,
      hLπ hy, hy'x', hLπ (u := x') (v := xx) hπx.symm, add_zero, add_zero]
  -- The point `y` of the new edges over `y'`, with its time and the sign of its crossing.
  obtain ⟨y, τy, hyD, hynew, hπy, hτy, hbpy, hdiry⟩ : ∃ y τy, y ∈ D ∧
      y ∈ affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i)) ∧
      π y = π y' ∧ τy ∈ Ioo ((i : ℕ) : ℝ) ((i : ℕ) + 2) ∧ q.boundaryParam τy = y ∧
      SignType.sign (L (q (finRotate (n + 1) (edgeIndexAt (n + 1) τy)) -ᵥ
        q (edgeIndexAt (n + 1) τy))) = SignType.sign (L (poly (finRotate n i) -ᵥ poly i)) := by
    rcases hside with ⟨h1, h0⟩ | ⟨h0, h1⟩
    · -- `y'` lies over the side `AC`.
      set ρ := f 2 s₁
      have hρ : ρ ∈ Ioo (0 : ℝ) 1 := ⟨hpos₂, by linarith [hsum s₁]⟩
      have hπy : π (lineMap (poly i) c ρ) = π y' := by
        rw [π.apply_lineMap]
        refine β.ext_elem fun k ↦ ?_
        rw [hβ0, hβ2, hcl, ← hf]
        fin_cases k <;> simp [lineMap_apply_ring', ρ] <;> linarith [hsum s₁]
      have hτ : edgeIndexAt (n + 1) (((i.castSucc : Fin (n + 1)) : ℕ) + ρ) = i.castSucc :=
        edgeIndexAt_natCast_add _ ⟨hρ.1.le, hρ.2⟩
      refine ⟨lineMap (poly i) c ρ, ((i.castSucc : Fin (n + 1)) : ℕ) + ρ,
        hΔ.affineSegment_left_subset_closedInterior ⟨ρ, ⟨hρ.1.le, hρ.2.le⟩, rfl⟩,
        .inl ⟨ρ, ⟨hρ.1.le, hρ.2.le⟩, rfl⟩, hπy, ?_, ?_, ?_⟩
      · rw [Fin.val_castSucc]
        exact ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
      · rw [boundaryParam_natCast_add _ _ ⟨hρ.1.le, hρ.2.le⟩, edgePath_insertVertex_castSucc_self]
      · rw [hτ, Fin.finRotate_castSucc, insertVertex_apply_succ_self,
          insertVertex_apply_castSucc_self]
        -- `ρ L (c - a) = r L (a' - a)`, since `L` vanishes on `y - x`.
        have h : ρ * L (c -ᵥ poly i) = r * L (poly (finRotate n i) -ᵥ poly i) := by
          have h := hLyx hπy
          simp only [hxxdef, lineMap_vsub_lineMap_eq_vsub_add_smul_sub_smul, vsub_self,
            map_add, map_sub, map_smul, map_zero, smul_eq_mul] at h
          linear_combination h
        rw [← hsignmul hρ.1, h, hsignmul hr.1]
    · -- `y'` lies over the side `CB`.
      set t := f 1 s₁
      have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨h1, by linarith [hsum s₁]⟩
      have hπy : π (lineMap c (poly (finRotate n i)) t) = π y' := by
        rw [π.apply_lineMap]
        refine β.ext_elem fun k ↦ ?_
        rw [hβ1, hβ2, hcl, ← hf]
        fin_cases k <;> simp [lineMap_apply_ring', t] <;> linarith [hsum s₁]
      have hτ : edgeIndexAt (n + 1) (((i.succ : Fin (n + 1)) : ℕ) + t) = i.succ :=
        edgeIndexAt_natCast_add _ ⟨ht.1.le, ht.2⟩
      refine ⟨lineMap c (poly (finRotate n i)) t, ((i.succ : Fin (n + 1)) : ℕ) + t,
        hΔ.affineSegment_right_subset_closedInterior ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩,
        .inr ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, hπy, ?_, ?_, ?_⟩
      · rw [Fin.val_succ, Nat.cast_add_one]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      · rw [boundaryParam_natCast_add _ _ ⟨ht.1.le, ht.2.le⟩, edgePath_insertVertex_succ_self]
      · rw [hτ, insertVertex_apply_finRotate_succ_self, insertVertex_apply_succ_self]
        -- `(1 - t) L (a' - c) = (1 - r) L (a' - a)`, since `L` vanishes on `y - x`.
        have h : (1 - t) * L (poly (finRotate n i) -ᵥ c) =
            (1 - r) * L (poly (finRotate n i) -ᵥ poly i) := by
          have h := hLyx hπy
          have hca := congrArg L (vsub_sub_vsub_cancel_left c (poly i) (poly (finRotate n i)))
          simp only [hxxdef, lineMap_vsub_lineMap_eq_vsub_add_smul_sub_smul, map_add, map_sub,
            map_smul, smul_eq_mul] at h hca
          linear_combination -h - hca
        rw [← hsignmul (sub_pos.2 ht.2), h, hsignmul (sub_pos.2 hr.2)]
  /- The double points: `xx`, on edge `i`, and its partner `x'` cross before the move, `y`, on the
  new edges, and its partner `y'` cross after it, and no other crossing changes. -/
  have hxi : xx ∈ poly.edgeSet ℝ i := ⟨r, Ioo_subset_Icc_self hr, rfl⟩
  have hx'j : x' ∈ poly.edgeSet ℝ j := hpj (Ioo_subset_Icc_self hs₀)
  have hxx'' : xx ≠ x' := hxx'
  have hπx'' : π xx = π x' := hπx
  -- A point of the polygon with the same projection as a vertex is that vertex.
  have hvert {z w₀ : P} (hz : z ∈ poly.boundary ℝ) (hw₀ : w₀ = poly i ∨ w₀ = poly (finRotate n i))
      (h : π w₀ = π z) : z = w₀ := by
    rcases hw₀ with rfl | rfl
    exacts [hπ.eq_vertex_of_apply_eq _ hz h.symm, hπ.eq_vertex_of_apply_eq _ hz h.symm]
  have hDPi {z : P} (hz : z ∈ poly.edgeSet ℝ i) (hzDP : z ∈ poly.doublePoints ℝ π) : z = xx := by
    obtain ⟨-, w₀, hw₀, hne, hπeq⟩ := mem_doublePoints.1 hzDP
    obtain ⟨k, hk⟩ := mem_iUnion.1 hw₀
    by_cases hki : k = i
    · subst hki
      exact (hne (hπ.injOn_edgeSet k hk hz hπeq)).elim
    by_cases hkj : k = j
    · subst hkj
      exact (hsubx hz hk hπeq.symm).1
    exact (hne (hvert (hbdi hz) (hprism k hki hkj w₀ hk
      (hπeq ▸ ⟨z, hΔ.edgeSet_subset_closedInterior hz, rfl⟩)) hπeq).symm).elim
  have hIcc {s : ℝ} (hsu : s ∈ uIcc s₀ s₁) : s ∈ Icc (0 : ℝ) 1 :=
    uIcc_subset_Icc (Ioo_subset_Icc_self hs₀) hs₁I hsu
  have hDPj {s : ℝ} (hsu : s ∈ uIcc s₀ s₁) (hzDP : poly.edgePath ℝ j s ∈ poly.doublePoints ℝ π) :
      s = s₀ := by
    obtain ⟨-, w₀, hw₀, hne, hπeq⟩ := mem_doublePoints.1 hzDP
    obtain ⟨k, hk⟩ := mem_iUnion.1 hw₀
    have hT' : π (poly.edgePath ℝ j s) ∈ π '' D :=
      (hmemT _).2 fun k ↦ by fin_cases k <;> simp only [← hf] <;> simp [hin s hsu]
    by_cases hki : k = i
    · subst hki
      have h := (hsubx hk (hpj (hIcc hsu)) hπeq).2
      exact lineMap_injective ℝ (hs.hasNondegenerateEdges j) h
    by_cases hkj : k = j
    · subst hkj
      exact (hne (hπ.injOn_edgeSet k hk (hpj (hIcc hsu)) hπeq)).elim
    exact (hne (hvert (hbdj (hpj (hIcc hsu))) (hprism k hki hkj w₀ hk (hπeq ▸ hT')) hπeq).symm).elim
  -- Points of the new edges project into the sides `AC` and `CB`.
  set N := affineSegment ℝ (poly i) c ∪ affineSegment ℝ c (poly (finRotate n i))
  have hND : N ⊆ D := union_subset hΔ.affineSegment_left_subset_closedInterior
    hΔ.affineSegment_right_subset_closedInterior
  have hNq : N ⊆ q.boundary ℝ := by rw [boundary_insertVertex]; exact subset_union_right
  have hNc {z : P} (hz : z ∈ N) : (β.coord 1 (π z) = 0 ∧ 0 ≤ β.coord 0 (π z) ∨
      β.coord 0 (π z) = 0 ∧ 0 ≤ β.coord 1 (π z)) ∧ 0 ≤ β.coord 2 (π z) := by
    rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [π.apply_lineMap, hβ0, hβ2, hcl, hcl, hcl]
      simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, lineMap_apply_ring']
      exact ⟨.inl ⟨by ring, by linarith [ht.2]⟩, by linarith [ht.1]⟩
    · rw [π.apply_lineMap, hβ1, hβ2,
        hcl, hcl, hcl]
      simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, lineMap_apply_ring']
      exact ⟨.inr ⟨by ring, by linarith [ht.1]⟩, by linarith [ht.2]⟩
  -- A point of the new edges with the same projection as a point of edge `j` is `y`, over `y'`.
  have hNj {z : P} (hz : z ∈ N) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
      (h : π z = π (poly.edgePath ℝ j s)) : s = s₁ ∧ z = y := by
    have hs₁' : s = s₁ := by
      refine huniq s hs ?_ ?_ <;> simp only [hf, ← h]
      exacts [(hNc hz).2, (hNc hz).1]
    subst hs₁'
    exact ⟨rfl, hinjD (hND hz) hyD (h.trans hπy.symm)⟩
  have hqbd {z : P} (hz : z ∈ q.boundary ℝ) : z ∈ N ∨ ∃ k, k ≠ i ∧ z ∈ poly.edgeSet ℝ k := by
    rw [boundary_insertVertex] at hz
    rcases hz with hz | hz
    · obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 hz
      exact .inr ⟨k, hk, hzk⟩
    · exact .inl hz
  have hbq {z : P} {k : Fin n} (hk : k ≠ i) (hz : z ∈ poly.edgeSet ℝ k) : z ∈ q.boundary ℝ := by
    rw [boundary_insertVertex]
    exact .inl (mem_iUnion₂.2 ⟨k, hk, hz⟩)
  have hNpartner {z w₀ : P} (hz : z ∈ N) (hw₀ : w₀ ∈ q.boundary ℝ) (hne : w₀ ≠ z)
      (h : π w₀ = π z) : z = y ∧ w₀ = y' := by
    rcases hqbd hw₀ with hw₀N | ⟨k, hki, hk⟩
    · exact (hne (hinjD (hND hw₀N) (hND hz) h)).elim
    by_cases hkj : k = j
    · subst hkj
      obtain ⟨s, hs, rfl⟩ := hk
      obtain ⟨rfl, rfl⟩ := hNj hz hs h.symm
      exact ⟨rfl, rfl⟩
    rcases hprism k hki hkj w₀ hk (h ▸ ⟨z, hND hz, rfl⟩) with rfl | rfl
    · have := hπ'.eq_vertex_of_apply_eq i.castSucc (hNq hz)
      rw [insertVertex_apply_castSucc_self] at this
      exact (hne (this h.symm).symm).elim
    · have := hπ'.eq_vertex_of_apply_eq (finRotate (n + 1) i.succ) (hNq hz)
      rw [insertVertex_apply_finRotate_succ_self] at this
      exact (hne (this h.symm).symm).elim
  -- Facts about the new crossing.
  have hyy' : y ≠ y' := fun h ↦ by
    rcases hΔ.edgeSet_inter_closedInterior_subset hji ⟨hy'j, h ▸ hyD⟩ with h' | h'
    · exact ha_j (h' ▸ hy'j)
    · exact ha'_j (h' ▸ hy'j)
  have hcoord₂ {z : P} (hz : z ∈ poly.edgeSet ℝ i) : β.coord 2 (π z) = 0 := by
    obtain ⟨t, -, rfl⟩ := hz
    rw [π.apply_lineMap, hβ0,
      hβ1, hcl]
    simp
  have hyb : y ∉ poly.boundary ℝ := fun h ↦ by
    have hyi : y ∈ poly.edgeSet ℝ i := hΔ.closedInterior_inter_boundary ▸ ⟨hyD, h⟩
    have := hcoord₂ hyi
    rw [hπy, ← hf] at this
    exact hpos₂.ne' this
  have hy'DP : y' ∉ poly.doublePoints ℝ π := fun h ↦
    hs₁₀ (hDPj (s := s₁) right_mem_uIcc h)
  have hyDPq : y ∈ q.doublePoints ℝ π :=
    mem_doublePoints.2 ⟨hNq hynew, y', hjq hy'j, hyy'.symm, hπy.symm⟩
  have hy'DPq : y' ∈ q.doublePoints ℝ π :=
    mem_doublePoints.2 ⟨hjq hy'j, y, hNq hynew, hyy', hπy⟩
  have hxxq : xx ∉ q.boundary ℝ := fun h ↦ by
    rcases hqbd h with hN | ⟨k, hki, hk⟩
    · have h1 := hNc hN
      rw [hπx'', ← hf, ← hf, hf₀, hf₁] at h1
      rcases h1.1 with h | h
      · exact hr.1.ne' h.1
      · linarith [hr.2, h.1]
    · rcases hs.eq_vertex_of_mem_edgeSet (Ne.symm hki) hxi hk with ⟨-, h'⟩ | ⟨-, h'⟩
      · exact hπ.apply_notMem_doublePoints _ (h' ▸ hxDP)
      · exact hπ.apply_notMem_doublePoints _ (h' ▸ hxDP)
  have hpartx {w₀ : P} (hw₀ : w₀ ∈ poly.boundary ℝ) (h : π w₀ = π xx) : w₀ = xx ∨ w₀ = x' := by
    by_cases hw : w₀ = xx
    · exact .inl hw
    · exact .inr ((hπ.eq_doublePointPartner (hbdi hxi) hw₀ hw h).trans
        (hπ.eq_doublePointPartner (hbdi hxi) (hbdj hx'j) hxx''.symm hπx''.symm).symm)
  -- The correspondence of crossings: `xx ↦ y`, `x' ↦ y'`, and every other double point is kept.
  classical
  set g : P → P := fun z ↦ if z = xx then y else if z = x' then y' else z with hgdef
  have hgx : g xx = y := by rw [hgdef]; simp
  have hgx' : g x' = y' := by rw [hgdef]; simp [hxx''.symm]
  have hgo {z : P} (h₁ : z ≠ xx) (h₂ : z ≠ x') : g z = z := by rw [hgdef]; simp [h₁, h₂]
  have hgDP {z : P} (hz : z ∈ poly.doublePoints ℝ π) : g z ∈ q.doublePoints ℝ π := by
    by_cases h₁ : z = xx
    · rwa [h₁, hgx]
    by_cases h₂ : z = x'
    · rwa [h₂, hgx']
    rw [hgo h₁ h₂]
    obtain ⟨hzb, w₀, hw₀, hne, hπeq⟩ := mem_doublePoints.1 hz
    -- Neither `z` nor its partner `w₀` lies on edge `i`, so both lie on the new polygon.
    have hoff {u : P} (hu : u ∈ poly.boundary ℝ) (hui : u ∉ poly.edgeSet ℝ i) :
        u ∈ q.boundary ℝ := by
      obtain ⟨k, hk⟩ := mem_iUnion.1 hu
      exact hbq (fun h ↦ hui (h ▸ hk)) hk
    have hzi : z ∉ poly.edgeSet ℝ i := fun h ↦
      h₁ (hDPi h (mem_doublePoints.2 ⟨hzb, w₀, hw₀, hne, hπeq⟩))
    have hw₀i : w₀ ∉ poly.edgeSet ℝ i := fun h ↦ by
      have := hDPi h (mem_doublePoints.2 ⟨hw₀, z, hzb, hne.symm, hπeq.symm⟩)
      subst this
      rcases hpartx hzb hπeq.symm with h' | h'
      exacts [h₁ h', h₂ h']
    exact mem_doublePoints.2 ⟨hoff hzb hzi, w₀, hoff hw₀ hw₀i, hne, hπeq⟩
  have hDPq {z : P} (hz : z ∈ q.doublePoints ℝ π) :
      ∃ z₀ ∈ poly.doublePoints ℝ π, g z₀ = z := by
    obtain ⟨hzb, w₀, hw₀, hne, hπeq⟩ := mem_doublePoints.1 hz
    by_cases hzN : z ∈ N
    · obtain ⟨rfl, -⟩ := hNpartner hzN hw₀ hne hπeq
      exact ⟨xx, hxDP, hgx⟩
    by_cases hw₀N : w₀ ∈ N
    · obtain ⟨rfl, rfl⟩ := hNpartner hw₀N hzb hne.symm hπeq.symm
      exact ⟨x', hx'DP, hgx'⟩
    -- Both points lie on edges of `poly` other than edge `i`.
    have hpoly {u : P} (hu : u ∈ q.boundary ℝ) (huN : u ∉ N) : u ∈ poly.boundary ℝ := by
      rcases hqbd hu with h | ⟨k, -, hk⟩
      exacts [(huN h).elim, mem_iUnion.2 ⟨k, hk⟩]
    have hzDP : z ∈ poly.doublePoints ℝ π :=
      mem_doublePoints.2 ⟨hpoly hzb hzN, w₀, hpoly hw₀ hw₀N, hne, hπeq⟩
    refine ⟨z, hzDP, hgo (fun h ↦ hxxq (h ▸ hzb)) fun h ↦ ?_⟩
    -- If `z = x'`, then `xx`, `x'` and `w₀` would be three points over the same crossing.
    subst h
    rcases hπ.eq_or_eq_or_eq_of_apply_eq (hbdi hxi) (hbdj hx'j) (hpoly hw₀ hw₀N) hπx''
      (hπx''.trans hπeq.symm) with h | h | h
    · exact hxx'' h
    · exact hxxq (h ▸ hw₀)
    · exact hne h.symm
  -- The change of time: off edges `i` and `j` the traversals differ as for any inserted vertex.
  obtain ⟨ψ, hψ, hψt, hψle, hψge⟩ := exists_strictMono_boundaryParam_insertVertex poly i c
  set τx : ℝ := ((i : ℕ) : ℝ) + r with hτxdef
  set τx' : ℝ := ((j : ℕ) : ℝ) + s₀ with hτx'def
  have hin1 {k : Fin n} {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) : ((k : ℕ) : ℝ) + u ∈ Ico (0 : ℝ) n := by
    have hk : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast k.isLt
    exact ⟨add_nonneg (Nat.cast_nonneg _) hu.1, by linarith [hu.2]⟩
  have hbpτx : poly.boundaryParam τx = xx := by
    rw [hτxdef, boundaryParam_natCast_add _ _ (Ioo_subset_Icc_self hr)]
    rfl
  have hbpτx' : poly.boundaryParam τx' = x' := by
    rw [hτx'def, boundaryParam_natCast_add _ _ (Ioo_subset_Icc_self hs₀)]
  have hτxCT : τx ∈ poly.crossingTimes p₀ d :=
    mem_crossingTimes.2 ⟨hin1 ⟨hr.1.le, hr.2⟩, by rw [hbpτx]; exact hxDP⟩
  have hτx'CT : τx' ∈ poly.crossingTimes p₀ d :=
    mem_crossingTimes.2 ⟨hin1 ⟨hs₀.1.le, hs₀.2⟩, by rw [hbpτx']; exact hx'DP⟩
  have hbpinj {t t' : ℝ} (ht : t ∈ poly.crossingTimes p₀ d) (ht' : t' ∈ poly.crossingTimes p₀ d)
      (h : poly.boundaryParam t = poly.boundaryParam t') : t = t' :=
    hs.injOn_boundaryParam (crossingTimes_subset_Ico ht) (crossingTimes_subset_Ico ht') h
  have hτxx' : τx ≠ τx' := fun h ↦ hxx'' (by rw [← hbpτx, ← hbpτx', h])
  have hidx {k : Fin n} {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) : edgeIndexAt n (((k : ℕ) : ℝ) + u) = k :=
    edgeIndexAt_natCast_add _ hu
  -- The only crossing time on edge `i` is `τx`.
  have hCTi {t : ℝ} (ht : t ∈ poly.crossingTimes p₀ d) (hti : edgeIndexAt n t = i) : t = τx := by
    refine hbpinj ht hτxCT ?_
    rw [hbpτx]
    refine hDPi ?_ (mem_crossingTimes.1 ht).2
    rw [boundaryParam_eq_edgePath_edgeIndexAt, hti]
    exact ⟨_, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, rfl⟩
  have hCTside {t : ℝ} (ht : t ∈ poly.crossingTimes p₀ d) (htx : t ≠ τx) :
      t < (i : ℕ) ∨ ((i : ℕ) : ℝ) + 1 ≤ t := by
    by_contra! h
    refine htx (hCTi ht ?_)
    have := hidx (k := i) (u := t - (i : ℕ)) ⟨by linarith [h.1], by linarith [h.2]⟩
    rwa [add_sub_cancel] at this
  -- No crossing time of `poly` lies on edge `j` between the parameters `s₀` and `s₁`.
  have hgap {t : ℝ} (ht : t ∈ poly.crossingTimes p₀ d)
      (htu : t ∈ uIcc (((j : ℕ) : ℝ) + s₀) (((j : ℕ) : ℝ) + s₁)) : t = τx' := by
    have hsu : t - (j : ℕ) ∈ uIcc s₀ s₁ := by
      rw [mem_uIcc] at htu ⊢
      rcases htu with h | h
      exacts [.inl ⟨by linarith [h.1], by linarith [h.2]⟩,
        .inr ⟨by linarith [h.1], by linarith [h.2]⟩]
    have hbp : poly.boundaryParam t = poly.edgePath ℝ j (t - (j : ℕ)) := by
      conv_lhs => rw [← add_sub_cancel ((j : ℕ) : ℝ) t]
      exact boundaryParam_natCast_add _ _ (hIcc hsu)
    have := hDPj hsu (hbp ▸ (mem_crossingTimes.1 ht).2)
    rw [hτx'def, ← this, add_sub_cancel]
  -- Move the crossing time `τx'` to the time `j + s₁` of `y'`; then apply `ψ`, except at `τx`.
  set θ : ℝ → ℝ := update id τx' (((j : ℕ) : ℝ) + s₁)
  have hθx' : θ τx' = ((j : ℕ) : ℝ) + s₁ := update_self ..
  have hθo {t : ℝ} (h : t ≠ τx') : θ t = t := update_of_ne h ..
  set φ : ℝ → ℝ := update (ψ ∘ θ) τx τy
  have hφx : φ τx = τy := update_self ..
  have hφo {t : ℝ} (h : t ≠ τx) : φ t = ψ (θ t) := update_of_ne h ..
  have hji' : (j : ℕ) ≠ (i : ℕ) := fun h ↦ hji (Fin.ext h)
  have hθside {t : ℝ} (ht : t ∈ poly.crossingTimes p₀ d) (htx : t ≠ τx) :
      (θ t < (i : ℕ) ∧ t < (i : ℕ)) ∨ (((i : ℕ) : ℝ) + 1 ≤ θ t ∧ ((i : ℕ) : ℝ) + 1 ≤ t) := by
    by_cases htx' : t = τx'
    · subst htx'
      rw [hθx']
      rcases lt_or_gt_of_ne hji' with h | h
      · have : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast h
        exact .inl ⟨by linarith [hs₁.2], by linarith [hs₀.2]⟩
      · have : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast h
        exact .inr ⟨by linarith [hs₁.1], by linarith [hs₀.1]⟩
    · rw [hθo htx']
      rcases hCTside ht htx with h | h
      exacts [.inl ⟨h, h⟩, .inr ⟨h, h⟩]
  -- No crossing time lies between `τx'` and its new position; none but `τx` lies on edge `i`.
  have hθmono : StrictMonoOn θ (poly.crossingTimes p₀ d) :=
    (strictMono_id.strictMonoOn _).update
      (fun t ht htlt ↦ by
        by_contra! hle
        exact htlt.ne (hgap ht (mem_uIcc.2 (.inr ⟨hle, htlt.le⟩))))
      (fun t ht htgt ↦ by
        by_contra! hle
        exact htgt.ne' (hgap ht (mem_uIcc.2 (.inl ⟨htgt.le, hle⟩))))
  have hφmono : StrictMonoOn φ (poly.crossingTimes p₀ d) :=
    ((hψ.comp_strictMonoOn hθmono).mono sdiff_subset).update
      (fun t ht htlt ↦ by
        rcases hθside ht htlt.ne with h | h
        · rw [Function.comp_apply, hψle _ h.1.le]
          linarith [hτy.1, h.1]
        · linarith [h.2, hr.2])
      (fun t ht htgt ↦ by
        rcases hθside ht htgt.ne' with h | h
        · linarith [h.2, hr.1]
        · rw [Function.comp_apply, hψge _ h.1]
          linarith [hτy.2, h.1])
  -- At every crossing time other than `τx`, the shifted time runs along an edge other than `i`.
  have hθgood {t : ℝ} (ht : t ∈ poly.crossingTimes p₀ d) (htx : t ≠ τx) :
      θ t ∈ Ico (0 : ℝ) n ∧ edgeIndexAt n (θ t) ≠ i ∧
        poly.boundaryParam (θ t) = g (poly.boundaryParam t) ∧
        edgeIndexAt n (θ t) = edgeIndexAt n t := by
    by_cases htx' : t = τx'
    · subst htx'
      rw [hθx', hidx ⟨hs₁.1.le, hs₁.2⟩, hτx'def, hidx ⟨hs₀.1.le, hs₀.2⟩,
        boundaryParam_natCast_add _ _ hs₁I, ← hτx'def, hbpτx', hgx']
      exact ⟨hin1 ⟨hs₁.1.le, hs₁.2⟩, hji, rfl, rfl⟩
    · rw [hθo htx']
      refine ⟨crossingTimes_subset_Ico ht, fun h ↦ htx (hCTi ht h), (hgo
        (fun h ↦ htx (hbpinj ht hτxCT (h.trans hbpτx.symm)))
        fun h ↦ htx' (hbpinj ht hτx'CT (h.trans hbpτx'.symm))).symm, rfl⟩
  have hbp (t : ℝ) (ht : t ∈ poly.crossingTimes p₀ d) :
      q.boundaryParam (φ t) = g (poly.boundaryParam t) := by
    by_cases htx : t = τx
    · rw [htx, hφx, hbpy, hbpτx, hgx]
    · obtain ⟨h₁, h₂, h₃, -⟩ := hθgood ht htx
      rw [hφo htx, (hψt _ h₁ h₂).2.1, h₃]
  have hφmem (t : ℝ) (ht : t ∈ poly.crossingTimes p₀ d) : φ t ∈ Ico (0 : ℝ) (n + 1 : ℕ) := by
    by_cases htx : t = τx
    · rw [htx, hφx]
      have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
      push_cast
      have hi0 : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
      exact ⟨by linarith [hi0, hτy.1], by linarith [hτy.2]⟩
    · obtain ⟨h₁, h₂, -⟩ := hθgood ht htx
      rw [hφo htx]
      exact (hψt _ h₁ h₂).1
  have hct : q.crossingTimes p₀ d = φ '' poly.crossingTimes p₀ d := by
    ext t'
    constructor
    · intro ht'
      obtain ⟨ht'I, ht'DP⟩ := mem_crossingTimes.1 ht'
      obtain ⟨z₀, hz₀, hgz⟩ := hDPq ht'DP
      rw [← image_boundaryParam_crossingTimes] at hz₀
      obtain ⟨t, ht, rfl⟩ := hz₀
      exact ⟨t, ht, hs'.injOn_boundaryParam (hφmem t ht) ht'I (by rw [hbp t ht, hgz])⟩
    · rintro ⟨t, ht, rfl⟩
      exact mem_crossingTimes.2
        ⟨hφmem t ht, by rw [hbp t ht]; exact hgDP (mem_crossingTimes.1 ht).2⟩
  -- `g` is injective on the double points: `y` and `y'` are not double points of `poly`.
  have hyDP : y ∉ poly.doublePoints ℝ π := fun h ↦ hyb (doublePoints_subset_boundary h)
  have hgcases (z : P) :
      (z = xx ∧ g z = y) ∨ (z = x' ∧ g z = y') ∨ (z ≠ xx ∧ z ≠ x' ∧ g z = z) := by
    by_cases h₁ : z = xx
    · exact .inl ⟨h₁, h₁ ▸ hgx⟩
    by_cases h₂ : z = x'
    · exact .inr (.inl ⟨h₂, h₂ ▸ hgx'⟩)
    exact .inr (.inr ⟨h₁, h₂, hgo h₁ h₂⟩)
  have hgy {z : P} (hz : z ∈ poly.doublePoints ℝ π) (h : g z = y) : z = xx := by
    rcases hgcases z with ⟨h₁, -⟩ | ⟨-, e⟩ | ⟨-, -, e⟩
    exacts [h₁, (hyy' (h.symm.trans e)).elim, (hyDP ((e.symm.trans h) ▸ hz)).elim]
  have hgy' {z : P} (hz : z ∈ poly.doublePoints ℝ π) (h : g z = y') : z = x' := by
    rcases hgcases z with ⟨-, e⟩ | ⟨h₁, -⟩ | ⟨-, -, e⟩
    exacts [(hyy' (e.symm.trans h)).elim, h₁, (hy'DP ((e.symm.trans h) ▸ hz)).elim]
  have hginj : InjOn g (poly.doublePoints ℝ π) := by
    intro z₁ hz₁ z₂ hz₂ h
    rcases hgcases z₁ with ⟨h₁, e₁⟩ | ⟨h₁, e₁⟩ | ⟨-, -, e₁⟩
    · rw [h₁, hgy hz₂ (h.symm.trans e₁)]
    · rw [h₁, hgy' hz₂ (h.symm.trans e₁)]
    · rw [e₁] at h
      rcases hgcases z₂ with ⟨-, e₂⟩ | ⟨-, e₂⟩ | ⟨-, -, e₂⟩
      · exact (hyDP ((h.trans e₂) ▸ hz₁)).elim
      · exact (hy'DP ((h.trans e₂) ▸ hz₁)).elim
      · exact h.trans e₂
  -- The double points over the moved crossing are `xx` and `x'`.
  have hpair {z : P} (hz : z ∈ poly.doublePoints ℝ π) (h : π z = π xx) : z = xx ∨ z = x' :=
    hpartx (doublePoints_subset_boundary hz) h
  have hgπ {z : P} (hz : z = xx ∨ z = x') : π (g z) = π y := by
    rcases hz with rfl | rfl
    · rw [hgx]
    · rw [hgx', hπy]
  have hgoff {z : P} (_ : z ∈ poly.doublePoints ℝ π) (h : π z ≠ π xx) : g z = z :=
    hgo (fun h' ↦ h (h' ▸ rfl)) fun h' ↦ h (h' ▸ hπx''.symm)
  have hfib : ∀ z ∈ poly.doublePoints ℝ π, ∀ w₀ ∈ poly.doublePoints ℝ π,
      π z = π w₀ → π (g z) = π (g w₀) := by
    intro z hz w₀ hw₀ h
    by_cases hzx : π z = π xx
    · rw [hgπ (hpair hz hzx), hgπ (hpair hw₀ (h ▸ hzx))]
    · rw [hgoff hz hzx, hgoff hw₀ (h ▸ hzx), h]
  -- Over/under is kept: `xx` and `y` lie in the triangle, `x'` and `y'` on edge `j`, disjoint
  -- from it.
  have hdisj : ∀ z ∈ D, z ∉ affineSegment ℝ (poly j) (poly (finRotate n j)) := fun z hz hzj ↦ by
    rcases hΔ.edgeSet_inter_closedInterior_subset hji ⟨hzj, hz⟩ with rfl | rfl
    exacts [ha_j hzj, ha'_j hzj]
  obtain ⟨h₁, hh₁⟩ := projAlong_eq_projAlong_iff.1 hπy
  have hheight {h₀ : ℝ} (hh₀ : h₀ • d = xx -ᵥ x') : 0 < h₀ ↔ 0 < h₁ :=
    hΔ.triangle.pos_iff_pos_of_disjoint hdisj (hΔ.edgeSet_subset_closedInterior hxi) hyD hx'j hy'j
      hh₀ hh₁
  have hh₁0 : h₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul, eq_comm, vsub_eq_zero_iff_eq] at hh₁
    exact hyy' hh₁
  have hover : ∀ z ∈ poly.doublePoints ℝ π, ∀ w₀ ∈ poly.doublePoints ℝ π,
      (∃ c : ℝ, 0 < c ∧ c • d = z -ᵥ w₀) → ∃ c : ℝ, 0 < c ∧ c • d = g z -ᵥ g w₀ := by
    rintro z hz w₀ hw₀ ⟨e, he, hed⟩
    have hπzw : π z = π w₀ := projAlong_eq_projAlong_iff.2 ⟨e, hed⟩
    by_cases hzx : π z = π xx
    · have hzw : z ≠ w₀ := by
        rintro rfl
        rw [vsub_self, smul_eq_zero] at hed
        exact hed.elim he.ne' hd
      rcases hpair hz hzx with rfl | rfl <;> rcases hpair hw₀ (hπzw ▸ hzx) with rfl | rfl
      · exact (hzw rfl).elim
      · exact ⟨h₁, (hheight hed).1 he, by rw [hgx, hgx', hh₁]⟩
      · refine ⟨-h₁, ?_, by rw [hgx, hgx', neg_smul, hh₁, neg_vsub_eq_vsub_rev]⟩
        have : ¬ 0 < h₁ := fun h ↦ by
          have := (hheight (by rw [neg_smul, hed, neg_vsub_eq_vsub_rev] : (-e) • d = _)).2 h
          linarith
        exact neg_pos.2 (lt_of_le_of_ne (not_lt.1 this) hh₁0)
      · exact (hzw rfl).elim
    · exact ⟨e, he, by rw [hgoff hz hzx, hgoff hw₀ (hπzw ▸ hzx), hed]⟩
  -- The signs are kept: at the moved crossing by the choice of `y`, elsewhere since the edges
  -- are the same.
  have hpx : poly.doublePointPartner ℝ π xx = x' :=
    (hπ.eq_doublePointPartner (hbdi hxi) (hbdj hx'j) hxx''.symm hπx''.symm).symm
  have hpx' : poly.doublePointPartner ℝ π x' = xx := by
    rw [← hpx, hπ.involutive_doublePointPartner]
  have hdirτy' : q (finRotate (n + 1) (edgeIndexAt (n + 1) (φ τx'))) -ᵥ
      q (edgeIndexAt (n + 1) (φ τx')) = w := by
    obtain ⟨h₁, h₂, -, h₄⟩ := hθgood hτx'CT hτxx'.symm
    rw [hφo hτxx'.symm, (hψt _ h₁ h₂).2.2, h₄, hτx'def, hidx ⟨hs₀.1.le, hs₀.2⟩]
  have hdirτx : poly (finRotate n (edgeIndexAt n τx)) -ᵥ poly (edgeIndexAt n τx) =
      poly (finRotate n i) -ᵥ poly i := by
    rw [hτxdef, hidx ⟨hr.1.le, hr.2⟩]
  have hdirτx' : poly (finRotate n (edgeIndexAt n τx')) -ᵥ poly (edgeIndexAt n τx') = w := by
    rw [hτx'def, hidx ⟨hs₀.1.le, hs₀.2⟩]
  have hswap (u : V) : b.det ![w, u, d] = -b.det ![u, w, d] := by
    have h := b.det.map_swap ![u, w, d] (i := 0) (j := 1) (by decide)
    have he : ![u, w, d] ∘ (Equiv.swap (0 : Fin 3) 1) = ![w, u, d] := by
      funext k
      fin_cases k <;> rfl
    rw [he] at h
    exact h
  have hsign : ∀ t ∈ poly.crossingTimes p₀ d, ∀ t' ∈ poly.crossingTimes p₀ d,
      poly.boundaryParam t' = poly.doublePointPartner ℝ π (poly.boundaryParam t) →
      SignType.sign (b.det
        ![q (finRotate (n + 1) (edgeIndexAt (n + 1) (φ t))) -ᵥ q (edgeIndexAt (n + 1) (φ t)),
          q (finRotate (n + 1) (edgeIndexAt (n + 1) (φ t'))) -ᵥ q (edgeIndexAt (n + 1) (φ t')),
          d]) =
      SignType.sign (b.det
        ![poly (finRotate n (edgeIndexAt n t)) -ᵥ poly (edgeIndexAt n t),
          poly (finRotate n (edgeIndexAt n t')) -ᵥ poly (edgeIndexAt n t'), d]) := by
    intro t ht t' ht' htt'
    by_cases htx : t = τx
    · subst htx
      obtain rfl : t' = τx' := hbpinj ht' hτx'CT (by rw [htt', hbpτx, hpx, hbpτx'])
      rw [hφx, hdirτy', hdirτx, hdirτx', ← hL, ← hL]
      exact hdiry
    by_cases htx' : t = τx'
    · subst htx'
      obtain rfl : t' = τx := hbpinj ht' hτxCT (by rw [htt', hbpτx', hpx', hbpτx])
      rw [hφx, hdirτy', hdirτx, hdirτx', hswap, hswap, ← hL, ← hL, Left.sign_neg, Left.sign_neg,
        hdiry]
    -- Away from the moved crossing, both visits keep their edges.
    have ht'x : t' ≠ τx := fun h ↦ htx' (hbpinj ht hτx'CT (by
      rw [hbpτx', ← hpx, ← hbpτx, ← h, htt', hπ.involutive_doublePointPartner]))
    obtain ⟨a₁, a₂, -, a₄⟩ := hθgood ht htx
    obtain ⟨b₁, b₂, -, b₄⟩ := hθgood ht' ht'x
    rw [hφo htx, hφo ht'x, (hψt _ a₁ a₂).2.2, (hψt _ b₁ b₂).2.2, a₄, b₄]
  exact gaussCode_eq_of_strictMonoOn b hs hπ b hs' hπ' hφmono hct hbp hginj hfib hover hsign

end Polygon
