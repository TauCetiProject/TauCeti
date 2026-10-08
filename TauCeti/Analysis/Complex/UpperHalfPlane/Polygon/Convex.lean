/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.ExtSegment
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.VertexAngle
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Basic
import TauCeti.Data.Fin.Basic

/-!
# Convex hyperbolic polygons with ideal vertices

A convex hyperbolic polygon with `n ≥ 3` vertices is given by its vertices `v₀, …, vₙ₋₁` in
`ℍ ∪ ∂ℍ`, modelled as `ℍ ⊕ OnePoint ℝ`, listed counterclockwise: consecutive vertices are
distinct, and every vertex other than the endpoints of an edge lies strictly to the left of the
geodesic through that edge, in the open half-plane or on the open arc of ideal points on its left
(`ConvexPolygon`). A vertex on `∂ℍ` is an ideal vertex. The side from `vᵢ` to `vᵢ₊₁`
(`ConvexPolygon.side i`) is the closed piece of geodesic between them: a segment if both lie in
`ℍ`, a ray if one of them is ideal, a whole geodesic line if both are. It lies on the full geodesic
line `ConvexPolygon.sideGeodesic i` running from `vᵢ` to `vᵢ₊₁`, the carrier is the intersection of
the closed left half-planes of these lines (`ConvexPolygon.carrier`) and contains every side, and
the interior angle at a vertex is the angle between the two sides there
(`ConvexPolygon.interiorAngle`), which is `0` at an ideal vertex.

A compact convex polygon (`CompactConvexPolygon`, all vertices in `ℍ`) is a convex polygon with the
same sides, carrier and angles (`CompactConvexPolygon.toConvexPolygon`), and every convex polygon
without ideal vertices arises this way (`ConvexPolygon.exists_eq_toConvexPolygon`).

## Main definitions

* `ConvexPolygon n`: a convex hyperbolic polygon with `n` vertices in `ℍ ∪ ∂ℍ`.
* `ConvexPolygon.side`, `ConvexPolygon.sideGeodesic`, `ConvexPolygon.carrier`,
  `ConvexPolygon.interiorAngle`: its sides, the geodesic lines of its sides, its carrier and its
  interior angles.
* `ConvexPolygon.rotate`: the cyclic relabelling of the vertices.
* `CompactConvexPolygon.toConvexPolygon`: a compact convex polygon as a convex polygon.

## Main results

* `ConvexPolygon.vertex_injective`: the vertices are distinct.
* `ConvexPolygon.isClosed_carrier`, `ConvexPolygon.mem_carrier_iff_sideForm_nonpos`: the carrier
  is closed, and is cut out by the side forms of the edges.
* `ConvexPolygon.side_subset_range_sideGeodesic`, `ConvexPolygon.side_subset_carrier`: each side
  lies on its geodesic line and in the carrier.
* `ConvexPolygon.vertex_mem_extClosedLeftHalfPlane_sideGeodesic`: every vertex is weakly to the
  left of the geodesic line of every side.
* `ConvexPolygon.sideForm_sideGeodesic_toComplex_nonpos`,
  `ConvexPolygon.sideForm_sideGeodesic_toComplex_neg`: every vertex other than `∞` lies in the
  closed left half-plane of the geodesic line of every side, strictly when it is not an endpoint
  of that side.
* The `MulAction` of `PSL(2, ℝ)` on convex polygons, with `ConvexPolygon.side_smul`,
  `ConvexPolygon.carrier_smul` and `ConvexPolygon.interiorAngle_smul`; the cyclic relabelling
  `ConvexPolygon.rotate`, with `ConvexPolygon.rotate_zero`, `ConvexPolygon.rotate_rotate`,
  `ConvexPolygon.side_rotate`, `ConvexPolygon.carrier_rotate` and
  `ConvexPolygon.sum_interiorAngle_rotate`.
* `CompactConvexPolygon.side_toConvexPolygon`, `CompactConvexPolygon.carrier_toConvexPolygon`,
  `CompactConvexPolygon.interiorAngle_toConvexPolygon`: the embedding preserves sides, carrier and
  angles.

The counterclockwise orientation is a convention of this file, as for `CompactConvexPolygon`.

## Source

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), §7.1 (polygons with
vertices in `ℍ ∪ ∂ℍ`; their sides `[vᵢ, vᵢ₊₁]`, which are rays or geodesic lines at ideal
vertices; ideal vertices and their zero angle) and §14.2 (a convex hyperbolic polygon
is an intersection of finitely many half-planes).
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint Real

namespace TauCeti.UpperHalfPlane

/-- A convex hyperbolic polygon with `n` vertices `vertex 0, …, vertex (n - 1)` in `ℍ ∪ ∂ℍ`,
listed counterclockwise: consecutive vertices are distinct, and every vertex other than
`vertex i` and `vertex (i + 1)` lies strictly to the left of the geodesic from `vertex i` to
`vertex (i + 1)`. -/
@[ext]
structure ConvexPolygon (n : ℕ) [NeZero n] where
  /-- The vertices, in counterclockwise order; indices are taken cyclically. -/
  vertex : Fin n → ℍ ⊕ OnePoint ℝ
  /-- A polygon has at least three vertices. -/
  three_le : 3 ≤ n
  /-- Consecutive vertices are distinct. -/
  vertex_ne_vertex_add_one : ∀ i, vertex i ≠ vertex (i + 1)
  /-- Every vertex off an edge lies strictly to the left of it. -/
  vertex_mem_extLeftHalfPlane : ∀ i j : Fin n, j ≠ i → j ≠ i + 1 →
    vertex j ∈ extLeftHalfPlane (geodesicFromTo (vertex i) (vertex (i + 1)))

namespace ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n)

/-! ### Sides and vertices -/

/-- The full geodesic line supporting the side of a convex polygon from `vertex i` to
`vertex (i + 1)`, oriented from `vertex i` to `vertex (i + 1)`. -/
def sideGeodesic (i : Fin n) : PSL(2, ℝ) :=
  geodesicFromTo (P.vertex i) (P.vertex (i + 1))

-- The body of `sideGeodesic` is not `@[expose]`d, so downstream modules rewrite with this.
/-- The geodesic line of a side, unfolded. -/
theorem sideGeodesic_def (i : Fin n) :
    P.sideGeodesic i = geodesicFromTo (P.vertex i) (P.vertex (i + 1)) := by
  rfl

/-- The geodesic line of the side from `vertex i` runs from `vertex i` to `vertex (i + 1)`. -/
theorem isGeodesicFromTo_sideGeodesic (i : Fin n) :
    IsGeodesicFromTo (P.sideGeodesic i) (P.vertex i) (P.vertex (i + 1)) :=
  isGeodesicFromTo_geodesicFromTo (P.vertex_ne_vertex_add_one i)

/-- A vertex off an edge lies strictly to the left of it. -/
theorem vertex_mem_extLeftHalfPlane_sideGeodesic {i j : Fin n} (hji : j ≠ i) (hji' : j ≠ i + 1) :
    P.vertex j ∈ extLeftHalfPlane (P.sideGeodesic i) :=
  P.vertex_mem_extLeftHalfPlane i j hji hji'

/-- Every vertex is weakly to the left of the geodesic line of every side: the endpoints of the
side lie on its closure, and the other vertices strictly to its left. -/
theorem vertex_mem_extClosedLeftHalfPlane_sideGeodesic (i j : Fin n) :
    P.vertex j ∈ extClosedLeftHalfPlane (P.sideGeodesic i) := by
  by_cases hji : j = i
  · subst hji
    exact (P.isGeodesicFromTo_sideGeodesic j).left_mem_extClosedLeftHalfPlane
  by_cases hji' : j = i + 1
  · subst hji'
    exact (P.isGeodesicFromTo_sideGeodesic i).right_mem_extClosedLeftHalfPlane
  exact extLeftHalfPlane_subset_extClosedLeftHalfPlane _
    (P.vertex_mem_extLeftHalfPlane_sideGeodesic hji hji')

/-- The vertices of a convex polygon are distinct. -/
theorem vertex_injective : Function.Injective P.vertex := by
  intro i j hij
  by_contra hne
  by_cases hj : j = i + 1
  · rw [hj] at hij
    exact P.vertex_ne_vertex_add_one i hij
  · refine (P.isGeodesicFromTo_sideGeodesic i).left_notMem_extLeftHalfPlane ?_
    rw [hij]
    exact P.vertex_mem_extLeftHalfPlane_sideGeodesic (Ne.symm hne) hj

/-- A vertex differs from the previous one. -/
theorem vertex_ne_vertex_sub_one (i : Fin n) : P.vertex i ≠ P.vertex (i - 1) :=
  P.vertex_injective.ne (sub_one_ne_self (Nat.le_of_succ_le P.three_le) i).symm

/-! ### The carrier -/

/-- The carrier of a convex polygon: the intersection of the closed left half-planes of its
edges. -/
def carrier : Set ℍ :=
  ⋂ i, closure (leftHalfPlane (P.sideGeodesic i))

-- The body of `carrier` is not `@[expose]`d, so downstream modules rewrite with this.
/-- The carrier, unfolded: the intersection of the closed left half-planes of the edges. -/
theorem carrier_def : P.carrier = ⋂ i, closure (leftHalfPlane (P.sideGeodesic i)) := by
  rfl

/-- Membership in the carrier. -/
@[simp]
theorem mem_carrier_iff (z : ℍ) :
    z ∈ P.carrier ↔ ∀ i, z ∈ closure (leftHalfPlane (P.sideGeodesic i)) :=
  Set.mem_iInter

/-- The polygon lies in the closed left half-plane of each side. -/
theorem carrier_subset_closure_leftHalfPlane (i : Fin n) :
    P.carrier ⊆ closure (leftHalfPlane (P.sideGeodesic i)) :=
  fun _ hz ↦ (P.mem_carrier_iff _).mp hz i

/-- The carrier is cut out by the side forms of the edges. -/
theorem mem_carrier_iff_sideForm_nonpos (z : ℍ) :
    z ∈ P.carrier ↔ ∀ i, sideForm (P.sideGeodesic i) z ≤ 0 :=
  (P.mem_carrier_iff z).trans
    (forall_congr' fun i ↦ mem_closure_leftHalfPlane_iff_sideForm_nonpos (P.sideGeodesic i) z)

/-- The carrier is closed. -/
theorem isClosed_carrier : IsClosed P.carrier :=
  isClosed_iInter fun _ ↦ isClosed_closure

/-- The carrier is measurable. -/
theorem measurableSet_carrier : MeasurableSet P.carrier :=
  P.isClosed_carrier.measurableSet

/-- The interior is the intersection of the open left half-planes of the sides. -/
theorem interior_carrier :
    interior P.carrier = ⋂ i, leftHalfPlane (P.sideGeodesic i) := by
  simp_rw [carrier_def, interior_iInter_of_finite, interior_closure_leftHalfPlane]

/-- A point is in the polygon interior exactly when it is strictly left of every side. -/
@[simp]
theorem mem_interior_carrier_iff (z : ℍ) :
    z ∈ interior P.carrier ↔ ∀ i, z ∈ leftHalfPlane (P.sideGeodesic i) := by
  rw [interior_carrier, Set.mem_iInter]

/-- A point is in the polygon interior exactly when every side form is strictly negative. -/
theorem mem_interior_carrier_iff_sideForm_neg (z : ℍ) :
    z ∈ interior P.carrier ↔ ∀ i, sideForm (P.sideGeodesic i) z < 0 := by
  simp_rw [mem_interior_carrier_iff, mem_leftHalfPlane_iff_sideForm_neg]

/-- A vertex other than `∞` and off an edge lies strictly to its left: the side form of the edge is
negative there. -/
theorem sideForm_sideGeodesic_toComplex_neg {i j : Fin n} (hj : P.vertex j ≠ .inr ∞) (hji : j ≠ i)
    (hji' : j ≠ i + 1) : sideForm (P.sideGeodesic i) (toComplex (P.vertex j)) < 0 :=
  sideForm_toComplex_neg_of_mem_extLeftHalfPlane hj
    (P.vertex_mem_extLeftHalfPlane_sideGeodesic hji hji')

/-- Every vertex other than `∞` lies in the closed left half-plane of every edge: the side form of
the edge is nonpositive there. -/
theorem sideForm_sideGeodesic_toComplex_nonpos (i j : Fin n) (hj : P.vertex j ≠ .inr ∞) :
    sideForm (P.sideGeodesic i) (toComplex (P.vertex j)) ≤ 0 :=
  sideForm_toComplex_nonpos_of_mem_extClosedLeftHalfPlane hj
    (P.vertex_mem_extClosedLeftHalfPlane_sideGeodesic i j)

/-- A vertex in `ℍ` lies in the carrier. -/
theorem vertex_mem_carrier {i : Fin n} {z : ℍ} (h : P.vertex i = .inl z) : z ∈ P.carrier := by
  refine (P.mem_carrier_iff_sideForm_nonpos z).2 fun j ↦ ?_
  have hi : P.vertex i ≠ .inr ∞ := by
    rw [h]
    exact Sum.inl_ne_inr
  have hz := P.sideForm_sideGeodesic_toComplex_nonpos j i hi
  rwa [h, toComplex_inl] at hz

/-! ### Sides -/

/-- The side of a convex polygon from `vertex i` to `vertex (i + 1)`: the geodesic segment between
them if both lie in `ℍ`, the geodesic ray from the one in `ℍ` towards the other if exactly one of
them is ideal, and the whole geodesic line `sideGeodesic i` if both are ideal. -/
def side (i : Fin n) : Set ℍ :=
  extGeodesicSegment (P.vertex i) (P.vertex (i + 1))

-- The body of `side` is not `@[expose]`d, so downstream modules rewrite with this.
/-- The side of a convex polygon, unfolded: the geodesic piece between `vertex i` and
`vertex (i + 1)`. -/
theorem side_def (i : Fin n) :
    P.side i = extGeodesicSegment (P.vertex i) (P.vertex (i + 1)) := by
  rfl

/-- A vertex in `ℍ` lies on the side starting there. -/
theorem mem_side_of_vertex_eq_inl {i : Fin n} {z : ℍ} (h : P.vertex i = .inl z) :
    z ∈ P.side i := by
  rw [side_def, h]
  exact left_mem_extGeodesicSegment z _

/-- A vertex in `ℍ` lies on the side ending there. -/
theorem mem_side_of_vertex_add_one_eq_inl {i : Fin n} {z : ℍ} (h : P.vertex (i + 1) = .inl z) :
    z ∈ P.side i := by
  rw [side_def, h]
  exact right_mem_extGeodesicSegment _ z

/-- A side lies on its geodesic line. -/
theorem side_subset_range_sideGeodesic (i : Fin n) :
    P.side i ⊆ Set.range (geodesicLine (P.sideGeodesic i)) :=
  extGeodesicSegment_subset_range_geodesicLine (P.isGeodesicFromTo_sideGeodesic i)

/-- The sides lie in the carrier. -/
theorem side_subset_carrier (i : Fin n) : P.side i ⊆ P.carrier := by
  rw [carrier_def]
  exact Set.subset_iInter fun j ↦ extGeodesicSegment_subset_closure_leftHalfPlane
    (P.vertex_mem_extClosedLeftHalfPlane_sideGeodesic j i)
    (P.vertex_mem_extClosedLeftHalfPlane_sideGeodesic j (i + 1))

/-- Every side belongs to the topological boundary of the polygon. -/
theorem side_subset_frontier_carrier (i : Fin n) : P.side i ⊆ frontier P.carrier := by
  intro z hz
  rw [P.isClosed_carrier.frontier_eq]
  refine ⟨P.side_subset_carrier i hz, ?_⟩
  intro hzi
  have hleft := (P.mem_interior_carrier_iff z).mp hzi i
  exact Set.disjoint_left.1 (disjoint_leftHalfPlane_range_geodesicLine (P.sideGeodesic i))
    hleft (P.side_subset_range_sideGeodesic i hz)

/-! ### Interior angles -/

/-- The interior angle of a convex polygon at `vertex i`: the angle between the edges to
`vertex (i - 1)` and to `vertex (i + 1)`, which is `0` at an ideal vertex. -/
def interiorAngle (i : Fin n) : ℝ :=
  vertexAngle (P.vertex i) (P.vertex (i - 1)) (P.vertex (i + 1))

-- The body of `interiorAngle` is not `@[expose]`d, so downstream modules rewrite with this.
/-- The interior angle of a convex polygon, unfolded. -/
theorem interiorAngle_def (i : Fin n) :
    P.interiorAngle i = vertexAngle (P.vertex i) (P.vertex (i - 1)) (P.vertex (i + 1)) := by
  rfl

/-- The interior angle at an ideal vertex is `0`. -/
@[simp]
theorem interiorAngle_eq_zero_of_vertex_eq_inr {i : Fin n} {ξ : OnePoint ℝ}
    (h : P.vertex i = .inr ξ) : P.interiorAngle i = 0 := by
  rw [interiorAngle_def, h, vertexAngle_inr]

/-- The interior angles are nonnegative. -/
theorem interiorAngle_nonneg (i : Fin n) : 0 ≤ P.interiorAngle i := by
  rw [interiorAngle_def]
  exact vertexAngle_nonneg _ _ _

/-- The interior angle at a finite vertex is positive. -/
theorem interiorAngle_pos_of_isLeft_vertex {i : Fin n} (hi : (P.vertex i).isLeft) :
    0 < P.interiorAngle i := by
  obtain ⟨A, hA⟩ := Sum.isLeft_iff.mp hi
  have hleft := P.vertex_mem_extLeftHalfPlane i (i - 1)
    (sub_one_ne_self (Nat.le_of_succ_le P.three_le) i)
    (fun h ↦ add_one_add_one_ne_self P.three_le i (by rw [← h, sub_add_cancel]))
  rw [hA] at hleft
  have hg := isGeodesicFromTo_geodesicFromTo (hA ▸ P.vertex_ne_vertex_add_one i)
  have hray := isGeodesicFromTo_rayToward (hA ▸ P.vertex_ne_vertex_add_one i)
  rw [hray.extLeftHalfPlane_eq hg] at hleft
  rw [interiorAngle_def, hA, vertexAngle_comm]
  exact vertexAngle_pos_of_mem_extLeftHalfPlane hleft

/-- The interior angles are at most `π`. -/
theorem interiorAngle_le_pi (i : Fin n) : P.interiorAngle i ≤ π := by
  rw [interiorAngle_def]
  exact vertexAngle_le_pi _ _ _

/-! ### The action of `PSL(2, ℝ)` -/

/-- `PSL(2, ℝ)` acts on convex polygons by moving their vertices. -/
instance : MulAction PSL(2, ℝ) (ConvexPolygon n) where
  smul h Q :=
    { vertex := fun i ↦ h • Q.vertex i
      three_le := Q.three_le
      vertex_ne_vertex_add_one := fun i ↦ (MulAction.injective h).ne (Q.vertex_ne_vertex_add_one i)
      vertex_mem_extLeftHalfPlane := fun i j hij hij' ↦ by
        rw [extLeftHalfPlane_geodesicFromTo_smul h (Q.vertex_ne_vertex_add_one i)]
        exact Set.smul_mem_smul_set (Q.vertex_mem_extLeftHalfPlane i j hij hij') }
  one_smul Q := ConvexPolygon.ext (funext fun i ↦ one_smul _ (Q.vertex i))
  mul_smul g h Q := ConvexPolygon.ext (funext fun i ↦ mul_smul g h (Q.vertex i))

/-- The vertices of the translate. -/
@[simp]
theorem vertex_smul (h : PSL(2, ℝ)) (i : Fin n) : (h • P).vertex i = h • P.vertex i := by
  rfl

/-- The sides of the translate are the translates of the sides. -/
@[simp]
theorem side_smul (h : PSL(2, ℝ)) (i : Fin n) : (h • P).side i = h • P.side i := by
  rw [side_def, side_def, vertex_smul, vertex_smul, smul_extGeodesicSegment]

/-- The closed left half-plane of an edge of the translate is the translate of that of the
edge. -/
theorem closure_leftHalfPlane_sideGeodesic_smul (h : PSL(2, ℝ)) (i : Fin n) :
    closure (leftHalfPlane ((h • P).sideGeodesic i)) =
      h • closure (leftHalfPlane (P.sideGeodesic i)) := by
  rw [sideGeodesic_def, sideGeodesic_def, vertex_smul, vertex_smul,
    leftHalfPlane_geodesicFromTo_smul h (P.vertex_ne_vertex_add_one i), closure_smul]

/-- The carrier of the translate is the translate of the carrier. -/
@[simp]
theorem carrier_smul (h : PSL(2, ℝ)) : (h • P).carrier = h • P.carrier := by
  rw [carrier_def, carrier_def, Set.smul_set_iInter]
  exact Set.iInter_congr (P.closure_leftHalfPlane_sideGeodesic_smul h)

/-- The interior angles are invariant under `PSL(2, ℝ)`. -/
@[simp]
theorem interiorAngle_smul (h : PSL(2, ℝ)) (i : Fin n) :
    (h • P).interiorAngle i = P.interiorAngle i := by
  rw [interiorAngle_def, interiorAngle_def, vertex_smul, vertex_smul, vertex_smul]
  exact vertexAngle_smul h (P.vertex_ne_vertex_sub_one i) (P.vertex_ne_vertex_add_one i)

/-! ### Cyclic relabelling -/

/-- The same polygon with its vertices relabelled cyclically, starting from `vertex k`. -/
def rotate (k : Fin n) : ConvexPolygon n where
  vertex i := P.vertex (i + k)
  three_le := P.three_le
  vertex_ne_vertex_add_one i := by
    rw [add_right_comm i 1 k]
    exact P.vertex_ne_vertex_add_one (i + k)
  vertex_mem_extLeftHalfPlane i j hij hij' := by
    have h := P.vertex_mem_extLeftHalfPlane (i + k) (j + k) (fun h ↦ hij (add_right_cancel h))
      (fun h ↦ hij' (add_right_cancel (h.trans (add_right_comm i k 1))))
    rwa [add_right_comm i k 1] at h

/-- The vertices of the relabelled polygon. -/
@[simp]
theorem vertex_rotate (k i : Fin n) : (P.rotate k).vertex i = P.vertex (i + k) := by
  rfl

/-- Relabelling by `0` does nothing. -/
@[simp]
theorem rotate_zero : P.rotate 0 = P := by
  ext i
  rw [vertex_rotate, add_zero]

/-- Relabelling twice is relabelling by the sum. -/
@[simp]
theorem rotate_rotate (k l : Fin n) : (P.rotate k).rotate l = P.rotate (l + k) := by
  ext i
  rw [vertex_rotate, vertex_rotate, vertex_rotate, add_assoc]

/-- The edges of the relabelled polygon. -/
@[simp]
theorem sideGeodesic_rotate (k i : Fin n) :
    (P.rotate k).sideGeodesic i = P.sideGeodesic (i + k) := by
  rw [sideGeodesic_def, sideGeodesic_def, vertex_rotate, vertex_rotate, add_right_comm i 1 k]

/-- The sides of the relabelled polygon. -/
@[simp]
theorem side_rotate (k i : Fin n) : (P.rotate k).side i = P.side (i + k) := by
  rw [side_def, side_def, vertex_rotate, vertex_rotate, add_right_comm i 1 k]

/-- Relabelling the vertices does not change the carrier. -/
@[simp]
theorem carrier_rotate (k : Fin n) : (P.rotate k).carrier = P.carrier := by
  simp_rw [carrier_def, sideGeodesic_rotate]
  exact (Equiv.addRight k).surjective.iInter_comp fun i ↦ closure (leftHalfPlane (P.sideGeodesic i))

/-- The interior angles of the relabelled polygon. -/
@[simp]
theorem interiorAngle_rotate (k i : Fin n) :
    (P.rotate k).interiorAngle i = P.interiorAngle (i + k) := by
  rw [interiorAngle_def, interiorAngle_def, vertex_rotate, vertex_rotate, vertex_rotate,
    sub_add_eq_add_sub, add_right_comm i 1 k]

/-- Relabelling the vertices does not change the angle sum. -/
-- Not `@[simp]`: `interiorAngle_rotate` is, and rewrites its left-hand side first (simpNF).
theorem sum_interiorAngle_rotate (k : Fin n) :
    ∑ i, (P.rotate k).interiorAngle i = ∑ i, P.interiorAngle i := by
  simp_rw [interiorAngle_rotate]
  exact Equiv.sum_comp (Equiv.addRight k) P.interiorAngle

end ConvexPolygon

/-! ### Compact convex polygons -/

namespace CompactConvexPolygon

variable {n : ℕ} [NeZero n] (P : CompactConvexPolygon n)

/-- A compact convex polygon, as a convex polygon without ideal vertices. -/
def toConvexPolygon : ConvexPolygon n where
  vertex i := .inl (P.vertex i)
  three_le := P.three_le
  vertex_ne_vertex_add_one i := Sum.inl_injective.ne (P.vertex_ne_vertex_add_one i)
  vertex_mem_extLeftHalfPlane i j hij hij' := by
    rw [inl_mem_extLeftHalfPlane_iff,
      leftHalfPlane_geodesicFromTo_inl_inl (P.vertex_ne_vertex_add_one i)]
    exact P.vertex_mem_leftHalfPlane i j hij hij'

/-- The vertices of `toConvexPolygon`. -/
@[simp]
theorem vertex_toConvexPolygon (i : Fin n) : P.toConvexPolygon.vertex i = .inl (P.vertex i) := by
  rfl

/-- `toConvexPolygon` does not change the sides. -/
@[simp]
theorem side_toConvexPolygon (i : Fin n) : P.toConvexPolygon.side i = P.side i := by
  rw [ConvexPolygon.side_def, vertex_toConvexPolygon, vertex_toConvexPolygon,
    extGeodesicSegment_inl_inl, side_def]

/-- `toConvexPolygon` does not change the carrier. -/
@[simp]
theorem carrier_toConvexPolygon : P.toConvexPolygon.carrier = P.carrier := by
  rw [ConvexPolygon.carrier_def, carrier_def]
  refine Set.iInter_congr fun i ↦ ?_
  rw [ConvexPolygon.sideGeodesic_def, vertex_toConvexPolygon, vertex_toConvexPolygon,
    leftHalfPlane_geodesicFromTo_inl_inl (P.vertex_ne_vertex_add_one i)]

/-- `toConvexPolygon` does not change the interior angles. -/
@[simp]
theorem interiorAngle_toConvexPolygon (i : Fin n) :
    P.toConvexPolygon.interiorAngle i = P.interiorAngle i := by
  rw [ConvexPolygon.interiorAngle_def, vertex_toConvexPolygon, vertex_toConvexPolygon,
    vertex_toConvexPolygon, vertexAngle_inl_inl_inl, interiorAngle_def]

end CompactConvexPolygon

/-- A convex polygon without ideal vertices is a compact convex polygon. -/
theorem ConvexPolygon.exists_eq_toConvexPolygon {n : ℕ} [NeZero n] (P : ConvexPolygon n)
    (h : ∀ i, ∃ z : ℍ, P.vertex i = .inl z) :
    ∃ Q : CompactConvexPolygon n, Q.toConvexPolygon = P := by
  choose z hz using h
  refine ⟨⟨z, P.three_le, fun i j hij hij' ↦ ?_⟩, ConvexPolygon.ext (funext fun i ↦ (hz i).symm)⟩
  have hne : z i ≠ z (i + 1) := fun he ↦ P.vertex_ne_vertex_add_one i (by rw [hz, hz, he])
  have hj := P.vertex_mem_extLeftHalfPlane i j hij hij'
  simp only [hz] at hj
  rwa [inl_mem_extLeftHalfPlane_iff, leftHalfPlane_geodesicFromTo_inl_inl hne] at hj

end TauCeti.UpperHalfPlane
