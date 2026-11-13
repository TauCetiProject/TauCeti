/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Zeeman
public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Certificate

/-!
# Bing's house

Bing's house with two rooms is a box divided into an upper and a lower room by a middle floor.
The upper room is entered through a tunnel that starts at a hole in the floor of the box, crosses
the lower room, and opens through a hole in the middle floor; symmetrically, the lower room is
entered through a tunnel from a hole in the roof that crosses the upper room. Each room also
contains a small wall joining its tunnel to an outer wall. The resulting two-dimensional
polyhedron is contractible, but every edge lies on at least two of its faces, so no
triangulation of it has a free face and none is collapsible. With the dunce hat it is the
standard example showing that collapsibility is strictly stronger than contractibility.

This file triangulates Bing's house as an abstract simplicial complex on `Fin 72`. The vertices
are the integer points of the box `[0, 5] × [0, 3] × [0, 2]`, the point `(x, y, z)` being the
vertex `x + 6 * y + 24 * z`. The house is a union of `83` unit squares of this grid: the lower
tunnel runs over `[1, 2] × [1, 2] × [0, 1]`, the upper tunnel over `[3, 4] × [1, 2] × [1, 2]`,
and the two small walls are `[0, 1] × {1} × [0, 1]` and `[4, 5] × {1} × [1, 2]`. Each square is
cut into two triangles along the diagonal through its lowest corner.

No free face is checked by `checkMaskNoFreePair`. Contractibility comes from the box: its
Freudenthal triangulation, which cuts each unit cube into six tetrahedra along the diagonal
through its lowest corner, contains the triangulated house as a subcomplex, collapses onto it, and
also collapses to a point. Both collapses are explicit sequences checked with
`checkMaskCollapseTo` and `checkMaskCollapse`, and a collapse is a homotopy equivalence.

## Main definitions

All declarations are in the namespace `TauCeti`.

* `bingHouseSquares`: the unit squares of the house.
* `bingHouseTriangles`: the bit masks of its `166` triangles.
* `bingHouse`: the triangulated Bing's house.

## Main results

* `not_isFreePair_bingHouse`: Bing's house has no free face.
* `not_collapsible_bingHouse`: Bing's house is not collapsible.
* `contractibleSpace_realization_bingHouse`: its realization is contractible.
* `contractible2Complex_bingHouse`: it is a contractible 2-complex.

## References

* R. H. Bing, *Some aspects of the topology of 3-manifolds related to the Poincaré conjecture*,
  in *Lectures on Modern Mathematics II* (1964), 93–128.
* A. Hatcher, *Algebraic Topology* (2002), Chapter 0 (the house with two rooms).
* H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. 43 (1942),
  580–582 (the triangulation of the cube).
* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology* (1972),
  Chapter 3 (simplicial collapse).
-/

public section

open PreAbstractSimplicialComplex AbstractSimplicialComplex TauCeti.PreAbstractSimplicialComplex

namespace TauCeti

/-- The unit squares of Bing's house. The entry `(c, a, b)` is the square with lowest corner the
vertex `c` spanned by the coordinate strides `a < b`, where `1`, `6` and `24` are the strides of
the `x`, `y` and `z` directions. The horizontal squares form the floor, the middle floor and the
roof, minus the holes `[1, 2] × [1, 2]` in the floor and middle floor and `[3, 4] × [1, 2]` in the
middle floor and roof. The squares in the planes `x = const` form the two end walls and the
sides of the tunnels; those in the planes `y = const` form the front and back walls, the other
sides of the tunnels and the two small walls. -/
def bingHouseSquares : List (ℕ × ℕ × ℕ) :=
  (List.range 72).flatMap fun c =>
    let x := c % 6
    let y := c / 6 % 4
    let z := c / 24
    (if x < 5 ∧ y < 3 ∧ (z = 0 ∧ (x, y) ≠ (1, 1) ∨ z = 1 ∧ (x, y) ≠ (1, 1) ∧ (x, y) ≠ (3, 1) ∨
        z = 2 ∧ (x, y) ≠ (3, 1)) then [(c, 1, 6)] else []) ++
    (if y < 3 ∧ z < 2 ∧ (x = 0 ∨ x = 5 ∨
        y = 1 ∧ (z = 0 ∧ (x = 1 ∨ x = 2) ∨ z = 1 ∧ (x = 3 ∨ x = 4))) then [(c, 6, 24)] else []) ++
    (if x < 5 ∧ z < 2 ∧ (y = 0 ∨ y = 3 ∨ (y = 1 ∨ y = 2) ∧ (x = 1 ∧ z = 0 ∨ x = 3 ∧ z = 1) ∨
        y = 1 ∧ (x = 0 ∧ z = 0 ∨ x = 4 ∧ z = 1)) then [(c, 1, 24)] else [])

/-- The bit masks of the triangles of Bing's house: the square `(c, a, b)` of `bingHouseSquares`
is cut into the triangles `{c, c + a, c + a + b}` and `{c, c + b, c + a + b}`. -/
def bingHouseTriangles : List ℕ :=
  bingHouseSquares.flatMap fun (c, a, b) =>
    [2 ^ c ||| 2 ^ (c + a) ||| 2 ^ (c + a + b), 2 ^ c ||| 2 ^ (c + b) ||| 2 ^ (c + a + b)]

/-- Every vertex of the grid lies on a triangle of Bing's house. -/
private theorem singleton_mem_ofMasks_bingHouseTriangles (v : Fin 72) :
    {v} ∈ ofMasks 72 bingHouseTriangles := by
  have key : ∀ v : Fin 72, ∃ g ∈ bingHouseTriangles, g.testBit v = true := by decide +kernel
  obtain ⟨g, hg, hv⟩ := key v
  exact mem_ofMasks.mpr
    ⟨Finset.singleton_nonempty v, g, hg, Finset.singleton_subset_iff.mpr (mem_maskFace.mpr hv)⟩

/-- **Bing's house**, triangulated with `72` vertices and the `166` triangles of
`bingHouseTriangles`. -/
def bingHouse : AbstractSimplicialComplex (Fin 72) where
  toPreAbstractSimplicialComplex := ofMasks 72 bingHouseTriangles
  singleton_mem := singleton_mem_ofMasks_bingHouseTriangles

/-- The faces of Bing's house are the nonempty subsets of its triangles. -/
@[simp]
theorem mem_bingHouse {σ : Finset (Fin 72)} :
    σ ∈ bingHouse ↔ σ.Nonempty ∧ ∃ g ∈ bingHouseTriangles, σ ⊆ maskFace 72 g :=
  mem_ofMasks

/-- The precomplex underlying Bing's house is generated by its triangles. -/
theorem bingHouse_toPreAbstractSimplicialComplex :
    bingHouse.toPreAbstractSimplicialComplex = ofMasks 72 bingHouseTriangles :=
  (rfl)

/-- Bing's house has finitely many faces. -/
theorem finite_faces_bingHouse : bingHouse.faces.Finite :=
  Set.toFinite _

/-- The triangles of Bing's house have three vertices. -/
theorem card_maskFace_of_mem_bingHouseTriangles {g : ℕ} (hg : g ∈ bingHouseTriangles) :
    (maskFace 72 g).card = 3 := by
  revert g
  decide +kernel

/-- The triangle `{0, 1, 7}` of the floor, with bit mask `131`, is a triangle of Bing's house. -/
private theorem mem_bingHouseTriangles_131 : 131 ∈ bingHouseTriangles := by
  decide +kernel

/-- The triangle `{0, 1, 7}` is a face of Bing's house. -/
private theorem maskFace_mem_bingHouse_131 : maskFace 72 131 ∈ bingHouse :=
  mem_bingHouse.mpr ⟨Finset.card_pos.mp (by
    rw [card_maskFace_of_mem_bingHouseTriangles mem_bingHouseTriangles_131]; omega),
    131, mem_bingHouseTriangles_131, subset_rfl⟩

/-- Bing's house is two-dimensional. -/
theorem dimension_bingHouse : dimension bingHouse = 2 := by
  refine le_antisymm (AbstractSimplicialComplex.dimension_le_iff.mpr fun σ hσ => ?_) ?_
  · obtain ⟨-, g, hg, hσg⟩ := mem_bingHouse.mp hσ
    have := Finset.card_le_card hσg
    rw [card_maskFace_of_mem_bingHouseTriangles hg] at this
    exact_mod_cast (by omega : σ.card - 1 ≤ 2)
  · simpa [card_maskFace_of_mem_bingHouseTriangles mem_bingHouseTriangles_131] using
      AbstractSimplicialComplex.le_dimension maskFace_mem_bingHouse_131

/-- **Bing's house has no free face.** Every edge of a triangle lies on a second triangle. -/
theorem not_isFreePair_bingHouse (σ τ : Finset (Fin 72)) :
    ¬ IsFreePair bingHouse.toPreAbstractSimplicialComplex σ τ :=
  not_isFreePair_ofMasks_of_checkMaskNoFreePair (by decide +kernel) σ τ

/-- **Bing's house is not collapsible**: it has no free face to start a collapse. -/
theorem not_collapsible_bingHouse :
    ¬ PreAbstractSimplicialComplex.Collapsible bingHouse.toPreAbstractSimplicialComplex := by
  intro hcol
  obtain ⟨v, h⟩ := hcol.exists_eq_point_of_forall_not_isFreePair not_isFreePair_bingHouse
  have hmem : maskFace 72 131 ∈ bingHouse.toPreAbstractSimplicialComplex :=
    maskFace_mem_bingHouse_131
  rw [h, mem_point] at hmem
  simpa [hmem] using card_maskFace_of_mem_bingHouseTriangles mem_bingHouseTriangles_131

/-- The bit masks of the tetrahedra of the Freudenthal triangulation of the box
`[0, 5] × [0, 3] × [0, 2]`: the unit cube with lowest corner `c` is cut into the six tetrahedra
`{c, c + a, c + a + b, c + 31}` spanned by the monotone lattice paths from `c` to the opposite
corner `c + 31`, one for each ordering of the strides `1`, `6` and `24`. -/
private def bingBoxTetrahedra : List ℕ :=
  (List.range 72).flatMap fun c =>
    if c % 6 < 5 ∧ c / 6 % 4 < 3 ∧ c / 24 < 2 then
      [(1, 6), (1, 24), (6, 1), (6, 24), (24, 1), (24, 6)].map fun (a, b) =>
        2 ^ c ||| 2 ^ (c + a) ||| 2 ^ (c + a + b) ||| 2 ^ (c + 31)
    else []

/-- The triangulated box, as an abstract simplicial complex on the vertices of the grid. -/
private def bingBox : AbstractSimplicialComplex (Fin 72) where
  toPreAbstractSimplicialComplex := ofMasks 72 bingBoxTetrahedra
  singleton_mem v := by
    have key : ∀ v : Fin 72, ∃ g ∈ bingBoxTetrahedra, g.testBit v = true := by decide +kernel
    obtain ⟨g, hg, hv⟩ := key v
    exact mem_ofMasks.mpr ⟨Finset.singleton_nonempty v, g, hg,
      Finset.singleton_subset_iff.mpr (mem_maskFace.mpr hv)⟩

/-- A collapse of the triangulated box onto Bing's house, as steps `(σ, i)` collapsing the face
with vertex list `σ` through its coface obtained by adjoining `i`. The bit mask of `σ` is
`(σ.map (2 ^ ·)).sum`, as in `Nat.bitIndices`. -/
private def bingBoxToHouseSteps : List (List ℕ × ℕ) :=
  [([57, 63, 64], 33), ([7, 13, 14], 38), ([7, 13, 38], 37), ([7, 37, 38], 31), ([57, 58, 64], 33),
   ([31, 37, 38], 62), ([7, 31, 38], 32), ([31, 38, 62], 32), ([31, 37, 62], 61),
   ([31, 32, 62], 56), ([37, 38, 62], 68), ([31, 61, 62], 55), ([7, 32, 38], 8), ([31, 55, 62], 56),
   ([32, 56, 62], 63), ([33, 58, 64], 34), ([31, 55, 61], 30), ([30, 55, 61], 54),
   ([31, 37, 61], 30), ([31, 55, 56], 25), ([7, 8, 38], 14), ([30, 37, 61], 36), ([33, 34, 64], 40),
   ([30, 54, 55], 24), ([32, 56, 63], 57), ([32, 56, 57], 26), ([37, 38, 68], 44),
   ([32, 57, 63], 33), ([30, 54, 61], 60), ([32, 33, 57], 26), ([24, 54, 55], 48),
   ([37, 44, 68], 43), ([38, 62, 68], 69), ([31, 32, 56], 25), ([30, 36, 61], 60),
   ([33, 34, 40], 9), ([37, 62, 68], 61), ([26, 33, 57], 27), ([33, 40, 64], 39),
   ([24, 30, 55], 31), ([27, 33, 57], 58), ([26, 27, 57], 51), ([33, 39, 64], 63),
   ([9, 33, 40], 39), ([26, 56, 57], 50), ([26, 50, 56], 25), ([38, 44, 68], 69),
   ([32, 38, 62], 63), ([36, 37, 61], 67), ([37, 61, 68], 67), ([38, 62, 63], 69),
   ([36, 37, 67], 43), ([25, 55, 56], 49), ([24, 31, 55], 25), ([25, 50, 56], 49),
   ([27, 33, 58], 34), ([27, 51, 57], 58), ([37, 67, 68], 43), ([32, 33, 63], 39),
   ([32, 38, 63], 39), ([36, 60, 61], 67), ([25, 49, 55], 24), ([26, 32, 56], 25),
   ([26, 51, 57], 50), ([27, 34, 58], 28), ([9, 34, 40], 10), ([38, 63, 69], 39),
   ([38, 44, 69], 45), ([39, 63, 69], 70), ([9, 33, 39], 8), ([24, 49, 55], 48), ([9, 10, 34], 3),
   ([3, 9, 34], 33), ([8, 33, 39], 32), ([10, 34, 40], 41), ([8, 9, 33], 2), ([39, 69, 70], 45),
   ([9, 10, 40], 16), ([9, 39, 40], 15), ([9, 15, 40], 16), ([38, 39, 69], 45), ([8, 32, 33], 2),
   ([2, 8, 32], 1), ([1, 2, 32], 26), ([2, 26, 32], 33), ([36, 60, 67], 66), ([27, 28, 58], 52),
   ([10, 34, 41], 35), ([39, 45, 70], 46), ([39, 63, 70], 64), ([27, 52, 58], 51),
   ([10, 40, 41], 16), ([39, 64, 70], 40), ([39, 46, 70], 40), ([28, 52, 58], 59),
   ([36, 66, 67], 42), ([1, 26, 32], 25), ([28, 52, 59], 53), ([3, 33, 34], 27), ([1, 25, 32], 31),
   ([8, 32, 39], 38), ([36, 43, 67], 42), ([2, 9, 33], 3), ([28, 53, 59], 29), ([3, 27, 33], 2),
   ([3, 27, 34], 28), ([16, 40, 41], 47), ([1, 8, 32], 7), ([40, 64, 70], 71), ([2, 26, 33], 27),
   ([40, 70, 71], 46), ([15, 39, 40], 46), ([10, 35, 41], 11), ([28, 29, 59], 35), ([1, 31, 32], 7),
   ([15, 40, 46], 16), ([16, 40, 47], 46), ([10, 11, 41], 17), ([28, 35, 59], 34),
   ([10, 17, 41], 16), ([10, 11, 35], 4), ([1, 7, 31], 0), ([0, 7, 31], 6), ([16, 46, 47], 22),
   ([40, 64, 71], 65), ([15, 39, 46], 45), ([1, 25, 31], 0), ([3, 28, 34], 4), ([9, 15, 39], 8),
   ([28, 34, 58], 59), ([40, 65, 71], 41), ([40, 46, 71], 47), ([40, 64, 65], 34), ([3, 10, 34], 4),
   ([34, 64, 65], 58), ([4, 11, 35], 5), ([16, 17, 41], 47), ([0, 25, 31], 24), ([4, 5, 35], 29),
   ([8, 15, 39], 14), ([15, 45, 46], 21), ([0, 6, 31], 30), ([34, 40, 65], 41), ([15, 21, 45], 14),
   ([4, 10, 34], 35), ([16, 22, 46], 15), ([15, 39, 45], 14), ([16, 17, 47], 23), ([8, 38, 39], 14),
   ([16, 22, 47], 23), ([4, 28, 34], 35), ([0, 30, 31], 24), ([40, 47, 71], 41), ([4, 28, 35], 29),
   ([14, 38, 39], 45), ([34, 58, 65], 59), ([34, 41, 65], 35), ([34, 35, 65], 59),
   ([15, 22, 46], 21), ([14, 38, 45], 44), ([14, 44, 45], 20), ([14, 20, 44], 13),
   ([14, 38, 44], 13), ([13, 38, 44], 37), ([14, 21, 45], 20), ([13, 20, 44], 19),
   ([13, 37, 44], 43), ([13, 37, 43], 12), ([12, 37, 43], 36), ([12, 36, 43], 42),
   ([12, 13, 37], 6), ([12, 13, 43], 19), ([13, 19, 43], 44), ([12, 19, 43], 18),
   ([12, 18, 43], 42), ([6, 12, 37], 36), ([6, 36, 37], 30), ([6, 30, 37], 31), ([6, 31, 37], 7),
   ([6, 13, 37], 7), ([37, 68], 43), ([28, 58], 59), ([8, 33], 2), ([15, 40], 16), ([31, 38], 32),
   ([40, 65], 41), ([32, 62], 63), ([28, 59], 34), ([7, 38], 14), ([30, 55], 31), ([34, 65], 59),
   ([31, 62], 56), ([10, 41], 16), ([16, 41], 47), ([38, 62], 69), ([39, 70], 40), ([37, 62], 61),
   ([6, 37], 7), ([16, 47], 23), ([36, 61], 67), ([32, 63], 39), ([14, 44], 13), ([12, 43], 42),
   ([1, 31], 0), ([13, 43], 44), ([9, 40], 16), ([40, 70], 46), ([1, 32], 7), ([27, 57], 58),
   ([33, 40], 39), ([7, 14], 8), ([9, 34], 33), ([15, 45], 14), ([39, 69], 45), ([31, 56], 25),
   ([9, 33], 3), ([3, 33], 2), ([2, 32], 33), ([31, 55], 25), ([27, 58], 51), ([26, 56], 25),
   ([13, 44], 19), ([32, 57], 26), ([0, 31], 24), ([26, 57], 50), ([57, 64], 33), ([2, 33], 27),
   ([12, 37], 36), ([38, 63], 39), ([40, 71], 41), ([32, 56], 25), ([10, 40], 16), ([16, 40], 46),
   ([25, 56], 49), ([15, 39], 14), ([36, 67], 42), ([9, 39], 8), ([25, 55], 24), ([24, 55], 48),
   ([38, 68], 69), ([10, 34], 35), ([10, 35], 4), ([37, 61], 67), ([8, 39], 14), ([31, 61], 30),
   ([30, 61], 60), ([38, 69], 45), ([3, 34], 4), ([16, 46], 15), ([33, 64], 63), ([15, 46], 21),
   ([37, 67], 43), ([4, 34], 35), ([4, 35], 29), ([14, 39], 45), ([14, 45], 20)]

/-- A collapse of the triangulated box to the vertex `33`, in the same format. -/
private def bingBoxToPointSteps : List (List ℕ × ℕ) :=
  [([28, 52, 53], 59), ([11, 35, 41], 10), ([0, 6, 7], 31), ([51, 52, 58], 27), ([2, 3, 27], 33),
   ([12, 36, 42], 43), ([29, 35, 59], 28), ([12, 42, 43], 18), ([63, 64, 70], 39),
   ([50, 56, 57], 26), ([8, 14, 15], 39), ([18, 19, 43], 12), ([22, 23, 47], 16),
   ([12, 36, 43], 37), ([10, 11, 41], 17), ([28, 35, 59], 34), ([41, 47, 71], 40),
   ([43, 44, 68], 37), ([6, 12, 13], 37), ([40, 41, 47], 16), ([50, 51, 57], 26), ([0, 7, 31], 1),
   ([20, 21, 45], 14), ([8, 15, 39], 9), ([3, 4, 28], 34), ([28, 29, 59], 53), ([5, 29, 35], 4),
   ([13, 19, 20], 44), ([30, 36, 60], 61), ([36, 42, 43], 67), ([21, 22, 46], 15),
   ([57, 63, 64], 33), ([27, 51, 58], 57), ([2, 3, 9], 33), ([41, 65, 71], 40), ([6, 7, 31], 37),
   ([55, 56, 62], 31), ([24, 48, 49], 55), ([14, 20, 45], 44), ([44, 45, 69], 38),
   ([42, 66, 67], 36), ([33, 57, 63], 32), ([25, 26, 50], 56), ([24, 25, 49], 55), ([2, 9, 33], 8),
   ([24, 48, 55], 54), ([37, 43, 44], 13), ([12, 19, 43], 13), ([3, 9, 10], 34), ([52, 58, 59], 28),
   ([62, 68, 69], 38), ([33, 57, 64], 58), ([28, 29, 35], 4), ([13, 37, 44], 38), ([7, 13, 14], 38),
   ([4, 10, 11], 35), ([13, 19, 44], 43), ([17, 23, 47], 16), ([43, 67, 68], 37),
   ([15, 16, 22], 46), ([33, 58, 64], 34), ([24, 54, 55], 30), ([6, 30, 36], 37), ([3, 9, 33], 34),
   ([14, 44, 45], 38), ([55, 61, 62], 31), ([4, 11, 35], 5), ([27, 51, 57], 26), ([6, 31, 37], 30),
   ([37, 67, 68], 61), ([46, 70, 71], 40), ([6, 7, 37], 13), ([27, 52, 58], 28), ([1, 7, 8], 32),
   ([6, 36, 37], 12), ([13, 20, 44], 14), ([15, 16, 46], 40), ([12, 13, 43], 37), ([28, 34, 35], 4),
   ([45, 69, 70], 39), ([24, 25, 55], 31), ([16, 40, 47], 46), ([64, 65, 71], 40),
   ([40, 64, 65], 34), ([46, 47, 71], 40), ([39, 69, 70], 63), ([31, 55, 56], 25),
   ([25, 26, 56], 32), ([14, 21, 45], 15), ([2, 8, 33], 32), ([2, 26, 27], 33), ([40, 41, 65], 34),
   ([62, 63, 69], 38), ([3, 10, 34], 4), ([38, 68, 69], 44), ([64, 70, 71], 40), ([3, 28, 34], 27),
   ([7, 31, 37], 38), ([0, 24, 30], 31), ([30, 36, 37], 61), ([14, 38, 44], 13), ([8, 9, 33], 39),
   ([35, 41, 65], 34), ([31, 37, 38], 62), ([22, 46, 47], 16), ([33, 63, 64], 39), ([7, 8, 14], 38),
   ([39, 45, 70], 46), ([9, 15, 16], 40), ([27, 28, 58], 34), ([8, 33, 39], 32), ([34, 40, 64], 33),
   ([31, 55, 61], 30), ([1, 2, 26], 32), ([34, 64, 65], 58), ([39, 64, 70], 40), ([9, 33, 34], 40),
   ([0, 24, 31], 25), ([7, 8, 38], 32), ([15, 21, 45], 46), ([10, 35, 41], 34), ([38, 44, 68], 37),
   ([1, 2, 32], 8), ([33, 39, 64], 40), ([8, 14, 39], 38), ([39, 45, 69], 38), ([0, 1, 31], 25),
   ([28, 34, 58], 59), ([31, 61, 62], 37), ([9, 10, 16], 40), ([34, 58, 65], 59),
   ([38, 62, 63], 32), ([16, 17, 47], 41), ([9, 33, 39], 40), ([38, 39, 45], 14), ([7, 31, 38], 32),
   ([7, 37, 38], 13), ([8, 38, 39], 32), ([38, 63, 69], 39), ([25, 49, 50], 56), ([14, 15, 45], 39),
   ([31, 56, 62], 32), ([3, 27, 33], 34), ([10, 16, 17], 41), ([60, 66, 67], 36),
   ([30, 31, 61], 37), ([32, 33, 39], 63), ([9, 15, 40], 39), ([37, 61, 68], 62),
   ([15, 39, 40], 46), ([0, 6, 31], 30), ([60, 61, 67], 36), ([31, 32, 38], 62), ([32, 56, 62], 63),
   ([25, 49, 55], 56), ([2, 32, 33], 26), ([33, 57, 58], 27), ([30, 54, 60], 61),
   ([37, 38, 62], 68), ([9, 34, 40], 10), ([30, 31, 55], 24), ([39, 45, 46], 15),
   ([26, 27, 33], 57), ([37, 43, 67], 36), ([25, 26, 32], 1), ([26, 32, 33], 57),
   ([35, 59, 65], 34), ([39, 40, 70], 46), ([56, 57, 63], 32), ([10, 34, 35], 4),
   ([36, 61, 67], 37), ([7, 31, 32], 1), ([38, 39, 63], 32), ([30, 54, 61], 55), ([26, 32, 56], 57),
   ([10, 34, 40], 41), ([16, 40, 41], 10), ([1, 25, 32], 31), ([27, 33, 34], 58),
   ([25, 31, 56], 32), ([11, 41], 17), ([29, 35], 4), ([49, 50], 56), ([25, 50], 56), ([2, 3], 33),
   ([47, 71], 40), ([40, 47], 46), ([45, 70], 46), ([7, 37], 13), ([35, 65], 34), ([50, 56], 26),
   ([1, 2], 8), ([11, 17], 10), ([21, 45], 46), ([35, 41], 34), ([48, 49], 55), ([45, 69], 38),
   ([64, 65], 58), ([2, 9], 8), ([55, 62], 31), ([41, 71], 40), ([28, 35], 4), ([22, 23], 16),
   ([57, 64], 58), ([31, 61], 37), ([24, 48], 54), ([52, 58], 28), ([21, 22], 15), ([62, 69], 38),
   ([28, 58], 59), ([57, 63], 32), ([3, 33], 34), ([1, 8], 32), ([20, 45], 44), ([68, 69], 44),
   ([9, 16], 40), ([7, 8], 32), ([20, 21], 14), ([6, 7], 13), ([2, 8], 32), ([15, 22], 46),
   ([46, 71], 40), ([15, 16], 40), ([45, 46], 15), ([60, 66], 36), ([51, 52], 27), ([64, 71], 40),
   ([9, 33], 40), ([67, 68], 61), ([38, 63], 32), ([43, 68], 37), ([12, 42], 18), ([3, 10], 4),
   ([7, 14], 38), ([29, 59], 53), ([30, 36], 61), ([7, 13], 38), ([17, 47], 41), ([13, 20], 14),
   ([3, 9], 34), ([25, 26], 1), ([14, 21], 15), ([7, 31], 1), ([35, 59], 34), ([0, 7], 1),
   ([2, 27], 33), ([0, 1], 25), ([10, 11], 35), ([10, 17], 41), ([51, 58], 57), ([25, 49], 56),
   ([14, 15], 39), ([27, 52], 28), ([7, 38], 32), ([65, 71], 40), ([8, 15], 9), ([10, 35], 4),
   ([15, 40], 46), ([21, 46], 15), ([26, 56], 57), ([2, 33], 26), ([18, 19], 12), ([61, 67], 37),
   ([40, 71], 70), ([1, 26], 32), ([28, 52], 59), ([6, 31], 30), ([4, 10], 34), ([9, 34], 10),
   ([8, 14], 38), ([42, 66], 36), ([52, 59], 53), ([4, 11], 5), ([18, 42], 43), ([50, 51], 26),
   ([42, 43], 67), ([40, 65], 34), ([37, 67], 36), ([36, 42], 67), ([12, 19], 13), ([17, 41], 16),
   ([58, 64], 34), ([46, 47], 16), ([26, 33], 57), ([31, 38], 62), ([23, 47], 16), ([56, 62], 63),
   ([64, 70], 40), ([3, 28], 27), ([66, 67], 36), ([18, 43], 12), ([1, 25], 31), ([56, 63], 32),
   ([12, 43], 37), ([7, 32], 1), ([44, 68], 37), ([22, 47], 16), ([41, 47], 16), ([69, 70], 63),
   ([0, 6], 30), ([6, 36], 12), ([63, 70], 39), ([63, 69], 39), ([39, 70], 46), ([43, 67], 36),
   ([17, 23], 16), ([53, 59], 28), ([10, 34], 41), ([31, 56], 32), ([62, 63], 32), ([12, 36], 37),
   ([8, 9], 39), ([28, 53], 29), ([28, 29], 4), ([48, 54], 55), ([58, 65], 59), ([5, 29], 4),
   ([12, 13], 37), ([44, 69], 38), ([28, 59], 34), ([46, 70], 40), ([36, 67], 60), ([2, 32], 26),
   ([16, 22], 46), ([54, 60], 61), ([41, 65], 34), ([6, 30], 37), ([24, 54], 30), ([13, 19], 43),
   ([1, 32], 31), ([16, 46], 40), ([58, 59], 34), ([3, 4], 34), ([50, 57], 26), ([30, 60], 61),
   ([19, 43], 44), ([63, 64], 39), ([24, 49], 55), ([34, 65], 59), ([56, 57], 32), ([30, 54], 55),
   ([40, 46], 39), ([15, 45], 39), ([34, 35], 4), ([0, 30], 31), ([51, 57], 26), ([39, 46], 15),
   ([27, 28], 34), ([12, 37], 6), ([15, 39], 9), ([0, 31], 25), ([49, 56], 55), ([8, 33], 32),
   ([36, 43], 37), ([37, 43], 13), ([16, 40], 10), ([4, 35], 5), ([44, 45], 38), ([27, 51], 26),
   ([32, 56], 25), ([16, 41], 10), ([38, 45], 14), ([3, 27], 34), ([19, 20], 44), ([8, 38], 32),
   ([39, 69], 38), ([5, 35], 11), ([28, 34], 4), ([13, 43], 44), ([54, 61], 55), ([14, 20], 44),
   ([0, 25], 24), ([26, 27], 57), ([39, 45], 14), ([57, 58], 27), ([34, 64], 33), ([34, 41], 40),
   ([61, 68], 62), ([25, 32], 31), ([55, 61], 30), ([6, 13], 37), ([55, 56], 25), ([25, 55], 31),
   ([24, 25], 31), ([60, 61], 36), ([31, 55], 24), ([24, 31], 30), ([13, 37], 38), ([61, 62], 37),
   ([30, 61], 37), ([31, 32], 62), ([14, 39], 38), ([38, 39], 32), ([37, 44], 38), ([24, 55], 30),
   ([40, 41], 10), ([34, 40], 33), ([36, 37], 61), ([27, 34], 58), ([27, 57], 33), ([33, 57], 32),
   ([9, 39], 40), ([31, 62], 37), ([26, 57], 32), ([32, 62], 38), ([33, 34], 58), ([27, 33], 58),
   ([10, 40], 9), ([8, 32], 39), ([30, 31], 37), ([14, 44], 13), ([38, 44], 13), ([13, 38], 14),
   ([32, 33], 63), ([37, 62], 68), ([62, 68], 38), ([32, 63], 39), ([39, 63], 33), ([39, 64], 40),
   ([33, 64], 40), ([39, 40], 33), ([37, 38], 68), ([43], 44), ([51], 26), ([18], 12), ([63], 33),
   ([66], 36), ([64], 40), ([20], 44), ([27], 58), ([28], 4), ([12], 6), ([47], 16), ([50], 26),
   ([69], 38), ([3], 34), ([23], 16), ([56], 25), ([22], 46), ([0], 24), ([46], 15), ([25], 31),
   ([54], 55), ([7], 1), ([1], 31), ([52], 53), ([19], 44), ([41], 10), ([53], 29), ([48], 55),
   ([21], 15), ([45], 14), ([44], 13), ([49], 55), ([29], 4), ([42], 67), ([55], 30), ([35], 11),
   ([17], 16), ([16], 10), ([13], 14), ([15], 9), ([2], 26), ([31], 37), ([62], 38), ([71], 70),
   ([11], 5), ([57], 32), ([10], 9), ([14], 38), ([8], 39), ([26], 32), ([24], 30), ([5], 4),
   ([4], 34), ([9], 40), ([30], 37), ([67], 60), ([60], 36), ([36], 61), ([70], 40), ([40], 33),
   ([61], 37), ([65], 59), ([6], 37), ([59], 34), ([34], 58), ([37], 68), ([68], 38), ([38], 32),
   ([32], 39), ([39], 33), ([58], 33)]

/-- The triangulated box collapses onto Bing's house. -/
private theorem collapsesTo_bingBox_bingHouse :
    CollapsesTo bingBox.toPreAbstractSimplicialComplex bingHouse.toPreAbstractSimplicialComplex :=
  collapsesTo_ofMasks_of_checkMaskCollapseTo
    (steps := bingBoxToHouseSteps.map fun p => ((p.1.map (2 ^ ·)).sum, p.2)) (by decide +kernel)

/-- The triangulated box is collapsible. -/
private theorem collapsible_bingBox :
    PreAbstractSimplicialComplex.Collapsible bingBox.toPreAbstractSimplicialComplex :=
  collapsible_ofMasks_of_checkMaskCollapse
    (steps := bingBoxToPointSteps.map fun p => ((p.1.map (2 ^ ·)).sum, p.2)) (v := 33)
    (by decide +kernel)

/-- **Bing's house is contractible.** It is the end of a collapse of the triangulated box, which
is collapsible, and a collapse is a homotopy equivalence. -/
theorem contractibleSpace_realization_bingHouse : ContractibleSpace (Realization bingHouse) :=
  collapsesTo_bingBox_bingHouse.contractibleSpace_realization_iff.mpr
    collapsible_bingBox.contractibleSpace_realization

/-- Bing's house is a contractible 2-complex in the sense of Zeeman's conjecture. -/
theorem contractible2Complex_bingHouse : Contractible2Complex bingHouse :=
  contractible2Complex_iff.mpr
    ⟨finite_faces_bingHouse, dimension_bingHouse.le, contractibleSpace_realization_bingHouse⟩

end TauCeti
