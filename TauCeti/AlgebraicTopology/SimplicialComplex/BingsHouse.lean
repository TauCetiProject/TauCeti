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

Bing's house with two rooms is a two-dimensional polyhedron inside a box. A horizontal floor
divides the box into two rooms. The upper room is entered from below the box through a vertical
tube crossing the lower room, and the lower room is entered from above the box through a vertical
tube crossing the upper room. Each tube is joined to a side wall of the room it crosses by a
vertical wall, which cuts the room around the tube into a ball. Pushing in through the two holes
collapses the box onto the house, so the house is contractible. But in every triangulation of the
house each edge lies in at least two triangles, so there is no free face and the triangulation is
not collapsible; this file proves this for an explicit triangulation.

This file triangulates Bing's house by an abstract simplicial complex on `Fin 11` with
thirty-one triangles. It comes from the cubical model in the box `[0, 5] × [0, 3] × [0, 2]`: the
floor is at height `1`, the tube crossing the lower room lies over the unit square
`[1, 2] × [1, 2]` and the tube crossing the upper room over `[3, 4] × [1, 2]`, and the walls lie in
the plane `y = 1`, over `[0, 1]` in the lower room and over `[4, 5]` in the upper room. Its unit
squares, each split along the diagonal through its lowest corner, give `166` triangles on the `72`
grid points. Writing the grid point `(x, y, z)` as `xyz`, the following sixty-one edge contractions
`b → a`, merging `b` into `a` in this order, reduce it to `bingsHouseTriangles`:

```text
322→432, 522→512, 430→420, 302→201, 332→222, 211→110, 022→021, 120→020, 221→321, 032→031,
202→201, 101→201, 301→201, 520→510, 300→400, 131→031, 532→432, 521→511, 210→320, 531→511,
320→321, 421→511, 312→412, 220→321, 410→510, 021→031, 402→502, 422→321, 222→232, 121→111,
102→001, 310→321, 500→511, 001→201, 030→130, 230→020, 012→031, 530→510, 502→512, 130→020,
330→020, 212→201, 002→031, 431→511, 100→000, 132→122, 000→011, 200→011, 112→201, 231→331,
420→510, 331→511, 432→232, 510→020, 311→110, 401→501, 501→511, 122→031, 400→011, 232→031,
411→511
```

Each contraction is a PL homeomorphism of the polyhedron: it satisfies the link condition
`lk a ∩ lk b = lk ab`, and the part of `lk b` outside the open star of `a` is a tree that is a cone
on the points of `lk ab` relative to them, so the star of `b` is replaced by a book of triangles
with the same boundary `lk b`. The vertices `0, …, 10` are the surviving grid points
`(0, 1, 0)`, `(0, 1, 1)`, `(0, 2, 0)`, `(0, 3, 1)`, `(1, 1, 0)`, `(1, 1, 1)`, `(2, 0, 1)`,
`(3, 2, 1)`, `(4, 1, 2)`, `(5, 1, 1)` and `(5, 1, 2)`. Every edge lies in two or three triangles,
so there is no free face.

Contractibility follows the picture of the box: a three-dimensional complex on the same vertices,
with twenty-three tetrahedra and obtained from a triangulation of the box by edge contractions,
collapses onto the house in `23` elementary collapses and to a vertex in `64`. Both sequences are
checked with the bit-mask certificates of
`TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Certificate`.

## Main definitions

All declarations are in the namespace `TauCeti`.

* `bingsHouseTriangles`: the thirty-one triangles, listed by `bingsHouseTriangles_def`.
* `bingsHouse`: the triangulated Bing's house.

## Main results

* `not_isFreePair_bingsHouse`: Bing's house has no free face.
* `not_collapsible_bingsHouse`: Bing's house is not collapsible.
* `exists_collapsible_collapsesTo_bingsHouse`: Bing's house is a collapse of a collapsible
  complex.
* `contractibleSpace_realization_bingsHouse`: its realization is contractible.
* `contractible2Complex_bingsHouse`: it is a contractible 2-complex.

## References

* R. H. Bing, *Some aspects of the topology of 3-manifolds related to the Poincaré conjecture*,
  Lectures on Modern Mathematics II (1964), 93–128.
* A. Hatcher, *Algebraic Topology* (2002), Chapter 0 (the house with two rooms).
* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology* (1972),
  Chapter 3 (simplicial collapse).
-/

public section

open PreAbstractSimplicialComplex AbstractSimplicialComplex TauCeti.PreAbstractSimplicialComplex

namespace TauCeti

/-- The thirty-one triangles of the eleven-vertex Bing's house. -/
-- A list rather than a finset, so that the kernel checks below run along its entries.
def bingsHouseTriangles : List (Finset (Fin 11)) :=
  [{0, 1, 3}, {0, 1, 4}, {0, 1, 5}, {0, 2, 3}, {0, 2, 4}, {0, 4, 5}, {1, 2, 7}, {1, 2, 9},
   {1, 3, 5}, {1, 3, 6}, {1, 4, 7}, {1, 5, 6}, {1, 6, 9}, {2, 3, 9}, {2, 4, 5}, {2, 5, 7},
   {3, 4, 7}, {3, 4, 8}, {3, 5, 9}, {3, 6, 8}, {3, 7, 10}, {3, 9, 10}, {4, 5, 6}, {4, 6, 9},
   {4, 8, 9}, {5, 7, 9}, {6, 8, 10}, {6, 9, 10}, {7, 8, 9}, {7, 8, 10}, {8, 9, 10}]

/-- The explicit list of the triangles of Bing's house. -/
theorem bingsHouseTriangles_def : bingsHouseTriangles =
      [{0, 1, 3}, {0, 1, 4}, {0, 1, 5}, {0, 2, 3}, {0, 2, 4}, {0, 4, 5}, {1, 2, 7}, {1, 2, 9},
       {1, 3, 5}, {1, 3, 6}, {1, 4, 7}, {1, 5, 6}, {1, 6, 9}, {2, 3, 9}, {2, 4, 5}, {2, 5, 7},
       {3, 4, 7}, {3, 4, 8}, {3, 5, 9}, {3, 6, 8}, {3, 7, 10}, {3, 9, 10}, {4, 5, 6}, {4, 6, 9},
       {4, 8, 9}, {5, 7, 9}, {6, 8, 10}, {6, 9, 10}, {7, 8, 9}, {7, 8, 10}, {8, 9, 10}] :=
  (rfl)

/-- **Bing's house** with two rooms, triangulated with eleven vertices: its faces are the nonempty
subsets of the triangles in `bingsHouseTriangles`. -/
def bingsHouse : AbstractSimplicialComplex (Fin 11) :=
  AbstractSimplicialComplex.ofGenerators {t | t ∈ bingsHouseTriangles} (by decide)

/-- The faces of Bing's house are the nonempty subsets of its triangles. -/
@[simp]
theorem mem_bingsHouse {σ : Finset (Fin 11)} :
    σ ∈ bingsHouse ↔ σ.Nonempty ∧ ∃ t ∈ bingsHouseTriangles, σ ⊆ t := by
  simp [bingsHouse]

/-- The triangles of Bing's house have three vertices. -/
theorem card_of_mem_bingsHouseTriangles {t : Finset (Fin 11)} (ht : t ∈ bingsHouseTriangles) :
    t.card = 3 := by
  have h : bingsHouseTriangles.all (·.card == 3) = true := by decide +kernel
  exact beq_iff_eq.mp (List.all_eq_true.mp h t ht)

/-- Each triangle of Bing's house is a face. -/
theorem mem_bingsHouse_of_mem_bingsHouseTriangles {t : Finset (Fin 11)}
    (ht : t ∈ bingsHouseTriangles) : t ∈ bingsHouse :=
  AbstractSimplicialComplex.mem_ofGenerators_of_mem ht
    (Finset.card_pos.mp (by rw [card_of_mem_bingsHouseTriangles ht]; decide))

/-- Bing's house has finitely many faces. -/
theorem finite_faces_bingsHouse : bingsHouse.faces.Finite :=
  Set.toFinite _

/-- Bing's house is two-dimensional. -/
theorem dimension_bingsHouse : dimension bingsHouse = 2 :=
  AbstractSimplicialComplex.dimension_ofGenerators
    (fun _ ht => card_of_mem_bingsHouseTriangles ht) ⟨{0, 1, 3}, by decide⟩

/-- **Bing's house has no free face.** Every edge of a triangle lies in a second triangle. -/
theorem not_isFreePair_bingsHouse (σ τ : Finset (Fin 11)) :
    ¬ IsFreePair bingsHouse.toPreAbstractSimplicialComplex σ τ := by
  -- Boolean list checks keep the kernel from enumerating all subsets of `Fin 11`.
  have h : bingsHouseTriangles.all (fun t => decide (∀ a ∈ t,
      bingsHouseTriangles.any fun t' => t' != t && decide (t.erase a ⊂ t'))) = true := by
    decide +kernel
  have hT : ∀ t ∈ bingsHouseTriangles, ∀ a ∈ t,
      ∃ t' ∈ bingsHouseTriangles, t' ≠ t ∧ t.erase a ⊂ t' := by
    simpa only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      bne_iff_ne] using h
  rw [bingsHouse, AbstractSimplicialComplex.toPreAbstractSimplicialComplex_ofGenerators]
  exact not_isFreePair_of_forall_erase_ssubset (T := {t | t ∈ bingsHouseTriangles})
    hT σ τ

/-- **Bing's house is not collapsible**: it has no free face to start a collapse. -/
theorem not_collapsible_bingsHouse :
    ¬ PreAbstractSimplicialComplex.Collapsible bingsHouse.toPreAbstractSimplicialComplex := by
  exact not_collapsible_of_forall_not_isFreePair not_isFreePair_bingsHouse
    (mem_bingsHouse_of_mem_bingsHouseTriangles (t := {0, 1, 3}) (by decide)) (by decide)

/-- Bit masks of the twenty-three tetrahedra of a three-dimensional complex containing Bing's
house, with the vertex `v` encoded as bit `v`. -/
private def bingsHouseBallMasks : List ℕ :=
  [43, 45, 51, 53, 106, 114, 120, 150, 180, 184, 344, 408, 556, 594, 646, 658, 676, 680, 848, 912,
   1672, 1856, 1920]

/-- A certificate collapsing the complex of `bingsHouseBallMasks` onto Bing's house, as steps of
`checkMaskSteps`. -/
private def bingsHouseBallCollapse : List (ℕ × ℕ) :=
  [(22, 7), (392, 4), (400, 9), (656, 1), (642, 2), (644, 5), (148, 5), (176, 3), (530, 6),
   (168, 9), (56, 6), (648, 10), (1664, 8), (548, 3), (44, 0), (82, 5), (37, 4), (50, 0), (104, 1),
   (41, 1), (88, 8), (336, 9), (832, 10)]

/-- A certificate collapsing the complex of `bingsHouseBallMasks` to the vertex `10`, as steps of
`checkMaskCollapse`. -/
private def bingsHouseBallContraction : List (ℕ × ℕ) :=
  [(74, 5), (328, 4), (98, 4), (22, 7), (1600, 8), (50, 0), (49, 2), (524, 5), (148, 5), (134, 9),
   (552, 7), (1088, 8), (1544, 7), (42, 0), (104, 4), (520, 7), (41, 2), (832, 4), (82, 9), (34, 0),
   (176, 3), (644, 5), (132, 5), (642, 4), (280, 7), (656, 8), (1792, 7), (72, 4), (96, 4),
   (320, 4), (130, 4), (1536, 7), (66, 9), (1280, 7), (10, 0), (80, 9), (1032, 7), (9, 2), (12, 5),
   (33, 2), (5, 4), (6, 9), (64, 9), (514, 4), (516, 5), (544, 7), (36, 4), (18, 0), (160, 3),
   (640, 8), (48, 3), (264, 7), (768, 4), (24, 7), (144, 8), (512, 4), (32, 3), (8, 7), (2, 0),
   (4, 4), (1, 4), (16, 8), (256, 7), (128, 10)]

/-- The masks left by `bingsHouseBallCollapse` generate Bing's house. -/
private theorem ofMasks_deleteMaskSteps_bingsHouseBallCollapse :
    ofMasks 11 (deleteMaskSteps 11 bingsHouseBallMasks bingsHouseBallCollapse) =
      bingsHouse.toPreAbstractSimplicialComplex := by
  -- Boolean list checks keep the kernel from enumerating all subsets of `Fin 11`.
  have hfwd : bingsHouseTriangles.all (fun t =>
      (deleteMaskSteps 11 bingsHouseBallMasks bingsHouseBallCollapse).any
        fun g => decide (t ⊆ maskFace 11 g)) = true := by
    decide +kernel
  have hbwd : (deleteMaskSteps 11 bingsHouseBallMasks bingsHouseBallCollapse).all (fun g =>
      bingsHouseTriangles.any fun t => decide (maskFace 11 g ⊆ t)) = true := by
    decide +kernel
  simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hfwd hbwd
  apply SetLike.ext
  intro σ
  rw [mem_ofMasks]
  constructor
  · rintro ⟨hne, g, hg, hσg⟩
    obtain ⟨t, ht, hgt⟩ := hbwd g hg
    exact mem_bingsHouse.mpr ⟨hne, t, ht, hσg.trans hgt⟩
  · intro hσ
    obtain ⟨hne, t, ht, hσt⟩ := mem_bingsHouse.mp hσ
    obtain ⟨g, hg, htg⟩ := hfwd t ht
    exact ⟨hne, g, hg, hσt.trans htg⟩

/-- **Bing's house is a collapse of a collapsible complex**, although it is not itself
collapsible. -/
theorem exists_collapsible_collapsesTo_bingsHouse :
    ∃ K : PreAbstractSimplicialComplex (Fin 11), PreAbstractSimplicialComplex.Collapsible K ∧
      CollapsesTo K bingsHouse.toPreAbstractSimplicialComplex :=
  ⟨ofMasks 11 bingsHouseBallMasks,
    collapsible_ofMasks_of_checkMaskCollapse (steps := bingsHouseBallContraction) (v := 10)
      (by decide +kernel),
    ofMasks_deleteMaskSteps_bingsHouseBallCollapse ▸
      collapsesTo_ofMasks_of_checkMaskSteps (by decide +kernel)⟩

/-- **Bing's house is contractible.** It is a collapse of a collapsible complex, whose
contractible realization strongly deformation retracts onto it. -/
theorem contractibleSpace_realization_bingsHouse : ContractibleSpace (Realization bingsHouse) :=
  let ⟨_, hK, h⟩ := exists_collapsible_collapsesTo_bingsHouse
  h.contractibleSpace_realization hK

/-- Bing's house is a contractible 2-complex in the sense of Zeeman's conjecture. -/
theorem contractible2Complex_bingsHouse : Contractible2Complex bingsHouse :=
  contractible2Complex_iff.mpr
    ⟨finite_faces_bingsHouse, dimension_bingsHouse.le, contractibleSpace_realization_bingsHouse⟩

end TauCeti
