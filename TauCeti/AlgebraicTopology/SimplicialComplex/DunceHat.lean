/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Zeeman
public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Certificate
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Product.Cylinder
import Mathlib.Data.Finset.Grade

/-!
# The dunce hat

The dunce hat is the quotient of a triangle in which the three sides are identified by the word
`a a a⁻¹`. It is contractible, but it has no free face in any triangulation, so no triangulation
of it is collapsible; this file proves this for an explicit triangulation. Zeeman showed that its
cylinder is nevertheless collapsible, the first nontrivial instance of Zeeman's collapsibility
conjecture.

This file triangulates the dunce hat by an abstract simplicial complex on `Fin 8` with seventeen
triangles. Vertex `0` is the image of the three corners of the triangle, vertices `1` and `2`
divide the identified side into thirds, and vertices `3` to `7` lie in the interior. Every edge
on the identified side lies in three triangles and every interior edge in two, so there is no free
face. The staircase cylinder of this triangulation is shown to be collapsible by an explicit
sequence of `131` elementary collapses, checked with the bit-mask certificates of
`TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Certificate`. Since the cylinder also
realizes to the product of the dunce hat with the unit interval, this proves contractibility.

## Main definitions

All declarations are in the namespace `TauCeti`.

* `dunceHatTriangles`: the seventeen triangles, listed by `dunceHatTriangles_def`.
* `dunceHat`: the triangulated dunce hat.

## Main results

* `not_isFreePair_dunceHat`: the dunce hat has no free face.
* `not_collapsible_dunceHat`: the dunce hat is not collapsible.
* `collapsible_orderedCylinder_dunceHat`: its ordered cylinder is collapsible.
* `contractibleSpace_realization_dunceHat`: its realization is contractible.
* `contractible2Complex_dunceHat`: it is a contractible 2-complex.
* `hasCollapsibleTriangulation_orderedCylinder_dunceHat`: the conclusion of Zeeman's conjecture
  holds for the dunce hat.

## References

* E. C. Zeeman, *On the dunce hat*, Topology 2 (1964), 341–358.
* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology* (1972),
  Chapter 3 (simplicial collapse).
-/

public section

open PreAbstractSimplicialComplex AbstractSimplicialComplex TauCeti.PreAbstractSimplicialComplex

namespace TauCeti

/-- The seventeen triangles of the eight-vertex dunce hat. Vertex `0` is the common image of the
corners of the triangle, `1` and `2` divide the identified side, and `3` to `7` are interior. -/
def dunceHatTriangles : Finset (Finset (Fin 8)) :=
  {{0, 1, 3}, {0, 1, 4}, {0, 1, 7}, {0, 2, 4}, {0, 2, 5}, {0, 2, 6}, {0, 3, 7}, {0, 5, 6},
    {1, 2, 3}, {1, 2, 5}, {1, 2, 6}, {1, 4, 5}, {1, 6, 7}, {2, 3, 4}, {3, 4, 5}, {3, 5, 6},
    {3, 6, 7}}

/-- The explicit list of the triangles of the dunce hat. -/
theorem dunceHatTriangles_def : dunceHatTriangles =
    {{0, 1, 3}, {0, 1, 4}, {0, 1, 7}, {0, 2, 4}, {0, 2, 5}, {0, 2, 6}, {0, 3, 7}, {0, 5, 6},
      {1, 2, 3}, {1, 2, 5}, {1, 2, 6}, {1, 4, 5}, {1, 6, 7}, {2, 3, 4}, {3, 4, 5}, {3, 5, 6},
      {3, 6, 7}} :=
  (rfl)

/-- The **dunce hat**, triangulated with eight vertices: its faces are the nonempty subsets of the
triangles in `dunceHatTriangles`. -/
def dunceHat : AbstractSimplicialComplex (Fin 8) where
  faces := {σ | σ.Nonempty ∧ ∃ t ∈ dunceHatTriangles, σ ⊆ t}
  isRelLowerSet_faces := by
    rintro σ ⟨hσ, t, ht, hσt⟩
    exact ⟨hσ, fun τ hτσ hτ => ⟨hτ, t, ht, hτσ.trans hσt⟩⟩
  singleton_mem v := ⟨Finset.singleton_nonempty v, by
    simpa only [Finset.singleton_subset_iff] using
      (by decide : ∀ v : Fin 8, ∃ t ∈ dunceHatTriangles, v ∈ t) v⟩

/-- The faces of the dunce hat are the nonempty subsets of its triangles. -/
@[simp]
theorem mem_dunceHat {σ : Finset (Fin 8)} :
    σ ∈ dunceHat ↔ σ.Nonempty ∧ ∃ t ∈ dunceHatTriangles, σ ⊆ t :=
  Iff.rfl

/-- Each triangle of the dunce hat is a face. -/
theorem mem_dunceHat_of_mem_dunceHatTriangles {t : Finset (Fin 8)} (ht : t ∈ dunceHatTriangles) :
    t ∈ dunceHat :=
  ⟨Finset.nonempty_iff_ne_empty.mpr (by rintro rfl; revert ht; decide), t, ht, subset_rfl⟩

/-- The triangles of the dunce hat have three vertices. -/
theorem card_of_mem_dunceHatTriangles {t : Finset (Fin 8)} (ht : t ∈ dunceHatTriangles) :
    t.card = 3 := by
  revert t
  decide +kernel

/-- Every edge of a triangle of the dunce hat lies in a second triangle. -/
private theorem exists_ne_mem_dunceHatTriangles {t e : Finset (Fin 8)}
    (ht : t ∈ dunceHatTriangles) (he : e ⊆ t) (hcard : e.card = 2) :
    ∃ t' ∈ dunceHatTriangles, t' ≠ t ∧ e ⊆ t' := by
  have key : ∀ t ∈ dunceHatTriangles, ∀ e ∈ t.powersetCard 2,
      ∃ t' ∈ dunceHatTriangles, t' ≠ t ∧ e ⊆ t' := by decide +kernel
  exact key t ht e (Finset.mem_powersetCard.mpr ⟨he, hcard⟩)

/-- The dunce hat has finitely many faces. -/
theorem finite_faces_dunceHat : dunceHat.faces.Finite :=
  Set.toFinite _

/-- The dunce hat is two-dimensional. -/
theorem dimension_dunceHat : dimension dunceHat = 2 := by
  refine le_antisymm (AbstractSimplicialComplex.dimension_le_iff.mpr fun σ hσ => ?_) ?_
  · obtain ⟨-, t, ht, hσt⟩ := mem_dunceHat.mp hσ
    have := Finset.card_le_card hσt
    rw [card_of_mem_dunceHatTriangles ht] at this
    exact_mod_cast (by omega : σ.card - 1 ≤ 2)
  · have ht : ({0, 1, 3} : Finset (Fin 8)) ∈ dunceHatTriangles := by decide
    simpa [card_of_mem_dunceHatTriangles ht] using
      AbstractSimplicialComplex.le_dimension (mem_dunceHat_of_mem_dunceHatTriangles ht)

/-- **The dunce hat has no free face.** Every edge lies in at least two triangles, and the
triangles are its maximal faces. -/
theorem not_isFreePair_dunceHat (σ τ : Finset (Fin 8)) :
    ¬ IsFreePair dunceHat.toPreAbstractSimplicialComplex σ τ := by
  intro h
  obtain ⟨-, t, ht, hτt⟩ := mem_dunceHat.mp h.upper_mem
  have htτ : t = τ := h.upper_maximal (mem_dunceHat_of_mem_dunceHatTriangles ht) hτt
  subst htτ
  obtain ⟨a, haσ, hins⟩ := Finset.covBy_iff_exists_insert.mp h.covBy
  have hσcard : σ.card = 2 := by
    have := Finset.card_insert_of_notMem haσ
    rw [hins, card_of_mem_dunceHatTriangles ht] at this
    omega
  obtain ⟨t', ht', hne, hσt'⟩ :=
    exists_ne_mem_dunceHatTriangles ht h.lower_ssubset_upper.subset hσcard
  rcases h.eq_lower_or_eq_upper (mem_dunceHat_of_mem_dunceHatTriangles ht') hσt' with rfl | rfl
  · rw [card_of_mem_dunceHatTriangles ht'] at hσcard
    exact absurd hσcard (by decide)
  · exact hne rfl

/-- **The dunce hat is not collapsible**: it has no free face to start a collapse. -/
theorem not_collapsible_dunceHat :
    ¬ PreAbstractSimplicialComplex.Collapsible dunceHat.toPreAbstractSimplicialComplex := by
  intro hcol
  obtain ⟨v, h⟩ := hcol.exists_eq_point_of_forall_not_isFreePair not_isFreePair_dunceHat
  have hmem : ({0, 1} : Finset (Fin 8)) ∈ dunceHat.toPreAbstractSimplicialComplex :=
    mem_dunceHat.mpr ⟨by decide, {0, 1, 3}, by decide, by decide⟩
  rw [h, mem_point] at hmem
  have := congrArg Finset.card hmem
  simp at this

/-- Bit masks of the fifty-one staircase tetrahedra of the ordered cylinder on the dunce hat, with
the vertex `(v, i)` encoded as bit `i + 2 * v`. -/
private def dunceHatCylinderMasks : List ℕ :=
  [139, 141, 172, 180, 197, 212, 523, 525, 547, 561, 688, 720, 773, 785, 848, 2083, 2092, 2097,
   2100, 2572, 2752, 2820, 2880, 3089, 3092, 3332, 3392, 8227, 8236, 8241, 8244, 10243, 10432,
   11265, 11328, 12305, 12308, 13313, 13376, 32779, 32781, 32899, 32961, 40972, 41152, 45060,
   45120, 49157, 49217, 53252, 53312]

/-- A certificate collapsing the ordered cylinder on the dunce hat, as steps of
`checkMaskCollapse`. -/
private def dunceHatCylinderCollapse : List (ℕ × ℕ) :=
  [(168, 2), (1044, 11), (546, 0), (2688, 6), (20544, 15), (672, 4), (49216, 0), (1344, 11),
   (3136, 13), (164, 4), (2368, 9), (8226, 0), (560, 0), (35, 11), (273, 9), (36928, 13),
   (5184, 13), (3328, 2), (49153, 2), (336, 9), (522, 0), (2308, 9), (32773, 3), (84, 7), (592, 7),
   (41024, 7), (53248, 2), (521, 2), (2051, 13), (11264, 0), (524, 11), (2060, 5), (32960, 0),
   (1041, 11), (10304, 7), (261, 9), (13312, 0), (2065, 5), (8232, 2), (32777, 1), (2096, 2),
   (32771, 7), (52, 13), (4113, 13), (13, 7), (8204, 15), (131, 3), (8209, 5), (40964, 12),
   (8212, 12), (69, 7), (257, 9), (1280, 2), (272, 9), (16448, 0), (34, 11), (4160, 13), (520, 11),
   (16385, 2), (544, 0), (49152, 2), (2304, 9), (16388, 12), (1028, 11), (320, 9), (32832, 0),
   (2050, 13), (768, 2), (80, 7), (1088, 13), (9216, 0), (68, 7), (8200, 15), (1040, 11), (65, 7),
   (3072, 0), (8256, 7), (2064, 2), (160, 4), (5120, 0), (514, 0), (2056, 5), (40, 2), (8194, 0),
   (3, 3), (9, 7), (4097, 13), (32769, 7), (129, 2), (5, 9), (516, 11), (2560, 6), (513, 4),
   (576, 7), (640, 4), (144, 2), (2052, 5), (2112, 7), (132, 3), (36, 13), (2080, 0), (2049, 13),
   (10240, 7), (8196, 12), (8193, 5), (17, 5), (48, 13), (8320, 15), (136, 1), (10, 15), (130, 15),
   (20, 12), (8208, 12), (4100, 15), (12288, 15), (12, 15), (8, 15), (2, 15), (2048, 7),
   (16384, 12), (512, 4), (64, 7), (16, 12), (256, 2), (4096, 15), (1024, 0), (128, 15), (4, 15),
   (1, 5), (32, 13), (32768, 13)]

/-- The encoded ordered cylinder on the dunce hat is generated by `dunceHatCylinderMasks`. -/
private theorem map_orderedCylinder_dunceHat :
    dunceHat.orderedCylinder.toPreAbstractSimplicialComplex.map (finProdFinEquiv : _ ≃ Fin 16) =
      ofMasks 16 dunceHatCylinderMasks := by
  have hfwd : ∀ t ∈ dunceHatTriangles, ∀ k ∈ t, ∃ g ∈ dunceHatCylinderMasks,
      (t.cylinderStaircase k).image (finProdFinEquiv : _ ≃ Fin 16) = maskFace 16 g := by
    decide +kernel
  have hbwd : ∀ g ∈ dunceHatCylinderMasks, ∃ t ∈ dunceHatTriangles, ∃ k ∈ t,
      maskFace 16 g = (t.cylinderStaircase k).image (finProdFinEquiv : _ ≃ Fin 16) := by
    decide +kernel
  apply SetLike.ext
  intro σ
  rw [mem_map_iff, mem_ofMasks]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨hne, V, hV, k, hk, hτV⟩ :=
      mem_orderedCylinder_iff_exists_subset_cylinderStaircase.mp hτ
    obtain ⟨-, t, ht, hVt⟩ := mem_dunceHat.mp hV
    obtain ⟨g, hg, hgt⟩ := hfwd t ht k (hVt hk)
    exact ⟨hne.image _, g, hg, hgt ▸ Finset.image_subset_image
      (hτV.trans (Finset.cylinderStaircase_mono hVt k))⟩
  · rintro ⟨hne, g, hg, hσg⟩
    obtain ⟨t, ht, k, hk, hgt⟩ := hbwd g hg
    obtain ⟨τ, hτt, rfl⟩ := Finset.subset_image_iff.mp (hgt ▸ hσg)
    exact ⟨τ, mem_orderedCylinder_iff_exists_subset_cylinderStaircase.mpr
      ⟨Finset.image_nonempty.mp hne, t, mem_dunceHat_of_mem_dunceHatTriangles ht, k, hk, hτt⟩,
      rfl⟩

/-- **Zeeman's theorem for the dunce hat**: the ordered (staircase) cylinder on this
triangulation of the dunce hat is collapsible, although the dunce hat itself is not. -/
theorem collapsible_orderedCylinder_dunceHat :
    PreAbstractSimplicialComplex.Collapsible
      dunceHat.orderedCylinder.toPreAbstractSimplicialComplex := by
  rw [← Collapsible.map_equiv_iff (finProdFinEquiv : _ ≃ Fin 16), map_orderedCylinder_dunceHat]
  exact collapsible_ofMasks_of_checkMaskCollapse (steps := dunceHatCylinderCollapse) (v := 13)
    (by decide +kernel)

/-- **The dunce hat is contractible.** Its ordered cylinder is collapsible, hence has contractible
realization, and that realization is homeomorphic to the product of the dunce hat with the unit
interval. -/
theorem contractibleSpace_realization_dunceHat : ContractibleSpace (Realization dunceHat) :=
  contractibleSpace_realization_of_collapsible_orderedCylinder dunceHat finite_faces_dunceHat
    collapsible_orderedCylinder_dunceHat

/-- The dunce hat is a contractible 2-complex in the sense of Zeeman's conjecture. -/
theorem contractible2Complex_dunceHat : Contractible2Complex dunceHat :=
  contractible2Complex_iff.mpr
    ⟨finite_faces_dunceHat, dimension_dunceHat.le, contractibleSpace_realization_dunceHat⟩

/-- Collapsibility is strictly stronger than contractibility, even for finite two-dimensional
complexes: the dunce hat is a contractible 2-complex that is not collapsible. -/
theorem exists_contractible2Complex_not_collapsible :
    ∃ K : AbstractSimplicialComplex (Fin 8), Contractible2Complex K ∧
      ¬ PreAbstractSimplicialComplex.Collapsible K.toPreAbstractSimplicialComplex :=
  ⟨dunceHat, contractible2Complex_dunceHat, not_collapsible_dunceHat⟩

/-- The conclusion of **Zeeman's conjecture** holds for the dunce hat, already for its staircase
triangulation of the cylinder. -/
theorem hasCollapsibleTriangulation_orderedCylinder_dunceHat :
    PreAbstractSimplicialComplex.HasCollapsibleTriangulation.{0}
      dunceHat.orderedCylinder.toPreAbstractSimplicialComplex :=
  collapsible_orderedCylinder_dunceHat.hasCollapsibleTriangulation

end TauCeti
