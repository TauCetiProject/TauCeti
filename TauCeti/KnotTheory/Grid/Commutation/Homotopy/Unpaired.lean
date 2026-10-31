/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Recut
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.SameSideRecut

/-!
# Off-diagonal unpaired hexagon composites have a mixed-side overlap

On the left-hand side `∂ ∘ H + H ∘ ∂` of the homotopy equation of a column commutation, a counted
hexagon composite whose two rectangles share exactly one side column cancels against its recut
whenever that recut is again a counted composite (`Homotopy.Recut`). This file shows that this
always happens when the shared column is initial for both rectangles or terminal for both.
Consequently, off the diagonal, every unpaired composite has a mixed-side overlap.

The argument has two independent parts.

* *Markings.* A counted composite covers exactly one `X`-marking, that of the column its hexagon
  cuts away. If a repartition of its domain into two empty rectangles has a piece with the shape of
  a commutation hexagon, that piece covers the `X`-marking of its own cut-away column, which must
  therefore be the single one. Its hexagon carries no `X`-marking, the other piece carries none
  either, and the repartition is a counted composite
  (`GridDiagram.exists_toRectangleDecomposition_eq_of_isRepartition`).
* *Shapes.* For a same-side overlap, the recut cuts the L-shaped union the other way, and one of
  its pieces again underlies a commutation hexagon of the same kind
  (`GridHexagonCompositeDecomposition.exists_hexagon_of_isRecut`).

## Main results

* `TauCeti.GridDiagram.exists_toRectangleDecomposition_eq_of_isRepartition`: a repartition of a
  counted composite into empty rectangles, one of which underlies a commutation hexagon, underlies
  a counted composite.
* `TauCeti.GridDiagram.exists_isRecut_of_hasSameSideOverlap`: the recut of a counted composite
  with a same-side overlap underlies a counted composite.
* `TauCeti.GridDiagram.hasMixedSideOverlap_of_mem_unpairedHexagonComposites`: off the diagonal,
  every unpaired composite has a mixed-side overlap.

## References

This is the same-side case of the hexagon--rectangle juxtaposition argument of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1,
Proposition 3.2 (arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Promoting a repartition to a counted composite -/

/-- Every `X`-marking covered by a counted composite is one and the same. -/
private theorem exists_eq_of_mem_XSet_of_mem_coveredSquares_union {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.hexagonCompositeDecompositions C x z) :
    ∃ c : Fin n, ∀ p ∈ G.XSet,
      p ∈ F.toRectangleDecomposition.first.toGridRectangle.coveredSquares ∪
          F.toRectangleDecomposition.second.toGridRectangle.coveredSquares →
        p = (c, G.X c) := by
  have hhex {u v : GridState n}
      {P : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow u v}
      (hP : P ∈ G.commutationHexagons C u v) {p : Fin n × Fin n} (hX : p ∈ G.XSet)
      (hp : p ∈ P.toGridRectangleBetween.toGridRectangle.coveredSquares) :
      p = (P.cutColumn, G.X P.cutColumn) := by
    have hmem := Finset.mem_inter.mpr ⟨hX, hp⟩
    rw [G.XSet_inter_coveredSquares_of_mem_commutationHexagons C hP] at hmem
    exact Finset.mem_singleton.mp hmem
  cases F with
  | inl F =>
    obtain ⟨hP, hr⟩ := (G.mem_hexagonRectangleDecompositions C F).mp
      ((G.inl_mem_hexagonCompositeDecompositions C F).mp hF)
    refine ⟨F.hexagon.cutColumn, fun p hX hp => ?_⟩
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hhex hP hX hp
    · exact (Finset.disjoint_left.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr) hp hX).elim
  | inr F =>
    obtain ⟨hr, hP⟩ := (G.mem_rectangleHexagonDecompositions C F).mp
      ((G.inr_mem_hexagonCompositeDecompositions C F).mp hF)
    refine ⟨F.hexagon.cutColumn, fun p hX hp => ?_⟩
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.disjoint_left.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr) hp hX).elim
    · exact hhex hP hX hp

/-- A commutation hexagon whose underlying rectangle lies in a domain covering at most one
`X`-marking carries no `X`-marking, and its underlying rectangle covers that one. -/
private theorem disjoint_XSet_and_mem_of_coveredSquares_subset {u v : GridState n}
    (P : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow u v)
    {S : Finset (Fin n × Fin n)} {c : Fin n} (hc : ∀ p ∈ G.XSet, p ∈ S → p = (c, G.X c))
    (hsub : P.toGridRectangleBetween.toGridRectangle.coveredSquares ⊆ S) :
    Disjoint P.coveredSquares G.XSet ∧
      (c, G.X c) ∈ P.toGridRectangleBetween.toGridRectangle.coveredSquares := by
  have hcut := G.cutColumn_X_mem_toGridRectangle_coveredSquares C P
  have heq := hc _ ((G.mk_mem_XSet _ _).mpr rfl) (hsub hcut)
  refine ⟨Finset.disjoint_left.mpr fun {p} hp hX => ?_, heq ▸ hcut⟩
  obtain ⟨d, r⟩ := p
  -- A covered square lies outside both columns next to the replaced line, so in the rectangle.
  have hda : d ≠ a := fun h => P.mk_notMem_coveredSquares_left_column r (h ▸ hp)
  have hdb : d ≠ b := fun h => P.mk_notMem_coveredSquares_right_column r (h ▸ hp)
  have hrect := (P.mem_coveredSquares_iff_of_ne hda hdb).mp hp
  have hcol : d = P.cutColumn := (Prod.mk.inj ((hc _ hX (hsub hrect)).trans heq.symm)).1
  cases P with
  | inl P => exact hda (by rwa [GridCommutationHexagonBetween.cutColumn_inl] at hcol)
  | inr P => exact hdb (by rwa [GridCommutationHexagonBetween.cutColumn_inr] at hcol)

/-- A repartition of a counted composite into two empty rectangles, one of which underlies a
commutation hexagon, is the underlying rectangle decomposition of a counted composite. -/
theorem exists_toRectangleDecomposition_eq_of_isRepartition {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.hexagonCompositeDecompositions C x z) {E : GridRectangleDecomposition x z}
    (hrep : F.toRectangleDecomposition.IsRepartition E) (hfirst : E.first.IsEmpty)
    (hsecond : E.second.IsEmpty)
    (hhex : (∃ P : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow x E.middle,
        P.toGridRectangleBetween = E.first) ∨
      ∃ P : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow E.middle z,
        P.toGridRectangleBetween = E.second) :
    ∃ F' ∈ G.hexagonCompositeDecompositions C x z, F'.toRectangleDecomposition = E := by
  obtain ⟨c, hc⟩ := G.exists_eq_of_mem_XSet_of_mem_coveredSquares_union C hF
  rw [← hrep.coveredSquares_union_eq] at hc
  -- The piece without the hexagon misses the single `X`-marking, which the hexagon piece covers.
  have hdisj := Finset.disjoint_left.mp hrep.disjoint_coveredSquares_right
  rcases hhex with ⟨P, hP⟩ | ⟨P, hP⟩
  · obtain ⟨hPX, hcP⟩ := G.disjoint_XSet_and_mem_of_coveredSquares_subset C P hc
      (hP ▸ Finset.subset_union_left)
    refine ⟨Sum.inl ⟨E.middle, P, E.second⟩, ?_, ?_⟩
    · simp only [inl_mem_hexagonCompositeDecompositions, mem_hexagonRectangleDecompositions,
        mem_commutationHexagons, mem_unblockedRectangles]
      refine ⟨⟨hP ▸ hfirst, hPX⟩, hsecond, Finset.disjoint_left.mpr fun {p} hp hX => ?_⟩
      obtain rfl := hc p hX (Finset.mem_union_right _ hp)
      exact hdisj (hP ▸ hcP) hp
    · simp only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
        GridHexagonRectangleDecomposition.toRectangleDecomposition, hP]
  · obtain ⟨hPX, hcP⟩ := G.disjoint_XSet_and_mem_of_coveredSquares_subset C P hc
      (hP ▸ Finset.subset_union_right)
    refine ⟨Sum.inr ⟨E.middle, E.first, P⟩, ?_, ?_⟩
    · simp only [inr_mem_hexagonCompositeDecompositions, mem_rectangleHexagonDecompositions,
        mem_commutationHexagons, mem_unblockedRectangles]
      refine ⟨⟨hfirst, Finset.disjoint_left.mpr fun {p} hp hX => ?_⟩, hP ▸ hsecond, hPX⟩
      obtain rfl := hc p hX (Finset.mem_union_left _ hp)
      exact hdisj hp (hP ▸ hcP)
    · simp only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
        GridRectangleHexagonDecomposition.toRectangleDecomposition, hP]

/-! ### Same-side composites are paired -/

/-- The recut of a counted composite whose two rectangles share a side column with the same
orientation, initial for both or terminal for both, is the underlying rectangle decomposition of a
counted composite. -/
theorem exists_isRecut_of_hasSameSideOverlap {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.hexagonCompositeDecompositions C x z)
    (hsame : F.toRectangleDecomposition.HasSameSideOverlap) :
    ∃ F' ∈ G.hexagonCompositeDecompositions C x z,
      F.toRectangleDecomposition.IsRecut F'.toRectangleDecomposition := by
  obtain ⟨hfirst, hsecond⟩ := G.isEmpty_of_mem_hexagonCompositeDecompositions C hF
  have hrecut := F.toRectangleDecomposition.isRecut_recut
    (F.toRectangleDecomposition.hasSameSideOverlap_iff.mp hsame).1 hfirst hsecond
  obtain ⟨F', hF', hF'E⟩ := G.exists_toRectangleDecomposition_eq_of_isRepartition C hF
    hrecut.isRepartition hrecut.isEmpty_first hrecut.isEmpty_second
    (F.exists_hexagon_of_isRecut hsame hfirst hsecond hrecut)
  exact ⟨F', hF', hF'E ▸ hrecut⟩

/-- Off the diagonal, every unpaired hexagon composite has a mixed-side overlap: its two
rectangles share exactly one side column, initial for one and terminal for the other. -/
theorem hasMixedSideOverlap_of_mem_unpairedHexagonComposites {x z : GridState n} (hzx : z ≠ x)
    {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.unpairedHexagonComposites C x z) :
    F.toRectangleDecomposition.HasMixedSideOverlap := by
  obtain ⟨hF, hdisj, hnot⟩ := (G.mem_unpairedHexagonComposites C F).mp hF
  refine ((F.toRectangleDecomposition
    |>.not_hasDisjointSides_iff_sameSideOverlap_or_mixedSideOverlap_of_ne hzx).mp hdisj)
    |>.resolve_left fun hsame => ?_
  obtain ⟨F', hF', hrecut⟩ := G.exists_isRecut_of_hasSameSideOverlap C hF hsame
  exact hnot F' hF' hrecut

end TauCeti.GridDiagram
