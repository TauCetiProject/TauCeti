/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Recut
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.SameSideRecut

/-!
# Off-diagonal unpaired crossing change composites have a mixed-side overlap

Let `C` be a column turn at the columns `a` and `b = finRotate n a` of a grid diagram `G`, turning
in row `s`, and let `t` be a second row such that the annulus squares
`GridDiagram.crossingChangeAnnulusSquares C t` carry no `X`-marking, as for the crossing change
maps of interleaving columns. On the left-hand side `∂ ∘ H + H ∘ ∂` of the crossing change
homotopy equation, a counted composite whose two rectangles share exactly one side column cancels
against its recut whenever that recut is again a counted composite (`Homotopy.Recut`). This file
shows that this always happens when the shared column is initial for both rectangles or terminal
for both. Consequently, off the diagonal, every unpaired composite has a mixed-side overlap, and
only those remain to be matched with the pairs of pentagons counted by `Ψ ∘ Φ`.

The argument has two independent parts.

* *Markings.* A counted composite covers exactly one `X`-marking, that of the column its hexagon
  cuts away. The rectangle under any crossing-change hexagon covers the `X`-marking of its own
  cut-away column, and the hexagon is counted as soon as its rectangle is empty and covers no
  other `X`-marking
  (`GridDiagram.mem_crossingChangeCommutationHexagons_iff_XSet_inter_eq`). So if a repartition of
  the domain of a counted composite into two empty rectangles has a piece underlying a hexagon,
  that hexagon is counted, the other piece carries no `X`-marking, and the repartition is a
  counted composite
  (`GridDiagram.exists_crossingChange_toRectangleDecomposition_eq_of_isRepartition`).
* *Shapes.* For a same-side overlap, one piece of the recut again underlies a hexagon of the same
  kind (`GridHexagonCompositeDecomposition.exists_hexagon_of_isRecut`), exactly as for the
  homotopy of a column commutation.

## Main results

* `TauCeti.GridDiagram.exists_crossingChange_toRectangleDecomposition_eq_of_isRepartition`:
  a repartition of a counted composite into empty rectangles, one of which underlies a hexagon,
  underlies a counted composite.
* `TauCeti.GridDiagram.exists_crossingChange_isRecut_of_hasSameSideOverlap`: the
  recut of a counted composite with a same-side overlap underlies a counted composite.
* `TauCeti.GridDiagram.hasMixedSideOverlap_of_mem_crossingChangeUnpairedHexagonComposites`: off the
  diagonal, every unpaired composite has a mixed-side overlap.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 5.1 and 6.1: the juxtaposition argument for the hexagon
  homotopies of commutation and of a crossing change.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3: the
  homotopy equations for the hexagons with corners at the two turn points.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} {G : GridDiagram n} {C : ColumnTurn n} {t : Fin n}

local notation "a" => C.column

/-! ### Promoting a repartition to a counted composite -/

/-- If the annulus squares carry no `X`-marking, every `X`-marking covered by a counted composite
is one and the same. -/
private theorem exists_eq_of_mem_XSet_of_mem_coveredSquares_union
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z) :
    ∃ c : Fin n, ∀ p ∈ G.XSet,
      p ∈ F.toRectangleDecomposition.first.toGridRectangle.coveredSquares ∪
          F.toRectangleDecomposition.second.toGridRectangle.coveredSquares →
        p = (c, G.X c) := by
  have hhex {u v : GridState n} {P : GridCommutationHexagonBetween a C.turnRow t u v}
      (hP : P ∈ G.crossingChangeCommutationHexagons C t u v) {p : Fin n × Fin n}
      (hXp : p ∈ G.XSet) (hp : p ∈ P.toGridRectangleBetween.toGridRectangle.coveredSquares) :
      p = (P.cutColumn, G.X P.cutColumn) := by
    have hmem := Finset.mem_inter.mpr ⟨hXp, hp⟩
    rw [XSet_inter_coveredSquares_of_mem_crossingChangeCommutationHexagons hX hP] at hmem
    exact Finset.mem_singleton.mp hmem
  cases F with
  | inl F =>
    obtain ⟨hP, hr⟩ := (G.mem_crossingChangeHexagonRectangleDecompositions C t F).mp
      ((G.inl_mem_crossingChangeHexagonCompositeDecompositions C t F).mp hF)
    refine ⟨F.hexagon.cutColumn, fun p hXp hp => ?_⟩
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hhex hP hXp hp
    · exact (Finset.disjoint_left.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr) hp hXp).elim
  | inr F =>
    obtain ⟨hr, hP⟩ := (G.mem_crossingChangeRectangleHexagonDecompositions C t F).mp
      ((G.inr_mem_crossingChangeHexagonCompositeDecompositions C t F).mp hF)
    refine ⟨F.hexagon.cutColumn, fun p hXp hp => ?_⟩
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.disjoint_left.mp (G.disjoint_XSet_of_mem_unblockedRectangles hr) hp hXp).elim
    · exact hhex hP hXp hp

/-- If the annulus squares carry no `X`-marking, a crossing-change hexagon whose empty underlying
rectangle lies in a domain covering at most one `X`-marking is counted, and its underlying
rectangle covers that marking. -/
private theorem mem_and_mem_of_coveredSquares_subset
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {u v : GridState n}
    (P : GridCommutationHexagonBetween a C.turnRow t u v)
    (hempty : P.toGridRectangleBetween.IsEmpty)
    {S : Finset (Fin n × Fin n)} {c : Fin n} (hc : ∀ p ∈ G.XSet, p ∈ S → p = (c, G.X c))
    (hsub : P.toGridRectangleBetween.toGridRectangle.coveredSquares ⊆ S) :
    P ∈ G.crossingChangeCommutationHexagons C t u v ∧
      (c, G.X c) ∈ P.toGridRectangleBetween.toGridRectangle.coveredSquares := by
  have hcut :=
    cutColumn_X_mem_toGridRectangle_coveredSquares_of_disjoint_crossingChangeAnnulusSquares hX P
  have heq := hc _ ((G.mk_mem_XSet _ _).mpr rfl) (hsub hcut)
  refine ⟨(mem_crossingChangeCommutationHexagons_iff_XSet_inter_eq hX P).mpr ⟨hempty, ?_⟩,
    heq ▸ hcut⟩
  ext p
  simp only [Finset.mem_inter, Finset.mem_singleton]
  exact ⟨fun ⟨hXp, hp⟩ => (hc p hXp (hsub hp)).trans heq.symm,
    fun h => h ▸ ⟨(G.mk_mem_XSet _ _).mpr rfl, hcut⟩⟩

/-- If the annulus squares carry no `X`-marking, a repartition of a counted composite into two
empty rectangles, one of which underlies a crossing-change hexagon, is the underlying rectangle
decomposition of a counted composite. -/
theorem exists_crossingChange_toRectangleDecomposition_eq_of_isRepartition
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z)
    {E : GridRectangleDecomposition x z} (hrep : F.toRectangleDecomposition.IsRepartition E)
    (hfirst : E.first.IsEmpty) (hsecond : E.second.IsEmpty)
    (hhex : (∃ P : GridCommutationHexagonBetween a C.turnRow t x E.middle,
        P.toGridRectangleBetween = E.first) ∨
      ∃ P : GridCommutationHexagonBetween a C.turnRow t E.middle z,
        P.toGridRectangleBetween = E.second) :
    ∃ F' ∈ G.crossingChangeHexagonCompositeDecompositions C t x z,
      F'.toRectangleDecomposition = E := by
  obtain ⟨c, hc⟩ := exists_eq_of_mem_XSet_of_mem_coveredSquares_union hX hF
  rw [← hrep.coveredSquares_union_eq] at hc
  -- The piece without the hexagon misses the single `X`-marking, which the hexagon piece covers.
  have hdisj := Finset.disjoint_left.mp hrep.disjoint_coveredSquares_right
  rcases hhex with ⟨P, hP⟩ | ⟨P, hP⟩
  · obtain ⟨hPc, hcP⟩ := mem_and_mem_of_coveredSquares_subset hX P (hP ▸ hfirst) hc
      (hP ▸ Finset.subset_union_left)
    refine ⟨Sum.inl ⟨E.middle, P, E.second⟩, ?_, ?_⟩
    · simp only [inl_mem_crossingChangeHexagonCompositeDecompositions,
        mem_crossingChangeHexagonRectangleDecompositions, mem_unblockedRectangles]
      refine ⟨hPc, hsecond, Finset.disjoint_left.mpr fun {p} hp hXp => ?_⟩
      obtain rfl := hc p hXp (Finset.mem_union_right _ hp)
      exact hdisj (hP ▸ hcP) hp
    · simp only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl,
        GridHexagonRectangleDecomposition.toRectangleDecomposition, hP]
  · obtain ⟨hPc, hcP⟩ := mem_and_mem_of_coveredSquares_subset hX P (hP ▸ hsecond) hc
      (hP ▸ Finset.subset_union_right)
    refine ⟨Sum.inr ⟨E.middle, E.first, P⟩, ?_, ?_⟩
    · simp only [inr_mem_crossingChangeHexagonCompositeDecompositions,
        mem_crossingChangeRectangleHexagonDecompositions, mem_unblockedRectangles]
      refine ⟨⟨hfirst, Finset.disjoint_left.mpr fun {p} hp hXp => ?_⟩, hPc⟩
      obtain rfl := hc p hXp (Finset.mem_union_left _ hp)
      exact hdisj hp (hP ▸ hcP)
    · simp only [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr,
        GridRectangleHexagonDecomposition.toRectangleDecomposition, hP]

/-! ### Same-side composites are paired -/

/-- If the annulus squares carry no `X`-marking, the recut of a counted composite whose two
rectangles share a side column with the same orientation, initial for both or terminal for both,
is the underlying rectangle decomposition of a counted composite. -/
theorem exists_crossingChange_isRecut_of_hasSameSideOverlap
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z)
    (hsame : F.toRectangleDecomposition.HasSameSideOverlap) :
    ∃ F' ∈ G.crossingChangeHexagonCompositeDecompositions C t x z,
      F.toRectangleDecomposition.IsRecut F'.toRectangleDecomposition := by
  obtain ⟨hfirst, hsecond⟩ := isEmpty_of_mem_crossingChangeHexagonCompositeDecompositions hF
  have hrecut := F.toRectangleDecomposition.isRecut_recut
    (F.toRectangleDecomposition.hasSameSideOverlap_iff.mp hsame).1 hfirst hsecond
  obtain ⟨F', hF', hF'E⟩ :=
    exists_crossingChange_toRectangleDecomposition_eq_of_isRepartition hX hF
      hrecut.isRepartition hrecut.isEmpty_first hrecut.isEmpty_second
      (F.exists_hexagon_of_isRecut hsame hfirst hsecond hrecut)
  exact ⟨F', hF', hF'E ▸ hrecut⟩

/-- If the annulus squares carry no `X`-marking, then off the diagonal every unpaired composite of
the crossing change homotopy equation has a mixed-side overlap: its two rectangles share exactly
one side column, initial for one and terminal for the other. -/
theorem hasMixedSideOverlap_of_mem_crossingChangeUnpairedHexagonComposites
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n} (hzx : z ≠ x)
    {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeUnpairedHexagonComposites C t x z) :
    F.toRectangleDecomposition.HasMixedSideOverlap := by
  obtain ⟨hF, hdisj, hnot⟩ := (G.mem_crossingChangeUnpairedHexagonComposites C t F).mp hF
  refine ((F.toRectangleDecomposition
    |>.not_hasDisjointSides_iff_sameSideOverlap_or_mixedSideOverlap_of_ne hzx).mp hdisj)
    |>.resolve_left fun hsame => ?_
  obtain ⟨F', hF', hrecut⟩ :=
    exists_crossingChange_isRecut_of_hasSameSideOverlap hX hF hsame
  exact hnot F' hF' hrecut

end TauCeti.GridDiagram
