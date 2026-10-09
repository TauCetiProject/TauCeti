/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Sum
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Sum
public import TauCeti.KnotTheory.Grid.Commutation.Annulus.Diagonal
public import TauCeti.KnotTheory.Grid.Commutation.Disjoint.Reduction
import Mathlib.RingTheory.MvPolynomial.Basic
import TauCeti.Algebra.CharP.Two

/-!
# Removing the recut partners from the commutation equation

The four cross-overlap source families for each kind of pentagon have different common-side
orientations. Their recut images are disjoint too: empty-rectangle recutting is reversible and
unique, so a partner cannot come from two source families. This permits summing over their unions
without counting a domain twice.

After removing these unions from the pentagon--rectangle sums, the off-diagonal chain-map
identity is exactly the assertion that the remaining terms have the total weight of the two
turn-point-cut families. This isolates the remaining geometric cancellation on the
pentagon--rectangle side; it does not assert that cancellation.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G) {x z : GridState n}

private theorem source_eq_of_recut
    {D E : GridRectanglePentagonDecomposition C.column C.turnRow x z}
    {F : GridRectangleDecomposition x z} (hzx : z ≠ x)
    (hD : D ∈ G.rectanglePentagonDecompositions C x z)
    (hE : E ∈ G.rectanglePentagonDecompositions C x z)
    (hrD : D.toRectangleDecomposition.IsRecut F)
    (hrE : E.toRectangleDecomposition.IsRecut F) : D = E := by
  apply GridRectanglePentagonDecomposition.toRectangleDecomposition_injective
  exact GridRectangleDecomposition.IsRecut.eq_of_isRecut hrD hrE
    (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hrD hzx)
    (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hrE hzx)
    (G.toRectangleDecomposition_first_isEmpty_of_mem_rectanglePentagonDecompositions C hD)
    (G.toRectangleDecomposition_second_isEmpty_of_mem_rectanglePentagonDecompositions C hD)
    (G.toRectangleDecomposition_first_isEmpty_of_mem_rectanglePentagonDecompositions C hE)
    (G.toRectangleDecomposition_second_isEmpty_of_mem_rectanglePentagonDecompositions C hE)

private theorem disjoint_partners_of_disjoint_sources
    (S T : Finset (GridRectanglePentagonDecomposition C.column C.turnRow x z))
    (U V : Finset (GridPentagonRectangleDecomposition C.column C.turnRow x z))
    (hS : S ⊆ G.rectanglePentagonDecompositions C x z) (hT : T ⊆ G.rectanglePentagonDecompositions
      C x z)
    (hU : ∀ F, F ∈ U ↔ ∃ D ∈ S, D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition)
    (hV : ∀ F, F ∈ V ↔ ∃ D ∈ T, D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition)
    (hST : Disjoint S T) (hzx : z ≠ x) : Disjoint U V := by
  refine Finset.disjoint_left.2 fun F hFU hFV => ?_
  obtain ⟨D, hD, hrD⟩ := (hU F).1 hFU
  obtain ⟨E, hE, hrE⟩ := (hV F).1 hFV
  have hDE := G.source_eq_of_recut C hzx (hS hD) (hT hE) hrD hrE
  subst E
  exact Finset.disjoint_left.mp hST hD hE

open scoped Classical in
private theorem disjoint_cross_partners (hzx : z ≠ x) :
    Disjoint (G.initialOverlapPartners C x z ∪ G.terminalCrossOverlapPartners C x z ∪
        G.leftRightOverlapPartners C x z) (G.rightLeftOverlapPartners C x z) ∧
      Disjoint (G.initialOverlapPartners C x z ∪ G.terminalCrossOverlapPartners C x z)
        (G.leftRightOverlapPartners C x z) ∧
      Disjoint (G.initialOverlapPartners C x z) (G.terminalCrossOverlapPartners C x z) := by
  obtain ⟨-, -, h₁, h₂, h₃⟩ := G.disjoint_overlap_families C hzx
  refine ⟨?_, ?_, ?_⟩
  · apply G.disjoint_partners_of_disjoint_sources C _ _ _ _
      (Finset.union_subset
        (Finset.union_subset
          (G.initialOverlapSources_subset_rectanglePentagonDecompositions C)
          (G.terminalCrossOverlapSources_subset_rectanglePentagonDecompositions C))
        (G.leftRightOverlapSources_subset C))
      (G.rightLeftOverlapSources_subset C)
      _ (G.mem_rightLeftOverlapPartners C) h₁ hzx
    intro F
    simp only [Finset.mem_union,
      mem_initialOverlapPartners, mem_terminalCrossOverlapPartners, mem_leftRightOverlapPartners,
      or_and_right, exists_or]
  · apply G.disjoint_partners_of_disjoint_sources C _ _ _ _
      (Finset.union_subset
        (G.initialOverlapSources_subset_rectanglePentagonDecompositions C)
        (G.terminalCrossOverlapSources_subset_rectanglePentagonDecompositions C))
      (G.leftRightOverlapSources_subset C)
      _ (G.mem_leftRightOverlapPartners C) h₂ hzx
    intro F
    simp only [Finset.mem_union,
      mem_initialOverlapPartners, mem_terminalCrossOverlapPartners,
      or_and_right, exists_or]
  · apply G.disjoint_partners_of_disjoint_sources C _ _ _ _
      (G.initialOverlapSources_subset_rectanglePentagonDecompositions C)
      (G.terminalCrossOverlapSources_subset_rectanglePentagonDecompositions C)
      (G.mem_initialOverlapPartners C) (G.mem_terminalCrossOverlapPartners C) h₃ hzx

/-- The union of the four cross-overlap recut partner families for
terminal-side pentagons. These are the terms accounted for by recutting
rectangle--pentagon domains, excluding the turn-point-cut correspondence. -/
noncomputable def crossOverlapPartners (x z : GridState n) :
    Finset (GridPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact G.initialOverlapPartners C x z ∪ G.terminalCrossOverlapPartners C x z ∪
    G.leftRightOverlapPartners C x z ∪ G.rightLeftOverlapPartners C x z

/-- A cross-overlap partner belongs to one of the four recut image families. -/
@[simp]
theorem mem_crossOverlapPartners (F : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    F ∈ G.crossOverlapPartners C x z ↔
      F ∈ G.initialOverlapPartners C x z ∨ F ∈ G.terminalCrossOverlapPartners C x z ∨
        F ∈ G.leftRightOverlapPartners C x z ∨ F ∈ G.rightLeftOverlapPartners C x z := by
  classical
  simp only [crossOverlapPartners, Finset.mem_union]
  tauto

/-- Summing over the recut partner union counts each domain once. -/
theorem sum_crossOverlapPartners {M : Type*} [AddCommMonoid M]
    (w : GridPentagonRectangleDecomposition C.column C.turnRow x z → M) (hzx : z ≠ x) :
    ∑ F ∈ G.crossOverlapPartners C x z, w F =
      (∑ F ∈ G.initialOverlapPartners C x z, w F) +
        (∑ F ∈ G.terminalCrossOverlapPartners C x z, w F) +
        (∑ F ∈ G.leftRightOverlapPartners C x z, w F) +
        ∑ F ∈ G.rightLeftOverlapPartners C x z, w F := by
  classical
  obtain ⟨h₁, h₂, h₃⟩ := G.disjoint_cross_partners C hzx
  rw [crossOverlapPartners, Finset.sum_union h₁, Finset.sum_union h₂, Finset.sum_union h₃]

private theorem initialPentagon_source_eq_of_recut
    {D E : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z}
    {F : GridRectangleDecomposition x z} (hzx : z ≠ x)
    (hD : D ∈ G.rectangleInitialPentagonDecompositions C x z) (hE : E ∈
      G.rectangleInitialPentagonDecompositions C x z)
    (hrD : D.toGridRectangleDecomposition.IsRecut F) (hrE : E.toGridRectangleDecomposition.IsRecut
      F) : D = E := by
  apply GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition_injective
  exact GridRectangleDecomposition.IsRecut.eq_of_isRecut hrD hrE
    (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hrD hzx)
    (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hrE hzx)
    (G.toGridRectangleDecomposition_first_isEmpty_of_mem_rectangleInitialPentagonDecompositions
      C hD)
    (G.toGridRectangleDecomposition_second_isEmpty_of_mem_rectangleInitialPentagonDecompositions
      C hD)
    (G.toGridRectangleDecomposition_first_isEmpty_of_mem_rectangleInitialPentagonDecompositions
      C hE)
    (G.toGridRectangleDecomposition_second_isEmpty_of_mem_rectangleInitialPentagonDecompositions
      C hE)

private theorem initialPentagon_disjoint_partners_of_disjoint_sources
    (S T : Finset (GridRectangleInitialPentagonDecomposition C.column C.turnRow x z))
    (U V : Finset (GridInitialPentagonRectangleDecomposition C.column C.turnRow x z))
    (hS : S ⊆ G.rectangleInitialPentagonDecompositions C x z) (hT : T ⊆
      G.rectangleInitialPentagonDecompositions C x z)
    (hU : ∀ F, F ∈ U ↔ ∃ D ∈ S, D.toGridRectangleDecomposition.IsRecut
      F.toGridRectangleDecomposition)
    (hV : ∀ F, F ∈ V ↔ ∃ D ∈ T, D.toGridRectangleDecomposition.IsRecut
      F.toGridRectangleDecomposition)
    (hST : Disjoint S T) (hzx : z ≠ x) : Disjoint U V := by
  refine Finset.disjoint_left.2 fun F hFU hFV => ?_
  obtain ⟨D, hD, hrD⟩ := (hU F).1 hFU
  obtain ⟨E, hE, hrE⟩ := (hV F).1 hFV
  have hDE := G.initialPentagon_source_eq_of_recut C hzx (hS hD) (hT hE) hrD hrE
  subst E
  exact Finset.disjoint_left.mp hST hD hE

open scoped Classical in
private theorem initialPentagon_disjoint_cross_partners (hzx : z ≠ x) :
    Disjoint (G.initialPentagonInitialCrossOverlapPartners C x z ∪
      G.initialPentagonTerminalOverlapPartners C x z ∪
        G.initialPentagonLeftRightOverlapPartners C x z)
          (G.initialPentagonRightLeftOverlapPartners C x z) ∧
      Disjoint (G.initialPentagonInitialCrossOverlapPartners C x z ∪
        G.initialPentagonTerminalOverlapPartners C x z)
        (G.initialPentagonLeftRightOverlapPartners C x z) ∧
      Disjoint (G.initialPentagonInitialCrossOverlapPartners C x z)
        (G.initialPentagonTerminalOverlapPartners C x z) := by
  obtain ⟨-, -, h₁, h₂, h₃⟩ := G.disjoint_initialPentagon_overlap_families C hzx
  refine ⟨?_, ?_, ?_⟩
  · apply G.initialPentagon_disjoint_partners_of_disjoint_sources C _ _ _ _
      (Finset.union_subset
        (Finset.union_subset
          (G.initialPentagonInitialCrossOverlapSources_subset C)
          (G.initialPentagonTerminalOverlapSources_subset C))
        (G.initialPentagonLeftRightOverlapSources_subset C))
      (G.initialPentagonRightLeftOverlapSources_subset C)
      _ (G.mem_initialPentagonRightLeftOverlapPartners C) h₁ hzx
    intro F
    simp only [Finset.mem_union,
      mem_initialPentagonInitialCrossOverlapPartners, mem_initialPentagonTerminalOverlapPartners,
      mem_initialPentagonLeftRightOverlapPartners,
      or_and_right, exists_or]
  · apply G.initialPentagon_disjoint_partners_of_disjoint_sources C _ _ _ _
      (Finset.union_subset
        (G.initialPentagonInitialCrossOverlapSources_subset C)
        (G.initialPentagonTerminalOverlapSources_subset C))
      (G.initialPentagonLeftRightOverlapSources_subset C)
      _ (G.mem_initialPentagonLeftRightOverlapPartners C) h₂ hzx
    intro F
    simp only [Finset.mem_union,
      mem_initialPentagonInitialCrossOverlapPartners, mem_initialPentagonTerminalOverlapPartners,
      or_and_right, exists_or]
  · apply G.initialPentagon_disjoint_partners_of_disjoint_sources C _ _ _ _
      (G.initialPentagonInitialCrossOverlapSources_subset C)
      (G.initialPentagonTerminalOverlapSources_subset C)
      (G.mem_initialPentagonInitialCrossOverlapPartners C)
      (G.mem_initialPentagonTerminalOverlapPartners C) h₃ hzx

/-- The union of the four cross-overlap recut partner families for
initial-side pentagons. These are the terms accounted for by recutting
rectangle--pentagon domains, excluding the turn-point-cut correspondence. -/
noncomputable def initialPentagonCrossOverlapPartners (x z : GridState n) :
    Finset (GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact G.initialPentagonInitialCrossOverlapPartners C x z ∪
    G.initialPentagonTerminalOverlapPartners C x z ∪
    G.initialPentagonLeftRightOverlapPartners C x z ∪
      G.initialPentagonRightLeftOverlapPartners C x z

/-- A cross-overlap partner belongs to one of the four recut image families. -/
@[simp]
theorem mem_initialPentagonCrossOverlapPartners (F : GridInitialPentagonRectangleDecomposition
  C.column C.turnRow x z) :
    F ∈ G.initialPentagonCrossOverlapPartners C x z ↔
      F ∈ G.initialPentagonInitialCrossOverlapPartners C x z ∨ F ∈
        G.initialPentagonTerminalOverlapPartners C x z ∨
        F ∈ G.initialPentagonLeftRightOverlapPartners C x z ∨ F ∈
          G.initialPentagonRightLeftOverlapPartners C x z := by
  classical
  simp only [initialPentagonCrossOverlapPartners, Finset.mem_union]
  tauto

/-- Summing over the recut partner union counts each domain once. -/
theorem sum_initialPentagonCrossOverlapPartners {M : Type*} [AddCommMonoid M]
    (w : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z → M) (hzx : z ≠ x) :
    ∑ F ∈ G.initialPentagonCrossOverlapPartners C x z, w F =
      (∑ F ∈ G.initialPentagonInitialCrossOverlapPartners C x z, w F) +
        (∑ F ∈ G.initialPentagonTerminalOverlapPartners C x z, w F) +
        (∑ F ∈ G.initialPentagonLeftRightOverlapPartners C x z, w F) +
        ∑ F ∈ G.initialPentagonRightLeftOverlapPartners C x z, w F := by
  classical
  obtain ⟨h₁, h₂, h₃⟩ := G.initialPentagon_disjoint_cross_partners C hzx
  rw [initialPentagonCrossOverlapPartners, Finset.sum_union h₁, Finset.sum_union h₂,
    Finset.sum_union h₃]

open scoped Classical in
/-- Every cross-overlap partner is a counted overlapping domain. -/
theorem crossOverlapPartners_subset_filter (hzx : z ≠ x) :
    G.crossOverlapPartners C x z ⊆
      (G.pentagonRectangleDecompositions C x z).filter (fun F => ¬F.HasDisjointSides) := by
  intro F hF
  obtain ⟨D, hD, hr⟩ : ∃ D ∈ G.rectanglePentagonDecompositions C x z,
      D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition := by
    rcases (G.mem_crossOverlapPartners C F).1 hF with hF | hF | hF | hF
    · obtain ⟨D, hD, hr⟩ := (G.mem_initialOverlapPartners C F).1 hF
      exact ⟨D, G.initialOverlapSources_subset_rectanglePentagonDecompositions C hD, hr⟩
    · obtain ⟨D, hD, hr⟩ := (G.mem_terminalCrossOverlapPartners C F).1 hF
      exact ⟨D, G.terminalCrossOverlapSources_subset_rectanglePentagonDecompositions C hD, hr⟩
    · obtain ⟨D, hD, hr⟩ := (G.mem_leftRightOverlapPartners C F).1 hF
      exact ⟨D, G.leftRightOverlapSources_subset C hD, hr⟩
    · obtain ⟨D, hD, hr⟩ := (G.mem_rightLeftOverlapPartners C F).1 hF
      exact ⟨D, G.rightLeftOverlapSources_subset C hD, hr⟩
  have hcounted : F ∈ G.pentagonRectangleDecompositions C x z := by
    rcases (G.mem_crossOverlapPartners C F).1 hF with hF | hF | hF | hF
    · exact G.initialOverlapPartners_subset_pentagonRectangleDecompositions C hF
    · exact G.terminalCrossOverlapPartners_subset_pentagonRectangleDecompositions C hF
    · exact G.leftRightOverlapPartners_subset C hF
    · exact G.rightLeftOverlapPartners_subset C hF
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hr hzx
  have hback : F.toRectangleDecomposition.IsRecut D.toRectangleDecomposition :=
    hr.symm hone
      (G.toRectangleDecomposition_first_isEmpty_of_mem_rectanglePentagonDecompositions C hD)
      (G.toRectangleDecomposition_second_isEmpty_of_mem_rectanglePentagonDecompositions C hD)
  have hnot := F.toRectangleDecomposition.not_hasDisjointSides_of_hasOneCommonSide
    (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback hzx)
  exact Finset.mem_filter.2 ⟨hcounted, by
    simpa only [GridPentagonRectangleDecomposition.hasDisjointSides_def] using hnot⟩

open scoped Classical in
/-- Every cross-overlap partner is a counted overlapping domain. -/
theorem initialPentagonCrossOverlapPartners_subset_filter (hzx : z ≠ x) :
    G.initialPentagonCrossOverlapPartners C x z ⊆
      (G.initialPentagonRectangleDecompositions C x z).filter (fun F => ¬F.HasDisjointSides) := by
  intro F hF
  obtain ⟨D, hD, hr⟩ : ∃ D ∈ G.rectangleInitialPentagonDecompositions C x z,
      D.toGridRectangleDecomposition.IsRecut F.toGridRectangleDecomposition := by
    rcases (G.mem_initialPentagonCrossOverlapPartners C F).1 hF with hF | hF | hF | hF
    · obtain ⟨D, hD, hr⟩ := (G.mem_initialPentagonInitialCrossOverlapPartners C F).1 hF
      exact ⟨D, G.initialPentagonInitialCrossOverlapSources_subset C hD, hr⟩
    · obtain ⟨D, hD, hr⟩ := (G.mem_initialPentagonTerminalOverlapPartners C F).1 hF
      exact ⟨D, G.initialPentagonTerminalOverlapSources_subset C hD, hr⟩
    · obtain ⟨D, hD, hr⟩ := (G.mem_initialPentagonLeftRightOverlapPartners C F).1 hF
      exact ⟨D, G.initialPentagonLeftRightOverlapSources_subset C hD, hr⟩
    · obtain ⟨D, hD, hr⟩ := (G.mem_initialPentagonRightLeftOverlapPartners C F).1 hF
      exact ⟨D, G.initialPentagonRightLeftOverlapSources_subset C hD, hr⟩
  have hcounted : F ∈ G.initialPentagonRectangleDecompositions C x z := by
    rcases (G.mem_initialPentagonCrossOverlapPartners C F).1 hF with hF | hF | hF | hF
    · exact G.initialPentagonInitialCrossOverlapPartners_subset C hF
    · exact G.initialPentagonTerminalOverlapPartners_subset C hF
    · exact G.initialPentagonLeftRightOverlapPartners_subset C hF
    · exact G.initialPentagonRightLeftOverlapPartners_subset C hF
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hr hzx
  have hback : F.toGridRectangleDecomposition.IsRecut D.toGridRectangleDecomposition :=
    hr.symm hone
      (G.toGridRectangleDecomposition_first_isEmpty_of_mem_rectangleInitialPentagonDecompositions
      C hD)
      (G.toGridRectangleDecomposition_second_isEmpty_of_mem_rectangleInitialPentagonDecompositions
      C hD)
  have hnot := F.toGridRectangleDecomposition.not_hasDisjointSides_of_hasOneCommonSide
    (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hback hzx)
  exact Finset.mem_filter.2 ⟨hcounted, hnot⟩

variable (R : Type*) [CommSemiring R] [CharP R 2]

open scoped Classical in
/-- Off the diagonal, the commutation coefficient identity is equivalent to the assertion that
the overlapping pentagon--rectangle domains left after removing all cross-overlap recut partners
have the total weight of the two turn-point-cut families. -/
theorem sum_commutation_overlap_eq_iff_sdiff_crossOverlapPartners (hzx : z ≠ x) :
    (∑ D ∈ (G.rectanglePentagonDecompositions C x z).filter
        (fun D => ¬D.HasDisjointSides), G.rectanglePentagonWeight C R D) +
        ∑ D ∈ (G.rectangleInitialPentagonDecompositions C x z).filter
          (fun D => ¬D.HasDisjointSides), G.rectangleInitialPentagonWeight C R D =
      (∑ F ∈ (G.pentagonRectangleDecompositions C x z).filter
        (fun F => ¬F.HasDisjointSides), G.pentagonRectangleWeight C R F) +
        ∑ F ∈ (G.initialPentagonRectangleDecompositions C x z).filter
          (fun F => ¬F.HasDisjointSides), G.initialPentagonRectangleWeight C R F ↔
    (∑ F ∈ (G.pentagonRectangleDecompositions C x z).filter
        (fun F => ¬F.HasDisjointSides) \ G.crossOverlapPartners C x z,
        G.pentagonRectangleWeight C R F) +
        ∑ F ∈ (G.initialPentagonRectangleDecompositions C x z).filter
          (fun F => ¬F.HasDisjointSides) \ G.initialPentagonCrossOverlapPartners C x z,
          G.initialPentagonRectangleWeight C R F =
      (∑ F ∈ G.pentagonRectangleTurnCuts C x z, G.pentagonRectangleWeight C R F) +
        ∑ F ∈ G.initialPentagonRectangleTurnCuts C x z,
          G.initialPentagonRectangleWeight C R F := by
  classical
  rw [G.sum_rectanglePentagonWeight_overlap_eq_sum_partners C R hzx,
    G.sum_rectangleInitialPentagonWeight_overlap_eq_sum_partners C R hzx,
    ← G.sum_crossOverlapPartners C (G.pentagonRectangleWeight C R) hzx,
    ← G.sum_initialPentagonCrossOverlapPartners C (G.initialPentagonRectangleWeight C R) hzx,
    ← Finset.sum_sdiff (G.crossOverlapPartners_subset_filter C hzx)
      (f := G.pentagonRectangleWeight C R),
    ← Finset.sum_sdiff (G.initialPentagonCrossOverlapPartners_subset_filter C hzx)
      (f := G.initialPentagonRectangleWeight C R)]
  -- The common recut contributions cancel in characteristic two.
  have hc : ∀ a b c d e f : MvPolynomial (Fin n) R,
      a + b + (c + d) = e + a + (f + c) ↔ e + f = d + b := by
    intro a b c d e f
    have hleft : a + b + (c + d) = (a + c) + (b + d) := by abel
    have hright : e + a + (f + c) = (a + c) + (e + f) := by abel
    rw [hleft, hright]
    constructor
    · intro h
      have h' := congrArg (fun t => (a + c) + t) h
      simpa only [CharTwo.add_cancel_left, add_comm b d] using h'.symm
    · intro h
      rw [h]
      ac_rfl
  exact hc _ _ _ _ _ _

open scoped Classical in
/-- The commutation map is a chain map exactly when the residual off-diagonal
pentagon--rectangle sums have the turn-point-cut weights. The diagonal and all disjoint-side and
cross-overlap recut terms have already been discharged. -/
theorem commutationMap_comp_unblockedDifferential_eq_iff_sdiff_crossOverlapPartners :
    (G.commutationMap R C).comp (G.unblockedDifferential R) =
      ((G.swapColumns C.column (finRotate n C.column)).unblockedDifferential R).comp
        (G.commutationMap R C) ↔
    ∀ x z : GridState n, z ≠ x →
      (∑ F ∈ (G.pentagonRectangleDecompositions C x z).filter
          (fun F => ¬F.HasDisjointSides) \ G.crossOverlapPartners C x z,
          G.pentagonRectangleWeight C R F) +
          ∑ F ∈ (G.initialPentagonRectangleDecompositions C x z).filter
            (fun F => ¬F.HasDisjointSides) \ G.initialPentagonCrossOverlapPartners C x z,
            G.initialPentagonRectangleWeight C R F =
        (∑ F ∈ G.pentagonRectangleTurnCuts C x z, G.pentagonRectangleWeight C R F) +
          ∑ F ∈ G.initialPentagonRectangleTurnCuts C x z,
            G.initialPentagonRectangleWeight C R F := by
  classical
  have : IsCancelAdd R := isCancelAdd_of_charTwo R
  rw [G.commutationMap_comp_unblockedDifferential_eq_iff C R]
  constructor
  · intro h x z hzx
    apply (G.sum_commutation_overlap_eq_iff_sdiff_crossOverlapPartners C R hzx).1
    exact (G.sum_rectanglePentagonWeight_add_sum_rectangleInitialPentagonWeight_eq_iff_overlap
      C R x z).1 (h x z)
  · intro h x z
    by_cases hzx : z = x
    · subst z
      exact G.sum_rectanglePentagonWeight_add_sum_rectangleInitialPentagonWeight_self C R x
    · apply (G.sum_rectanglePentagonWeight_add_sum_rectangleInitialPentagonWeight_eq_iff_overlap
        C R x z).2
      exact (G.sum_commutation_overlap_eq_iff_sdiff_crossOverlapPartners C R hzx).2 (h x z hzx)

end TauCeti.GridDiagram
