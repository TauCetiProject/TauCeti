/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.SameSide
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Mixed.Pair
import TauCeti.Algebra.BigOperators.Finset.Pairing
import TauCeti.Algebra.CharP.Two

/-!
# Removing mixed-side pentagon pairs from the commutation homotopy equation

Off the diagonal, a counted pair of a forward and a reverse commutation pentagon turning on
opposite sides of the replaced grid line has the same underlying rectangle decomposition as a
unique unpaired hexagon composite, and the two have the same weight
(`Homotopy.Mixed.Pair`). Since a pentagon pair is determined by its underlying rectangles, this
matches the mixed-side pairs bijectively with their image, which therefore has the same total
weight.

That image is disjoint from the recut image of the same-side pairs removed in
`Homotopy.SameSide`. Every rectangle of a commutation pentagon has the replaced grid line as a
side, so this line is the unique common side of a mixed-side pair. A same-side pair shares it as
an initial or as a terminal side of both rectangles, and the recut of such a decomposition never
has the original common column as a common side.

Removing both families, the homotopy equation `∂ ∘ H + H ∘ ∂ = 1 + Ψ ∘ Φ` in characteristic two
becomes the statement that, off the diagonal, the unpaired hexagon composites lying in neither
partner image have total weight zero. No classification of these residual composites is
assumed here.

## Main results

* `TauCeti.GridDiagram.sum_pentagonPairWeight_mixedSide_eq_sum_partners`: off the diagonal, the
  mixed-side pentagon pairs and their hexagon-composite image have equal total weight.
* `TauCeti.GridDiagram.disjoint_sameSidePentagonPartners_mixedSidePentagonPartners`: off the
  diagonal, the two partner images are disjoint.
* `TauCeti.GridDiagram.unblockedDifferential_commutationHomotopy_add_eq_iff_sum_residual_eq_zero`:
  in characteristic two, the homotopy equation holds exactly when the residual unpaired
  composites have total weight zero off the diagonal.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1,
Proposition 3.2 (arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### The mixed-side pentagon pairs -/

/-- The counted forward--reverse pentagon pairs whose turns lie on opposite sides of the
replaced grid line: terminal--initial and initial--terminal pairs. -/
noncomputable def mixedSidePentagonPairs (x z : GridState n) :
    Finset (GridPentagonPairDecomposition a C.turnRow C.reverse.column C.reverse.turnRow x z) :=
  (G.pentagonPairDecompositions C x z).filter fun D => D.first.isLeft ≠ D.second.isLeft

/-- A mixed-side pair is counted and has distinct turn-side indicators. -/
@[simp]
theorem mem_mixedSidePentagonPairs {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow C.reverse.column C.reverse.turnRow x z) :
    D ∈ G.mixedSidePentagonPairs C x z ↔
      D ∈ G.pentagonPairDecompositions C x z ∧ D.first.isLeft ≠ D.second.isLeft := by
  simp only [mixedSidePentagonPairs, Finset.mem_filter]

/-- Every mixed-side pair is a term of the full round-trip coefficient sum. -/
theorem mixedSidePentagonPairs_subset (x z : GridState n) :
    G.mixedSidePentagonPairs C x z ⊆ G.pentagonPairDecompositions C x z :=
  fun D hD => ((G.mem_mixedSidePentagonPairs C D).mp hD).1

open scoped Classical in
/-- The counted pentagon pairs that do not turn on the same side are exactly the mixed-side
pairs. -/
theorem pentagonPairDecompositions_sdiff_sameSidePentagonPairs (x z : GridState n) :
    G.pentagonPairDecompositions C x z \ G.sameSidePentagonPairs C x z =
      G.mixedSidePentagonPairs C x z := by
  ext D
  simp only [Finset.mem_sdiff, mem_sameSidePentagonPairs, mem_mixedSidePentagonPairs]
  tauto

/-! ### Matching with unpaired hexagon composites -/

private theorem existsUnique_mixedSidePartner (R : Type*) [CommSemiring R]
    {x z : GridState n} (hzx : z ≠ x)
    (D : GridPentagonPairDecomposition a C.turnRow C.reverse.column C.reverse.turnRow x z)
    (hD : D ∈ G.mixedSidePentagonPairs C x z) :
    ∃! F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
      F ∈ G.unpairedHexagonComposites C x z ∧
        F.toRectangleDecomposition = D.toRectangleDecomposition ∧
        G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R D := by
  obtain ⟨hD, hside⟩ := (G.mem_mixedSidePentagonPairs C D).mp hD
  obtain ⟨hP, hQ⟩ := (G.mem_pentagonPairDecompositions C D).mp hD
  rcases D with ⟨m, P, Q⟩
  cases P with
  | inl P =>
    cases Q with
    | inl Q => simp at hside
    | inr Q =>
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using
        G.existsUnique_unpairedHexagonComposite_of_terminalInitialPentagonPair C R P Q
          ((G.inl_mem_commutationPentagons C P).mp hP)
          (((G.swapColumns a b).inr_mem_commutationPentagons C.reverse Q).mp hQ) hzx
  | inr P =>
    cases Q with
    | inl Q =>
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using
        G.existsUnique_unpairedHexagonComposite_of_initialTerminalPentagonPair C R P Q
          ((G.inr_mem_commutationPentagons C P).mp hP)
          (((G.swapColumns a b).inl_mem_commutationPentagons C.reverse Q).mp hQ) hzx
    | inr Q => simp at hside

/-- The unpaired hexagon composites with the underlying rectangle decomposition of a counted
mixed-side pentagon pair. This is their exact image, without a claim that it exhausts the
unpaired composites. -/
noncomputable def mixedSidePentagonPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z) := by
  classical
  exact (G.unpairedHexagonComposites C x z).filter fun F =>
    ∃ D ∈ G.mixedSidePentagonPairs C x z,
      D.toRectangleDecomposition = F.toRectangleDecomposition

/-- Partners are exactly the unpaired composites sharing their underlying rectangle
decomposition with a counted mixed-side pair. -/
@[simp]
theorem mem_mixedSidePentagonPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z) :
    F ∈ G.mixedSidePentagonPartners C x z ↔
      F ∈ G.unpairedHexagonComposites C x z ∧
        ∃ D ∈ G.mixedSidePentagonPairs C x z,
          D.toRectangleDecomposition = F.toRectangleDecomposition := by
  classical
  simp only [mixedSidePentagonPartners, Finset.mem_filter]

/-- Every partner belongs to the unpaired-composite coefficient sum. -/
theorem mixedSidePentagonPartners_subset (x z : GridState n) :
    G.mixedSidePentagonPartners C x z ⊆ G.unpairedHexagonComposites C x z :=
  fun F hF => ((G.mem_mixedSidePentagonPartners C F).mp hF).1

/-- Off the diagonal, the mixed-side pentagon pairs and their hexagon-composite image have
equal total polynomial weight over every commutative semiring. -/
theorem sum_pentagonPairWeight_mixedSide_eq_sum_partners
    (R : Type*) [CommSemiring R] {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ G.mixedSidePentagonPairs C x z, G.pentagonPairWeight C R D =
      ∑ F ∈ G.mixedSidePentagonPartners C x z, G.hexagonCompositeWeight C R F := by
  have hunpaired {F} (hF : F ∈ G.mixedSidePentagonPartners C x z) :=
    ((G.mem_unpairedHexagonComposites C F).mp (G.mixedSidePentagonPartners_subset C x z hF)).1
  refine Finset.sum_bij_of_rel
    (fun D F => D.toRectangleDecomposition = F.toRectangleDecomposition)
    (fun D hD => ?_) (fun D _ E _ F _ hDF hEF => ?_) (fun D _ F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ((G.mem_mixedSidePentagonPartners C F).mp hF).2)
  · obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ := G.existsUnique_mixedSidePartner C R hzx D hD
    exact ⟨F, (G.mem_mixedSidePentagonPartners C F).mpr ⟨hF, D, hD, hFD.symm⟩, hFD.symm, hw.symm⟩
  · exact GridPentagonPairDecomposition.toRectangleDecomposition_injective (hDF.trans hEF.symm)
  · exact G.injOn_toRectangleDecomposition_hexagonCompositeDecompositions C x z
      (hunpaired hF) (hunpaired hF') (hDF.symm.trans hDF')

/-! ### Disjointness of the two partner images -/

/-- Off the diagonal, no unpaired composite is both the recut of a same-side pentagon pair and
the underlying decomposition of a mixed-side pentagon pair: the replaced grid line is a common
side of the latter but not of the former. -/
theorem disjoint_sameSidePentagonPartners_mixedSidePentagonPartners {x z : GridState n}
    (hzx : z ≠ x) :
    Disjoint (G.sameSidePentagonPartners C x z) (G.mixedSidePentagonPartners C x z) := by
  rw [Finset.disjoint_left]
  intro F hS hM
  obtain ⟨-, D, hD, hrecut⟩ := (G.mem_sameSidePentagonPartners C F).mp hS
  obtain ⟨-, E, -, hEF⟩ := (G.mem_mixedSidePentagonPartners C F).mp hM
  have hb : b ∈ F.toRectangleDecomposition.commonSideColumns :=
    hEF ▸ G.finRotate_mem_commonSideColumns_of_pentagonPair C E
  have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hrecut hzx
  obtain ⟨-, hside⟩ := (G.mem_sameSidePentagonPairs C D).mp hD
  rcases D with ⟨m, P, Q⟩
  cases P with
  | inl P =>
    cases Q with
    | inl Q =>
      have hcommon := (hrecut.isRecutOfRightEqRight hone (by
        simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
          GridCommutationPentagonBetween.toGridRectangleBetween_inl, P.right_eq, Q.right_eq,
          C.reverse_column]))
      apply hcommon.first_right_notMem_commonSideColumns
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl, P.right_eq] using hb
    | inr Q => simp at hside
  | inr P =>
    cases Q with
    | inl Q => simp at hside
    | inr Q =>
      have hcommon := (hrecut.isRecutOfLeftEqLeft hone (by
        simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
          GridCommutationPentagonBetween.toGridRectangleBetween_inr, P.left_eq, Q.left_eq,
          C.reverse_column]))
      apply hcommon.first_left_notMem_commonSideColumns
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr, P.left_eq] using hb

/-! ### The residual coefficient equation -/

open scoped Classical in
/-- Off the diagonal, after removing the same-side pairs and their recut image, the coefficient
equation holds exactly when the unpaired composites in neither partner image have total weight
zero. -/
theorem sum_sdiff_sameSide_eq_sum_sdiff_sameSide_iff_sum_residual_eq_zero
    (R : Type*) [CommSemiring R] [IsCancelAdd R] {x z : GridState n} (hzx : z ≠ x) :
    (∑ F ∈ G.unpairedHexagonComposites C x z \ G.sameSidePentagonPartners C x z,
          G.hexagonCompositeWeight C R F) =
        ∑ D ∈ G.pentagonPairDecompositions C x z \ G.sameSidePentagonPairs C x z,
          G.pentagonPairWeight C R D ↔
      ∑ F ∈ (G.unpairedHexagonComposites C x z \ G.sameSidePentagonPartners C x z) \
          G.mixedSidePentagonPartners C x z, G.hexagonCompositeWeight C R F = 0 := by
  have hsub : G.mixedSidePentagonPartners C x z ⊆
      G.unpairedHexagonComposites C x z \ G.sameSidePentagonPartners C x z :=
    fun F hF => Finset.mem_sdiff.mpr ⟨G.mixedSidePentagonPartners_subset C x z hF,
      Finset.disjoint_right.mp
        (G.disjoint_sameSidePentagonPartners_mixedSidePentagonPartners C hzx) hF⟩
  rw [G.pentagonPairDecompositions_sdiff_sameSidePentagonPairs C,
    G.sum_pentagonPairWeight_mixedSide_eq_sum_partners C R hzx,
    ← Finset.sum_sdiff hsub (f := G.hexagonCompositeWeight C R)]
  exact add_eq_right

open scoped Classical in
/-- In characteristic two, the commutation homotopy equation `∂ ∘ H + H ∘ ∂ = 1 + Ψ ∘ Φ` holds
on every chain exactly when, off the diagonal, the unpaired hexagon composites lying neither in
the recut image of the same-side pentagon pairs nor in the image of the mixed-side pentagon pairs
have total weight zero. -/
theorem unblockedDifferential_commutationHomotopy_add_eq_iff_sum_residual_eq_zero
    (R : Type*) [CommSemiring R] [CharP R 2] :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.commutationHomotopy R C c) +
          G.commutationHomotopy R C (G.unblockedDifferential R c) =
        c + (G.swapColumns a b).commutationMap R C.reverse (G.commutationMap R C c)) ↔
      ∀ x z : GridState n, z ≠ x →
        ∑ F ∈ (G.unpairedHexagonComposites C x z \ G.sameSidePentagonPartners C x z) \
            G.mixedSidePentagonPartners C x z, G.hexagonCompositeWeight C R F = 0 := by
  have : IsCancelAdd R := isCancelAdd_of_charTwo R
  rw [G.unblockedDifferential_commutationHomotopy_add_eq_iff_sdiff_sameSide C R]
  exact forall_congr' fun x => forall_congr' fun z => imp_congr_right fun hzx =>
    G.sum_sdiff_sameSide_eq_sum_sdiff_sameSide_iff_sum_residual_eq_zero C R hzx

end TauCeti.GridDiagram
