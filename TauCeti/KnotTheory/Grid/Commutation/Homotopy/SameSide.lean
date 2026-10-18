/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.TerminalPair
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.InitialPair.Weight
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.PentagonPair

/-!
# Removing same-side pentagon pairs from the commutation homotopy equation

Off the diagonal, a counted pair of forward and reverse pentagons turning on the same side
recuts to a unique unpaired hexagon composite of the same weight. Distinct pentagon pairs
have distinct recuts. Consequently their total contribution equals that of their exact recut
image, and both families can be removed from the homotopy coefficient equation.

The partner family below is precisely this image, not all unpaired composites. The remaining
coefficient equation compares its complement with the mixed-side pentagon pairs. No converse
classification of unpaired composites is assumed.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1,
Proposition 3.2 (arXiv:math/0610559). The geometric input is the weighted recut matching in
`Homotopy.TerminalPair` and `Homotopy.InitialPair.Weight`.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-- The counted forward--reverse pentagon pairs whose turns lie on the same side of the
replaced grid line. This includes both terminal--terminal and initial--initial pairs. -/
noncomputable def sameSidePentagonPairs (x z : GridState n) :
    Finset (GridPentagonPairDecomposition a C.turnRow C.reverse.column C.reverse.turnRow x z) :=
  (G.pentagonPairDecompositions C x z).filter fun D => D.first.isLeft = D.second.isLeft

/-- A same-side pair is counted and has equal turn-side indicators. -/
@[simp]
theorem mem_sameSidePentagonPairs {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow C.reverse.column C.reverse.turnRow x z) :
    D ∈ G.sameSidePentagonPairs C x z ↔
      D ∈ G.pentagonPairDecompositions C x z ∧ D.first.isLeft = D.second.isLeft := by
  simp only [sameSidePentagonPairs, Finset.mem_filter]

/-- Every same-side pair is a term of the full round-trip coefficient sum. -/
theorem sameSidePentagonPairs_subset (x z : GridState n) :
    G.sameSidePentagonPairs C x z ⊆ G.pentagonPairDecompositions C x z :=
  fun D hD => ((G.mem_sameSidePentagonPairs C D).mp hD).1

private theorem existsUnique_sameSidePartner (R : Type*) [CommSemiring R]
    {x z : GridState n} (hzx : z ≠ x)
    (D : GridPentagonPairDecomposition a C.turnRow C.reverse.column C.reverse.turnRow x z)
    (hD : D ∈ G.sameSidePentagonPairs C x z) :
    ∃! F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z,
      F ∈ G.unpairedHexagonComposites C x z ∧
        D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition ∧
        G.hexagonCompositeWeight C R F = G.pentagonPairWeight C R D := by
  obtain ⟨hD, hside⟩ := (G.mem_sameSidePentagonPairs C D).mp hD
  obtain ⟨hP, hQ⟩ := (G.mem_pentagonPairDecompositions C D).mp hD
  rcases D with ⟨m, P, Q⟩
  cases P with
  | inl P =>
    cases Q with
    | inl Q =>
      have hne : P.left ≠ Q.left := by
        intro h
        apply hzx
        calc
          z = m.swapColumns P.left b := by
            simpa only [← h, Q.right_eq, C.reverse_column] using Q.target_eq_swapColumns
          _ = (x.swapColumns P.left b).swapColumns P.left b :=
            congrArg (GridState.swapColumns P.left b)
              (by simpa only [P.right_eq] using P.target_eq_swapColumns)
          _ = x := GridState.swapColumns_swapColumns _ _ _
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl] using
        G.existsUnique_unpairedHexagonComposite_of_terminalPentagonPair C R P Q
          ((G.inl_mem_commutationPentagons C P).mp hP)
          (((G.swapColumns a b).inl_mem_commutationPentagons C.reverse Q).mp hQ) hne
    | inr Q => simp at hside
  | inr P =>
    cases Q with
    | inl Q => simp at hside
    | inr Q =>
      have hne : P.right ≠ Q.right := by
        intro h
        apply hzx
        calc
          z = m.swapColumns b P.right := by
            simpa only [← h, Q.left_eq, C.reverse_column] using Q.target_eq_swapColumns
          _ = (x.swapColumns b P.right).swapColumns b P.right :=
            congrArg (GridState.swapColumns b P.right)
              (by simpa only [P.left_eq] using P.target_eq_swapColumns)
          _ = x := GridState.swapColumns_swapColumns _ _ _
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using
        G.existsUnique_unpairedHexagonComposite_of_initialPentagonPair C R P Q
          ((G.inr_mem_commutationPentagons C P).mp hP)
          (((G.swapColumns a b).inr_mem_commutationPentagons C.reverse Q).mp hQ) hne

private noncomputable def sameSidePartner {x z : GridState n} (hzx : z ≠ x)
    (D : {D // D ∈ G.sameSidePentagonPairs C x z}) :
    GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z :=
  (G.existsUnique_sameSidePartner C ℕ hzx D.val D.property).exists.choose

private theorem sameSidePartner_spec {x z : GridState n} (hzx : z ≠ x)
    (D : {D // D ∈ G.sameSidePentagonPairs C x z}) :
    G.sameSidePartner C hzx D ∈ G.unpairedHexagonComposites C x z ∧
      D.val.toRectangleDecomposition.IsRecut
        (G.sameSidePartner C hzx D).toRectangleDecomposition :=
  (G.existsUnique_sameSidePartner C ℕ hzx D.val D.property).exists.choose_spec.imp_right
    fun h => h.1

private theorem sameSidePartner_injective {x z : GridState n} (hzx : z ≠ x) :
    Function.Injective (G.sameSidePartner C hzx) := by
  intro D E h
  have hD := (G.sameSidePartner_spec C hzx D).2
  have hE := (G.sameSidePartner_spec C hzx E).2
  rw [← h] at hE
  obtain ⟨hfD, hsD⟩ := G.isEmpty_of_mem_pentagonPairDecompositions C
    (G.sameSidePentagonPairs_subset C x z D.property)
  obtain ⟨hfE, hsE⟩ := G.isEmpty_of_mem_pentagonPairDecompositions C
    (G.sameSidePentagonPairs_subset C x z E.property)
  apply Subtype.ext
  apply GridPentagonPairDecomposition.toRectangleDecomposition_injective
  exact hD.eq_of_isRecut hE
    (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hD hzx)
    (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hE hzx) hfD hsD hfE hsE

private theorem sameSidePartner_eq {x z : GridState n} (hzx : z ≠ x)
    (D : {D // D ∈ G.sameSidePentagonPairs C x z})
    {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.unpairedHexagonComposites C x z)
    (hrecut : D.val.toRectangleDecomposition.IsRecut F.toRectangleDecomposition) :
    G.sameSidePartner C hzx D = F := by
  apply G.injOn_toRectangleDecomposition_hexagonCompositeDecompositions C x z
    ((G.mem_unpairedHexagonComposites C _).mp (G.sameSidePartner_spec C hzx D).1).1
    ((G.mem_unpairedHexagonComposites C F).mp hF).1
  obtain ⟨hf, hs⟩ := G.isEmpty_of_mem_pentagonPairDecompositions C
    (G.sameSidePentagonPairs_subset C x z D.property)
  exact (D.val.toRectangleDecomposition.existsUnique_isRecut
    (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hrecut hzx) hf hs).unique
    (G.sameSidePartner_spec C hzx D).2 hrecut

/-- The unpaired hexagon composites obtained by recutting counted same-side pentagon pairs.
This is their exact recut image, without a claim that it exhausts the unpaired composites. -/
noncomputable def sameSidePentagonPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z) := by
  classical
  exact (G.unpairedHexagonComposites C x z).filter fun F =>
    ∃ D ∈ G.sameSidePentagonPairs C x z,
      D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition

/-- Partners are exactly the unpaired composites recutting a counted same-side pair. -/
@[simp]
theorem mem_sameSidePentagonPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z) :
    F ∈ G.sameSidePentagonPartners C x z ↔
      F ∈ G.unpairedHexagonComposites C x z ∧
        ∃ D ∈ G.sameSidePentagonPairs C x z,
          D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition := by
  classical
  simp only [sameSidePentagonPartners, Finset.mem_filter]

/-- Every partner belongs to the unpaired-composite coefficient sum. -/
theorem sameSidePentagonPartners_subset (x z : GridState n) :
    G.sameSidePentagonPartners C x z ⊆ G.unpairedHexagonComposites C x z :=
  fun F hF => ((G.mem_sameSidePentagonPartners C F).mp hF).1

private theorem sameSidePentagonPartners_eq_map {x z : GridState n} (hzx : z ≠ x) :
    G.sameSidePentagonPartners C x z = (G.sameSidePentagonPairs C x z).attach.map
      ⟨G.sameSidePartner C hzx, G.sameSidePartner_injective C hzx⟩ := by
  classical
  ext F
  simp only [mem_sameSidePentagonPartners, Finset.mem_map, Finset.mem_attach,
    true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hF, D, hD, hrecut⟩
    exact ⟨⟨D, hD⟩, G.sameSidePartner_eq C hzx ⟨D, hD⟩ hF hrecut⟩
  · rintro ⟨D, rfl⟩
    exact ⟨(G.sameSidePartner_spec C hzx D).1, D.val, D.property,
      (G.sameSidePartner_spec C hzx D).2⟩

/-- Off the diagonal, the same-side pentagon pairs and their exact hexagon-composite recut
image have equal total polynomial weight over every commutative semiring. -/
theorem sum_pentagonPairWeight_sameSide_eq_sum_partners
    (R : Type*) [CommSemiring R] {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ G.sameSidePentagonPairs C x z, G.pentagonPairWeight C R D =
      ∑ F ∈ G.sameSidePentagonPartners C x z, G.hexagonCompositeWeight C R F := by
  classical
  have hweight (D : {D // D ∈ G.sameSidePentagonPairs C x z}) :
      G.hexagonCompositeWeight C R (G.sameSidePartner C hzx D) =
        G.pentagonPairWeight C R D.val := by
    obtain ⟨F, ⟨hF, hrecut, hweight⟩, -⟩ :=
      G.existsUnique_sameSidePartner C R hzx D.val D.property
    rw [G.sameSidePartner_eq C hzx D hF hrecut, hweight]
  rw [G.sameSidePentagonPartners_eq_map C hzx, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, hweight, Finset.sum_attach]

open scoped Classical in
/-- The off-diagonal homotopy coefficient equation holds exactly when the remaining
unpaired composites and mixed-side pentagon pairs have equal total weight. -/
theorem sum_unpaired_eq_sum_pentagonPairs_iff_sdiff_sameSide
    (R : Type*) [CommSemiring R] [IsCancelAdd R] {x z : GridState n} (hzx : z ≠ x) :
    (∑ F ∈ G.unpairedHexagonComposites C x z, G.hexagonCompositeWeight C R F) =
        ∑ D ∈ G.pentagonPairDecompositions C x z, G.pentagonPairWeight C R D ↔
      (∑ F ∈ G.unpairedHexagonComposites C x z \ G.sameSidePentagonPartners C x z,
          G.hexagonCompositeWeight C R F) =
        ∑ D ∈ G.pentagonPairDecompositions C x z \ G.sameSidePentagonPairs C x z,
          G.pentagonPairWeight C R D := by
  rw [← Finset.sum_sdiff (G.sameSidePentagonPartners_subset C x z)
      (f := G.hexagonCompositeWeight C R),
    ← Finset.sum_sdiff (G.sameSidePentagonPairs_subset C x z)
      (f := G.pentagonPairWeight C R),
    G.sum_pentagonPairWeight_sameSide_eq_sum_partners C R hzx]
  exact add_right_cancel_iff

open scoped Classical in
/-- In characteristic two, the full commutation homotopy equation reduces to the
complement of the same-side recut image off the diagonal. The diagonal returning annuli
and the matched same-side pairs have already been discharged. -/
theorem unblockedDifferential_commutationHomotopy_add_eq_iff_sdiff_sameSide
    (R : Type*) [CommSemiring R] [IsCancelAdd R] [CharP R 2] :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.commutationHomotopy R C c) +
          G.commutationHomotopy R C (G.unblockedDifferential R c) =
        c + (G.swapColumns a b).commutationMap R C.reverse (G.commutationMap R C c)) ↔
      ∀ x z : GridState n, z ≠ x →
        (∑ F ∈ G.unpairedHexagonComposites C x z \ G.sameSidePentagonPartners C x z,
            G.hexagonCompositeWeight C R F) =
          ∑ D ∈ G.pentagonPairDecompositions C x z \ G.sameSidePentagonPairs C x z,
            G.pentagonPairWeight C R D := by
  rw [G.unblockedDifferential_commutationHomotopy_add_eq_iff_unpaired C R]
  have hdiag (x : GridState n) :
      (∑ D ∈ G.hexagonRectangleDecompositions C x x, G.hexagonRectangleWeight C R D) +
          ∑ D ∈ G.rectangleHexagonDecompositions C x x, G.rectangleHexagonWeight C R D =
        1 + ∑ D ∈ G.pentagonPairDecompositions C x x, G.pentagonPairWeight C R D := by
    simpa only [Finsupp.add_apply,
      G.unblockedDifferential_commutationHomotopy_single_apply C R,
      G.commutationHomotopy_unblockedDifferential_single_apply C R,
      G.reverse_commutationMap_commutationMap_single_apply C R,
      G.sum_commutationHexagonCoefficient_mul_unblockedCoefficient C R,
      G.sum_unblockedCoefficient_mul_commutationHexagonCoefficient C R,
      G.sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient C R] using
      G.unblockedDifferential_commutationHomotopy_add_single_apply_self_eq_one_add C R x
  simp only [hdiag, implies_true, true_and]
  exact forall_congr' fun x => forall_congr' fun z =>
    imp_congr_right fun hzx => G.sum_unpaired_eq_sum_pentagonPairs_iff_sdiff_sameSide C R hzx

end TauCeti.GridDiagram
