/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.SameSide
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Mixed
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Unpaired
import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Pentagon.Pair
import TauCeti.Algebra.BigOperators.Finset.Pairing
import TauCeti.Algebra.CharP.Two

/-!
# The homotopy equation of the crossing change maps

Let `C` be a column turn at the columns `a = C.column` and `b = finRotate n a` of a grid diagram
`G`, turning in row `s = C.turnRow`, and let `t ≠ s` be a second row. Write
`Φ : GC⁻(G) → GC⁻(G')` for the commutation map of `C` to `G' = G.swapColumns a b`,
`Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning at the same columns in row `t`,
and `H : GC⁻(G) → GC⁻(G)` for the crossing-change hexagon map `GridDiagram.crossingChangeHomotopy`.
When the annulus squares `GridDiagram.crossingChangeAnnulusSquares` carry no `X`-marking, this file
proves the homotopy equation

  `∂ ∘ H + H ∘ ∂ = w • 1 + Ψ ∘ Φ`

over every commutative semiring of characteristic two, where `w` is the annulus weight
`GridDiagram.crossingChangeAnnulusWeight`. For interleaving columns `a` and `b`, the two orders of
the markings give `w = V_b` when `O_a` lies on the arc of column `b` (turning at `s = O_a` and
`t = X_b`), and `w = V_a` when `O_a` lies off the arc of column `b` (turning at `s = X_a` and
`t = O_b`).

The diagonal, disjoint-side, and recut cancellations in `Homotopy.Diagonal`, `Homotopy.Disjoint`,
and `Homotopy.Recut` reduce the equation in characteristic two to an off-diagonal polynomial-weight
identity (`GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired`) between
the unpaired hexagon composites and the pentagon-pair products of `Ψ ∘ Φ`
(`GridDiagram.pentagonPairDecompositions` and `GridDiagram.pentagonPairWeight` applied to `C` and
`C.withTurnRow t`). That off-diagonal identity holds over *every* commutative semiring: same-side
pentagon pairs match bijectively by recutting (`Homotopy.SameSide`), mixed-side pentagon pairs match
bijectively by sharing the same two rectangles (`Homotopy.Mixed`), the two partner images are
disjoint because the replaced grid line is a common side of mixed-side pairs and never of a
same-side recut, and every unpaired composite arises from one of the two families
(`Homotopy.Unpaired`).

## Main definitions

* `TauCeti.GridDiagram.crossingChangeSameSidePentagonPartners`,
  `TauCeti.GridDiagram.crossingChangeMixedSidePentagonPartners`: the respective images of
  `GridDiagram.sameSidePentagonPairs` and `GridDiagram.mixedSidePentagonPairs` (for `C` and
  `C.withTurnRow t`) among the unpaired crossing-change hexagon composites.

## Main results

* `TauCeti.GridDiagram.crossingChangeUnpairedHexagonComposites_eq_union`: off the diagonal, the
  unpaired hexagon composites are the disjoint union of the same-side and mixed-side partner sets.
* `GridDiagram.sum_crossingChangeUnpairedHexagonComposites_eq_sum_commutationPentagonCoefficient`:
  off the diagonal, the unpaired composites have the total weight of the commutation-pentagon
  coefficient products over every commutative semiring.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq`: the homotopy equation
  `∂ ∘ H + H ∘ ∂ = w • 1 + Ψ ∘ Φ` in characteristic two.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc`,
  `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc`:
  the crossing-change homotopy equations `∂ ∘ H + H ∘ ∂ = V_b • 1 + Ψ ∘ Φ` and
  `∂ ∘ H + H ∘ ∂ = V_a • 1 + Ψ ∘ Φ` for interleaving columns.
* `TauCeti.GridDiagram.commutationMap_withTurnRow_commutationMap_of_mem_ker`: on cycles, `Ψ ∘ Φ`
  acts as multiplication by `w` up to a boundary.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 6.1, Proposition 6.1.3.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3.
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Same-side and mixed-side partner matchings -/

/-- The unpaired crossing-change hexagon composites obtained by recutting counted same-side
pentagon pairs for `C` and `C.withTurnRow t`. -/
noncomputable def crossingChangeSameSidePentagonPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.sameSidePentagonPairs C (C.withTurnRow t) x z,
      D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition

/-- Membership in `crossingChangeSameSidePentagonPartners` characterizes the recut image of counted
same-side pentagon pairs. -/
@[simp]
theorem mem_crossingChangeSameSidePentagonPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeSameSidePentagonPartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.sameSidePentagonPairs C (C.withTurnRow t) x z,
          D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition := by
  classical
  simp only [crossingChangeSameSidePentagonPartners, Finset.mem_filter]

/-- Every same-side partner is an unpaired crossing-change hexagon composite. -/
theorem crossingChangeSameSidePentagonPartners_subset (x z : GridState n) :
    G.crossingChangeSameSidePentagonPartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeSameSidePentagonPartners C t F).mp hF).1

/-- The unpaired crossing-change hexagon composites sharing their two underlying rectangles with a
counted mixed-side pentagon pair for `C` and `C.withTurnRow t`. -/
noncomputable def crossingChangeMixedSidePentagonPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.mixedSidePentagonPairs C (C.withTurnRow t) x z,
      D.toRectangleDecomposition = F.toRectangleDecomposition

/-- Membership in `crossingChangeMixedSidePentagonPartners` characterizes the rectangle-sharing
image of counted mixed-side pentagon pairs. -/
@[simp]
theorem mem_crossingChangeMixedSidePentagonPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeMixedSidePentagonPartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.mixedSidePentagonPairs C (C.withTurnRow t) x z,
          D.toRectangleDecomposition = F.toRectangleDecomposition := by
  classical
  simp only [crossingChangeMixedSidePentagonPartners, Finset.mem_filter]

/-- Every mixed-side partner is an unpaired crossing-change hexagon composite. -/
theorem crossingChangeMixedSidePentagonPartners_subset (x z : GridState n) :
    G.crossingChangeMixedSidePentagonPartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeMixedSidePentagonPartners C t F).mp hF).1

private theorem exists_sameSidePartner (R : Type*) [CommSemiring R]
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x)
    {D : GridPentagonPairDecomposition a C.turnRow a t x z}
    (hD : D ∈ G.sameSidePentagonPairs C (C.withTurnRow t) x z) :
    ∃ F ∈ G.crossingChangeSameSidePentagonPartners C t x z,
      D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition ∧
        G.pentagonPairWeight C (C.withTurnRow t) R D =
          G.crossingChangeHexagonCompositeWeight C t R F := by
  obtain ⟨hD', hside⟩ := (G.mem_sameSidePentagonPairs C (C.withTurnRow t) D).mp hD
  obtain ⟨hP, hQ⟩ := (G.mem_pentagonPairDecompositions C (C.withTurnRow t) D).mp hD'
  rcases D with ⟨m, P | P, Q | Q⟩
  · obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair R hX P Q
        ((G.inl_mem_commutationPentagons C P).mp hP)
        (((G.swapColumns a b).inl_mem_commutationPentagons (C.withTurnRow t) Q).mp hQ) hzx
    have hrecut' : (GridPentagonPairDecomposition.toRectangleDecomposition
        (⟨m, .inl P, .inl Q⟩ : GridPentagonPairDecomposition a C.turnRow a t x z)).IsRecut
        F.toRectangleDecomposition := by
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl] using hrecut
    exact ⟨F, (G.mem_crossingChangeSameSidePentagonPartners C t F).mpr ⟨hF, _, hD, hrecut'⟩,
      hrecut', by
        rw [G.pentagonPairWeight_def, G.commutationPentagonWeight_inl,
          (G.swapColumns a b).commutationPentagonWeight_inl (C.withTurnRow t)]
        exact (hw F hF hrecut).symm⟩
  · simp at hside
  · simp at hside
  · obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair R hX P Q
        ((G.inr_mem_commutationPentagons C P).mp hP)
        (((G.swapColumns a b).inr_mem_commutationPentagons (C.withTurnRow t) Q).mp hQ) hzx
    have hrecut' : (GridPentagonPairDecomposition.toRectangleDecomposition
        (⟨m, .inr P, .inr Q⟩ : GridPentagonPairDecomposition a C.turnRow a t x z)).IsRecut
        F.toRectangleDecomposition := by
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hrecut
    exact ⟨F, (G.mem_crossingChangeSameSidePentagonPartners C t F).mpr ⟨hF, _, hD, hrecut'⟩,
      hrecut', by
        rw [G.pentagonPairWeight_def, G.commutationPentagonWeight_inr,
          (G.swapColumns a b).commutationPentagonWeight_inr (C.withTurnRow t)]
        exact (hw F hF hrecut).symm⟩

private theorem exists_mixedSidePartner (R : Type*) [CommSemiring R]
    (hst : C.turnRow ≠ t) (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x)
    {D : GridPentagonPairDecomposition a C.turnRow a t x z}
    (hD : D ∈ G.mixedSidePentagonPairs C (C.withTurnRow t) x z) :
    ∃ F ∈ G.crossingChangeMixedSidePentagonPartners C t x z,
      D.toRectangleDecomposition = F.toRectangleDecomposition ∧
        G.pentagonPairWeight C (C.withTurnRow t) R D =
          G.crossingChangeHexagonCompositeWeight C t R F := by
  obtain ⟨hD', hside⟩ := (G.mem_mixedSidePentagonPairs C (C.withTurnRow t) D).mp hD
  obtain ⟨hP, hQ⟩ := (G.mem_pentagonPairDecompositions C (C.withTurnRow t) D).mp hD'
  rcases D with ⟨m, P | P, Q | Q⟩
  · simp at hside
  · obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalInitialPentagonPair R hst hX
        P Q ((G.inl_mem_commutationPentagons C P).mp hP)
        (((G.swapColumns a b).inr_mem_commutationPentagons (C.withTurnRow t) Q).mp hQ) hzx
    have hFD' : GridPentagonPairDecomposition.toRectangleDecomposition
        (⟨m, .inl P, .inr Q⟩ : GridPentagonPairDecomposition a C.turnRow a t x z) =
        F.toRectangleDecomposition := by
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hFD.symm
    exact ⟨F, (G.mem_crossingChangeMixedSidePentagonPartners C t F).mpr ⟨hF, _, hD, hFD'⟩,
      hFD', by
        rw [G.pentagonPairWeight_def, G.commutationPentagonWeight_inl,
          (G.swapColumns a b).commutationPentagonWeight_inr (C.withTurnRow t)]
        exact hw.symm⟩
  · obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialTerminalPentagonPair R hst hX
        P Q ((G.inr_mem_commutationPentagons C P).mp hP)
        (((G.swapColumns a b).inl_mem_commutationPentagons (C.withTurnRow t) Q).mp hQ) hzx
    have hFD' : GridPentagonPairDecomposition.toRectangleDecomposition
        (⟨m, .inr P, .inl Q⟩ : GridPentagonPairDecomposition a C.turnRow a t x z) =
        F.toRectangleDecomposition := by
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hFD.symm
    exact ⟨F, (G.mem_crossingChangeMixedSidePentagonPartners C t F).mpr ⟨hF, _, hD, hFD'⟩,
      hFD', by
        rw [G.pentagonPairWeight_def, G.commutationPentagonWeight_inr,
          (G.swapColumns a b).commutationPentagonWeight_inl (C.withTurnRow t)]
        exact hw.symm⟩
  · simp at hside

/-- Off the diagonal, if the annulus squares carry no `X`-marking, the counted same-side pentagon
pairs and their recut partners have equal total polynomial weight over every commutative
semiring. -/
theorem sum_pentagonPairWeight_sameSide_eq_sum_crossingChangePartners
    (R : Type*) [CommSemiring R] (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ G.sameSidePentagonPairs C (C.withTurnRow t) x z,
        G.pentagonPairWeight C (C.withTurnRow t) R D =
      ∑ F ∈ G.crossingChangeSameSidePentagonPartners C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F := by
  have hunpaired {F} (hF : F ∈ G.crossingChangeSameSidePentagonPartners C t x z) :=
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp
      (G.crossingChangeSameSidePentagonPartners_subset C t x z hF)).1
  refine Finset.sum_bij_of_rel
    (fun D F => D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition)
    (fun D hD => G.exists_sameSidePartner C t R hX hzx hD)
    (fun D hD E hE F _ hDF hEF => ?_)
    (fun D hD F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ((G.mem_crossingChangeSameSidePentagonPartners C t F).mp hF).2)
  · obtain ⟨hfD, hsD⟩ := G.isEmpty_of_mem_pentagonPairDecompositions C (C.withTurnRow t)
      (G.sameSidePentagonPairs_subset C (C.withTurnRow t) x z hD)
    obtain ⟨hfE, hsE⟩ := G.isEmpty_of_mem_pentagonPairDecompositions C (C.withTurnRow t)
      (G.sameSidePentagonPairs_subset C (C.withTurnRow t) x z hE)
    exact GridPentagonPairDecomposition.toRectangleDecomposition_injective
      (hDF.eq_of_isRecut hEF hfD hsD hfE hsE)
  · obtain ⟨hf, hs⟩ := G.isEmpty_of_mem_pentagonPairDecompositions C (C.withTurnRow t)
      (G.sameSidePentagonPairs_subset C (C.withTurnRow t) x z hD)
    exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hunpaired hF) (hunpaired hF')
      ((D.toRectangleDecomposition.existsUnique_isRecut
        (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hDF) hf hs).unique hDF hDF')

/-- Off the diagonal, if the turn rows `s` and `t` differ and the annulus squares carry no
`X`-marking, the counted mixed-side pentagon pairs and their partners have equal total polynomial
weight over every commutative semiring. -/
theorem sum_pentagonPairWeight_mixedSide_eq_sum_crossingChangePartners
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ G.mixedSidePentagonPairs C (C.withTurnRow t) x z,
        G.pentagonPairWeight C (C.withTurnRow t) R D =
      ∑ F ∈ G.crossingChangeMixedSidePentagonPartners C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F := by
  have hunpaired {F} (hF : F ∈ G.crossingChangeMixedSidePentagonPartners C t x z) :=
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp
      (G.crossingChangeMixedSidePentagonPartners_subset C t x z hF)).1
  refine Finset.sum_bij_of_rel
    (fun D F => D.toRectangleDecomposition = F.toRectangleDecomposition)
    (fun D hD => G.exists_mixedSidePartner C t R hst hX hzx hD)
    (fun D _ E _ F _ hDF hEF =>
      GridPentagonPairDecomposition.toRectangleDecomposition_injective (hDF.trans hEF.symm))
    (fun _ _ F hF F' hF' hDF hDF' =>
      injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
        (hunpaired hF) (hunpaired hF') (hDF.symm.trans hDF'))
    (fun F hF => ((G.mem_crossingChangeMixedSidePentagonPartners C t F).mp hF).2)

/-! ### Disjointness and exhaustion of unpaired composites -/

/-- No unpaired composite is both the recut of a same-side pentagon pair and the underlying
decomposition of a mixed-side pentagon pair: the replaced grid line `b` is a common side of every
mixed-side pair, whereas recutting a same-side pair removes `b` from the common sides. -/
theorem disjoint_crossingChangeSameSidePentagonPartners_crossingChangeMixedSidePentagonPartners
    {x z : GridState n} :
    Disjoint (G.crossingChangeSameSidePentagonPartners C t x z)
      (G.crossingChangeMixedSidePentagonPartners C t x z) := by
  rw [Finset.disjoint_left]
  intro F hS hM
  obtain ⟨-, D, hD, hrecut⟩ := (G.mem_crossingChangeSameSidePentagonPartners C t F).mp hS
  obtain ⟨-, E, -, hEF⟩ := (G.mem_crossingChangeMixedSidePentagonPartners C t F).mp hM
  exact D.finRotate_notMem_commonSideColumns_of_isRecut rfl
    ((G.mem_sameSidePentagonPairs C (C.withTurnRow t) D).mp hD).2 hrecut
    (hEF ▸ E.finRotate_mem_commonSideColumns rfl)

open scoped Classical in
/-- Off the diagonal, if the annulus squares carry no `X`-marking, the unpaired crossing-change
hexagon composites are the union of the same-side and mixed-side pentagon partner sets. -/
theorem crossingChangeUnpairedHexagonComposites_eq_union
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n} (hzx : z ≠ x) :
    G.crossingChangeUnpairedHexagonComposites C t x z =
      G.crossingChangeSameSidePentagonPartners C t x z ∪
        G.crossingChangeMixedSidePentagonPartners C t x z := by
  refine Finset.Subset.antisymm (fun F hF => ?_)
    (Finset.union_subset (G.crossingChangeSameSidePentagonPartners_subset C t x z)
      (G.crossingChangeMixedSidePentagonPartners_subset C t x z))
  obtain ⟨D, hD, hmatch⟩ := exists_pentagonPair_of_mem_crossingChangeUnpairedHexagonComposites
    hX hzx hF
  have hD' : D ∈ G.pentagonPairDecompositions C (C.withTurnRow t) x z := by
    rwa [G.mem_pentagonPairDecompositions C (C.withTurnRow t),
      G.commutationPentagons_def C,
      (G.swapColumns a b).commutationPentagons_def (C.withTurnRow t)]
  rw [Finset.mem_union]
  rcases hmatch with ⟨hside, hrecut⟩ | ⟨hside, hrect⟩
  · exact Or.inl ((G.mem_crossingChangeSameSidePentagonPartners C t F).mpr
      ⟨hF, D, (G.mem_sameSidePentagonPairs C (C.withTurnRow t) D).mpr ⟨hD', hside⟩, hrecut⟩)
  · exact Or.inr ((G.mem_crossingChangeMixedSidePentagonPartners C t F).mpr
      ⟨hF, D, (G.mem_mixedSidePentagonPairs C (C.withTurnRow t) D).mpr ⟨hD', hside⟩, hrect⟩)

/-- **Off-diagonal weight identity for the crossing-change homotopy.** If the turn rows `s` and
`t` differ and the annulus squares carry no `X`-marking, then for distinct grid states `x ≠ z` the
unpaired crossing-change hexagon composites from `x` to `z` have the total polynomial weight of the
products of the commutation-pentagon coefficients of `Φ` (renamed by the column swap) and `Ψ`, over
*every* commutative semiring. -/
theorem sum_crossingChangeUnpairedHexagonComposites_eq_sum_commutationPentagonCoefficient
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hxz : x ≠ z) :
    ∑ D ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
        G.crossingChangeHexagonCompositeWeight C t R D =
      ∑ y : GridState n,
        rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
          (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  classical
  rw [G.crossingChangeUnpairedHexagonComposites_eq_union C t hX hxz.symm,
    Finset.sum_union
      (G.disjoint_crossingChangeSameSidePentagonPartners_crossingChangeMixedSidePentagonPartners
        C t),
    ← G.sum_pentagonPairWeight_sameSide_eq_sum_crossingChangePartners C t R hX hxz.symm,
    ← G.sum_pentagonPairWeight_mixedSide_eq_sum_crossingChangePartners C t R hst hX hxz.symm,
    ← Finset.sum_union
      (G.disjoint_sameSidePentagonPairs_mixedSidePentagonPairs C (C.withTurnRow t)),
    ← G.pentagonPairDecompositions_eq_union C (C.withTurnRow t),
    ← G.sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient
      C (C.withTurnRow t) R]

/-! ### The crossing-change homotopy equations in characteristic two -/

/-- **The crossing-change homotopy equation.** If the turn rows `s = C.turnRow` and `t` differ and
the annulus squares carry no `X`-marking, then over any commutative semiring `R` of characteristic
two, `∂ ∘ H + H ∘ ∂ = w • 1 + Ψ ∘ Φ` on `GC⁻(G)`, where `w` is the annulus weight
`G.crossingChangeAnnulusWeight R C t`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq
    (R : Type*) [CommSemiring R] [CharP R 2] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      G.crossingChangeAnnulusWeight R C t • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired R hst hX).mpr
    (fun _ _ hxz =>
      G.sum_crossingChangeUnpairedHexagonComposites_eq_sum_commutationPentagonCoefficient
        C t R hst hX hxz) c

section Interleaving

variable {G C t}

/-- **The crossing-change homotopy equation for `O_a ∈ columnArc b`.** When the segments of columns
`a` and `b = finRotate n a` interleave with `O_a` on the arc of column `b`, and the crossing-change
maps turn in the rows `s = O_a` and `t = X_b`, the hexagon map `H` satisfies
`∂ ∘ H + H ∘ ∂ = V_b • 1 + Ψ ∘ Φ` over any commutative semiring of characteristic two. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc
    (R : Type*) [CommSemiring R] [CharP R 2]
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b) (hs : C.turnRow = G.O a)
    (ht : t = G.X b) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X b : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired_of_mem_columnArc R h hO hs
    ht).mpr
    (fun _ _ hxz =>
      G.sum_crossingChangeUnpairedHexagonComposites_eq_sum_commutationPentagonCoefficient C t R
        (hs ▸ ht ▸ ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.1)
        (disjoint_crossingChangeAnnulusSquares_XSet_of_mem_columnArc h hO hs ht) hxz) c

/-- **The crossing-change homotopy equation for `O_a ∉ columnArc b`.** When the segments of columns
`a` and `b = finRotate n a` interleave with `O_a` off the arc of column `b`, and the
crossing-change maps turn in the rows `s = X_a` and `t = O_b`, the hexagon map `H` satisfies
`∂ ∘ H + H ∘ ∂ = V_a • 1 + Ψ ∘ Φ` over any commutative semiring of characteristic two. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc
    (R : Type*) [CommSemiring R] [CharP R 2]
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∉ G.columnArc b) (hs : C.turnRow = G.X a)
    (ht : t = G.O b) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X a : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired_of_notMem_columnArc R h hO hs
    ht).mpr
    (fun _ _ hxz =>
      G.sum_crossingChangeUnpairedHexagonComposites_eq_sum_commutationPentagonCoefficient C t R
        (hs ▸ ht ▸ ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.2)
        (disjoint_crossingChangeAnnulusSquares_XSet_of_notMem_columnArc h hO hs ht) hxz) c

end Interleaving

/-- On a cycle `z` of `GC⁻(G)`, the crossing-change round trip `Ψ ∘ Φ` acts as multiplication by
the annulus weight `w` up to the boundary of `H z`. -/
theorem commutationMap_withTurnRow_commutationMap_of_mem_ker
    (R : Type*) [CommSemiring R] [CharP R 2] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {z : GridChainMinus R n} (hz : z ∈ LinearMap.ker (G.unblockedDifferential R)) :
    (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C z) =
      G.crossingChangeAnnulusWeight R C t • z +
        G.unblockedDifferential R (G.crossingChangeHomotopy R C t z) := by
  have h := G.unblockedDifferential_crossingChangeHomotopy_add_eq C t R hst hX z
  rw [LinearMap.mem_ker.mp hz, map_zero, add_zero] at h
  rw [h, ← add_assoc, add_self_eq_zero_of_charTwo (MvPolynomial (Fin n) R) _, zero_add]

end TauCeti.GridDiagram
