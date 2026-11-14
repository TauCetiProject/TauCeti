/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.SameSide
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Mixed
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Unpaired
import TauCeti.Algebra.BigOperators.Finset.Pairing

/-!
# The homotopy equation of a crossing change

Let `C` be a column turn at the columns `a = C.column` and `b = finRotate n a` of a grid diagram
`G`, turning in row `s = C.turnRow`, and let `t ≠ s` be a second row such that the annulus squares
`GridDiagram.crossingChangeAnnulusSquares C t` carry no `X`-marking. Write `Φ : GC⁻(G) → GC⁻(G')`
for the commutation map of `C`, where `G' = G.swapColumns a b`, `Ψ : GC⁻(G') → GC⁻(G)` for the
commutation map of `G'` turning at the same columns in row `t`, and `H : GC⁻(G) → GC⁻(G)` for the
hexagon-counting map `GridDiagram.crossingChangeHomotopy`. Over a commutative semiring of
characteristic two, this file proves the crossing-change homotopy equation

  `∂ ∘ H + H ∘ ∂ = w • · + Ψ ∘ Φ`

with `w = GridDiagram.crossingChangeAnnulusWeight R C t`, and specializes it to the two crossing
change maps of interleaving columns, where `w = V_b` when `O_a` lies on the arc of column `b` and
`w = V_a` when it does not.

By the diagonal, disjoint-side and recut cancellations of `Homotopy.Recut`, the equation reduces
to matching the off-diagonal unpaired hexagon composites
(`GridDiagram.crossingChangeUnpairedHexagonComposites`) with the pairs of pentagons counted by
`Ψ ∘ Φ`. That off-diagonal matching holds over *every* commutative semiring, with no
characteristic-two assumption:

* Counted pentagon pairs whose two pentagons turn on the same side of the replaced grid line `b`
  match bijectively and weight-preservingly with their recut image among the unpaired composites
  (`GridDiagram.sum_crossingChangePentagonPairWeight_sameSide_eq_sum_partners`, from
  `Homotopy.SameSide`).
* Counted pentagon pairs turning on opposite sides of `b` match bijectively and
  weight-preservingly with the unpaired composites sharing their underlying rectangles
  (`GridDiagram.sum_crossingChangePentagonPairWeight_mixedSide_eq_sum_partners`, from
  `Homotopy.Mixed`).
* The two partner images are disjoint because `b` is a common side column in the mixed-side image
  and never a common side column in the same-side recut image
  (`GridDiagram.disjoint_crossingChangeSameSidePentagonPartners_mixedSide`), and by
  `Homotopy.Unpaired` their union exhausts all off-diagonal unpaired composites
  (`GridDiagram.crossingChangeSameSidePentagonPartners_union_mixedSide`).

## Main definitions

* `TauCeti.GridDiagram.crossingChangePentagonPairDecompositions` and
  `TauCeti.GridDiagram.crossingChangePentagonPairWeight`: the counted pentagon pairs in the round
  trip `Ψ ∘ Φ` and their polynomial weights.
* `TauCeti.GridDiagram.crossingChangeSameSidePentagonPairs`,
  `TauCeti.GridDiagram.crossingChangeSameSidePentagonPartners`,
  `TauCeti.GridDiagram.crossingChangeMixedSidePentagonPairs`,
  `TauCeti.GridDiagram.crossingChangeMixedSidePentagonPartners`: the same-side and mixed-side
  pentagon-pair families and their partner images among the unpaired hexagon composites.

## Main results

* `TauCeti.GridDiagram.sum_crossingChangeHexagonCompositeWeight_unpaired_eq`: off the diagonal,
  for `s ≠ t` and an `X`-free annulus, the unpaired hexagon composites have the same total weight
  as the round-trip pentagon coefficient products over every commutative semiring.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq`: the homotopy equation
  `∂ ∘ H + H ∘ ∂ = w • · + Ψ ∘ Φ` in characteristic two.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc` and
  `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc`:
  the crossing-change homotopy equations for interleaving columns, with `w = V_b` and `w = V_a`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 6.1.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3.
-/

public section

namespace TauCeti

namespace GridPentagonPairDecomposition

/-- When both pentagons of a pair turn at column `a`, the replaced grid line `finRotate n a` is a
common side column of their two underlying rectangles. -/
theorem finRotate_mem_commonSideColumns {n : ℕ} {a s t : Fin n} {x z : GridState n}
    (D : GridPentagonPairDecomposition a s a t x z) :
    finRotate n a ∈ D.toRectangleDecomposition.commonSideColumns := by
  rcases D with ⟨m, P | P, Q | Q⟩
  · simp [P.right_eq, Q.right_eq]
  · simp [P.right_eq, Q.left_eq]
  · simp [P.left_eq, Q.right_eq]
  · simp [P.left_eq, Q.left_eq]

end GridPentagonPairDecomposition

namespace GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Pentagon pairs of the round trip -/

/-- The pairs of pentagons counted in the round trip `Ψ ∘ Φ` of a column turn `C` followed by the
turn `C.withTurnRow t` on the column-swapped diagram. -/
noncomputable def crossingChangePentagonPairDecompositions (x z : GridState n) :
    Finset (GridPentagonPairDecomposition a C.turnRow a t x z) :=
  GridTwoStepDecomposition.decompositionsOf
    (fun x y => (G.pentagons C x y).disjSum (G.initialPentagons C x y))
    (fun y z => ((G.swapColumns a b).pentagons (C.withTurnRow t) y z).disjSum
      ((G.swapColumns a b).initialPentagons (C.withTurnRow t) y z))
    x z

/-- A pentagon pair belongs to the round-trip family exactly when both its pentagons are
counted. -/
@[simp]
theorem mem_crossingChangePentagonPairDecompositions {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    D ∈ G.crossingChangePentagonPairDecompositions C t x z ↔
      D.first ∈ (G.pentagons C x D.middle).disjSum (G.initialPentagons C x D.middle) ∧
        D.second ∈ ((G.swapColumns a b).pentagons (C.withTurnRow t) D.middle z).disjSum
          ((G.swapColumns a b).initialPentagons (C.withTurnRow t) D.middle z) := by
  classical
  simp [crossingChangePentagonPairDecompositions]

/-- Both underlying rectangles of a counted crossing-change pentagon pair are empty. -/
theorem isEmpty_of_mem_crossingChangePentagonPairDecompositions {x z : GridState n}
    {D : GridPentagonPairDecomposition a C.turnRow a t x z}
    (hD : D ∈ G.crossingChangePentagonPairDecompositions C t x z) :
    D.toRectangleDecomposition.first.IsEmpty ∧ D.toRectangleDecomposition.second.IsEmpty := by
  obtain ⟨hP, hQ⟩ := (G.mem_crossingChangePentagonPairDecompositions C t D).mp hD
  rcases D with ⟨m, P | P, Q | Q⟩ <;>
    simp only [Finset.inl_mem_disjSum, Finset.inr_mem_disjSum,
      G.mem_pentagons, G.mem_initialPentagons,
      (G.swapColumns a b).mem_pentagons (C := C.withTurnRow t),
      (G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t)] at hP hQ <;>
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr] using ⟨hP.1, hQ.1⟩

/-- The polynomial weight of a pentagon pair in `Ψ ∘ Φ`: the weight of the forward pentagon,
renamed by the swap of `a` and `b`, times the weight of the returning pentagon on
`G.swapColumns a b`. -/
noncomputable def crossingChangePentagonPairWeight (R : Type*) [CommSemiring R]
    {x z : GridState n} (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    MvPolynomial (Fin n) R :=
  rename (Equiv.swap a b) (D.first.elim (G.pentagonWeight R C) (G.initialPentagonWeight R C)) *
    D.second.elim ((G.swapColumns a b).pentagonWeight R (C.withTurnRow t))
      ((G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t))

/-- Explicit formula for the weight of a crossing-change pentagon pair. -/
theorem crossingChangePentagonPairWeight_def (R : Type*) [CommSemiring R]
    {x z : GridState n} (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    G.crossingChangePentagonPairWeight C t R D =
      rename (Equiv.swap a b) (D.first.elim (G.pentagonWeight R C) (G.initialPentagonWeight R C)) *
        D.second.elim ((G.swapColumns a b).pentagonWeight R (C.withTurnRow t))
          ((G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t)) :=
  (rfl)

/-- The matrix product of the renamed forward pentagon coefficients and the returning pentagon
coefficients equals the sum of weights over all counted pentagon pairs. -/
theorem sum_rename_commutationPentagonCoefficient_mul_eq_sum_crossingChangePentagonPairs
    (R : Type*) [CommSemiring R] (x z : GridState n) :
    ∑ y : GridState n,
        rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
          (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z =
      ∑ D ∈ G.crossingChangePentagonPairDecompositions C t x z,
        G.crossingChangePentagonPairWeight C t R D := by
  have hcoeff {H : GridDiagram n} (C' : ColumnTurn n) (u v : GridState n) :
      H.commutationPentagonCoefficient R C' u v =
        ∑ P ∈ (H.pentagons C' u v).disjSum (H.initialPentagons C' u v),
          P.elim (H.pentagonWeight R C') (H.initialPentagonWeight R C') := by
    rw [H.commutationPentagonCoefficient_def R C', H.pentagonCoefficient_def R C' u v,
      H.initialPentagonCoefficient_def R C' u v, Finset.sum_disjSum]
    rfl
  simp_rw [hcoeff C, hcoeff (C.withTurnRow t), map_sum, Finset.sum_mul_sum]
  exact (GridTwoStepDecomposition.sum_decompositionsOf
    (fun x y => (G.pentagons C x y).disjSum (G.initialPentagons C x y))
    (fun y z => ((G.swapColumns a b).pentagons (C.withTurnRow t) y z).disjSum
      ((G.swapColumns a b).initialPentagons (C.withTurnRow t) y z))
    (fun _ P Q => rename (Equiv.swap a b) (P.elim (G.pentagonWeight R C)
      (G.initialPentagonWeight R C)) *
        Q.elim ((G.swapColumns a b).pentagonWeight R (C.withTurnRow t))
          ((G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t)))).symm

/-! ### Same-side pentagon pairs and their recut partners -/

/-- Counted crossing-change pentagon pairs whose two pentagons turn on the same side of `b`. -/
noncomputable def crossingChangeSameSidePentagonPairs (x z : GridState n) :
    Finset (GridPentagonPairDecomposition a C.turnRow a t x z) :=
  (G.crossingChangePentagonPairDecompositions C t x z).filter fun D =>
    D.first.isLeft = D.second.isLeft

/-- Membership in the same-side family is countedness together with equal turn-side indicators. -/
@[simp]
theorem mem_crossingChangeSameSidePentagonPairs {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    D ∈ G.crossingChangeSameSidePentagonPairs C t x z ↔
      D ∈ G.crossingChangePentagonPairDecompositions C t x z ∧
        D.first.isLeft = D.second.isLeft := by
  simp only [crossingChangeSameSidePentagonPairs, Finset.mem_filter]

/-- Every counted same-side pentagon pair belongs to the full pentagon-pair family. -/
theorem crossingChangeSameSidePentagonPairs_subset (x z : GridState n) :
    G.crossingChangeSameSidePentagonPairs C t x z ⊆
      G.crossingChangePentagonPairDecompositions C t x z :=
  fun D hD => ((G.mem_crossingChangeSameSidePentagonPairs C t D).mp hD).1

/-- The unpaired crossing-change hexagon composites obtained by recutting a counted same-side
pentagon pair. -/
noncomputable def crossingChangeSameSidePentagonPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.crossingChangeSameSidePentagonPairs C t x z,
      D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition

/-- Same-side partners are the unpaired composites recutting a counted same-side pair. -/
@[simp]
theorem mem_crossingChangeSameSidePentagonPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeSameSidePentagonPartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.crossingChangeSameSidePentagonPairs C t x z,
          D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition := by
  classical
  simp only [crossingChangeSameSidePentagonPartners, Finset.mem_filter]

/-- Every same-side partner is an unpaired hexagon composite. -/
theorem crossingChangeSameSidePentagonPartners_subset (x z : GridState n) :
    G.crossingChangeSameSidePentagonPartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeSameSidePentagonPartners C t F).mp hF).1

private theorem exists_crossingChangeSameSidePartner (R : Type*) [CommSemiring R]
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x)
    {D : GridPentagonPairDecomposition a C.turnRow a t x z}
    (hD : D ∈ G.crossingChangeSameSidePentagonPairs C t x z) :
    ∃ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
      D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          G.crossingChangePentagonPairWeight C t R D := by
  obtain ⟨hD, hside⟩ := (G.mem_crossingChangeSameSidePentagonPairs C t D).mp hD
  obtain ⟨hP, hQ⟩ := (G.mem_crossingChangePentagonPairDecompositions C t D).mp hD
  rcases D with ⟨m, P | P, Q | Q⟩
  · obtain ⟨⟨F, ⟨hF, hrec⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair R hX P Q
        (Finset.inl_mem_disjSum.mp hP) (Finset.inl_mem_disjSum.mp hQ) hzx
    refine ⟨F, hF, ?_, hw F hF hrec⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl] using hrec
  · simp at hside
  · simp at hside
  · obtain ⟨⟨F, ⟨hF, hrec⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair R hX P Q
        (Finset.inr_mem_disjSum.mp hP) (Finset.inr_mem_disjSum.mp hQ) hzx
    refine ⟨F, hF, ?_, hw F hF hrec⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hrec

/-- Off the diagonal, when the annulus carries no `X`-marking, the counted same-side pentagon
pairs and their recut partners have equal total polynomial weight over every commutative
semiring. -/
theorem sum_crossingChangePentagonPairWeight_sameSide_eq_sum_partners
    (R : Type*) [CommSemiring R] (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ G.crossingChangeSameSidePentagonPairs C t x z,
        G.crossingChangePentagonPairWeight C t R D =
      ∑ F ∈ G.crossingChangeSameSidePentagonPartners C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F := by
  have hcounted {F} (hF : F ∈ G.crossingChangeSameSidePentagonPartners C t x z) :=
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp
      (G.crossingChangeSameSidePentagonPartners_subset C t x z hF)).1
  refine Finset.sum_bij_of_rel
    (fun D F => D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition)
    (fun D hD => ?_) (fun D hD E hE F _ hDF hEF => ?_) (fun D hD F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ((G.mem_crossingChangeSameSidePentagonPartners C t F).mp hF).2)
  · obtain ⟨F, hF, hrec, hw⟩ := G.exists_crossingChangeSameSidePartner C t R hX hzx hD
    exact ⟨F, (G.mem_crossingChangeSameSidePentagonPartners C t F).mpr ⟨hF, D, hD, hrec⟩,
      hrec, hw.symm⟩
  · obtain ⟨hfD, hsD⟩ := G.isEmpty_of_mem_crossingChangePentagonPairDecompositions C t
      (G.crossingChangeSameSidePentagonPairs_subset C t x z hD)
    obtain ⟨hfE, hsE⟩ := G.isEmpty_of_mem_crossingChangePentagonPairDecompositions C t
      (G.crossingChangeSameSidePentagonPairs_subset C t x z hE)
    exact GridPentagonPairDecomposition.toRectangleDecomposition_injective
      (hDF.eq_of_isRecut hEF hfD hsD hfE hsE)
  · obtain ⟨hf, hs⟩ := G.isEmpty_of_mem_crossingChangePentagonPairDecompositions C t
      (G.crossingChangeSameSidePentagonPairs_subset C t x z hD)
    exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hcounted hF) (hcounted hF')
      ((D.toRectangleDecomposition.existsUnique_isRecut
        (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hDF) hf hs).unique hDF hDF')

/-! ### Mixed-side pentagon pairs and their partners -/

/-- Counted crossing-change pentagon pairs whose two pentagons turn on opposite sides of `b`. -/
noncomputable def crossingChangeMixedSidePentagonPairs (x z : GridState n) :
    Finset (GridPentagonPairDecomposition a C.turnRow a t x z) :=
  (G.crossingChangePentagonPairDecompositions C t x z).filter fun D =>
    D.first.isLeft ≠ D.second.isLeft

/-- Membership in the mixed-side family is countedness together with distinct turn-side
indicators. -/
@[simp]
theorem mem_crossingChangeMixedSidePentagonPairs {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    D ∈ G.crossingChangeMixedSidePentagonPairs C t x z ↔
      D ∈ G.crossingChangePentagonPairDecompositions C t x z ∧
        D.first.isLeft ≠ D.second.isLeft := by
  simp only [crossingChangeMixedSidePentagonPairs, Finset.mem_filter]

/-- Every counted mixed-side pentagon pair belongs to the full pentagon-pair family. -/
theorem crossingChangeMixedSidePentagonPairs_subset (x z : GridState n) :
    G.crossingChangeMixedSidePentagonPairs C t x z ⊆
      G.crossingChangePentagonPairDecompositions C t x z :=
  fun D hD => ((G.mem_crossingChangeMixedSidePentagonPairs C t D).mp hD).1

/-- The unpaired crossing-change hexagon composites sharing their underlying rectangle
decomposition with a counted mixed-side pentagon pair. -/
noncomputable def crossingChangeMixedSidePentagonPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.crossingChangeMixedSidePentagonPairs C t x z,
      D.toRectangleDecomposition = F.toRectangleDecomposition

/-- Mixed-side partners are the unpaired composites sharing their underlying rectangles with a
counted mixed-side pair. -/
@[simp]
theorem mem_crossingChangeMixedSidePentagonPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeMixedSidePentagonPartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.crossingChangeMixedSidePentagonPairs C t x z,
          D.toRectangleDecomposition = F.toRectangleDecomposition := by
  classical
  simp only [crossingChangeMixedSidePentagonPartners, Finset.mem_filter]

/-- Every mixed-side partner is an unpaired hexagon composite. -/
theorem crossingChangeMixedSidePentagonPartners_subset (x z : GridState n) :
    G.crossingChangeMixedSidePentagonPartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeMixedSidePentagonPartners C t F).mp hF).1

private theorem exists_crossingChangeMixedSidePartner (R : Type*) [CommSemiring R]
    (hst : C.turnRow ≠ t) (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x)
    {D : GridPentagonPairDecomposition a C.turnRow a t x z}
    (hD : D ∈ G.crossingChangeMixedSidePentagonPairs C t x z) :
    ∃ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
      D.toRectangleDecomposition = F.toRectangleDecomposition ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          G.crossingChangePentagonPairWeight C t R D := by
  obtain ⟨hD, hside⟩ := (G.mem_crossingChangeMixedSidePentagonPairs C t D).mp hD
  obtain ⟨hP, hQ⟩ := (G.mem_crossingChangePentagonPairDecompositions C t D).mp hD
  rcases D with ⟨m, P | P, Q | Q⟩
  · simp at hside
  · obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalInitialPentagonPair
        R hst hX P Q (Finset.inl_mem_disjSum.mp hP) (Finset.inr_mem_disjSum.mp hQ) hzx
    refine ⟨F, hF, ?_, hw⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hFD.symm
  · obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialTerminalPentagonPair
        R hst hX P Q (Finset.inr_mem_disjSum.mp hP) (Finset.inl_mem_disjSum.mp hQ) hzx
    refine ⟨F, hF, ?_, hw⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hFD.symm
  · simp at hside

/-- Off the diagonal, for distinct turn rows and an `X`-free annulus, the counted mixed-side
pentagon pairs and their partners have equal total polynomial weight over every commutative
semiring. -/
theorem sum_crossingChangePentagonPairWeight_mixedSide_eq_sum_partners
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ G.crossingChangeMixedSidePentagonPairs C t x z,
        G.crossingChangePentagonPairWeight C t R D =
      ∑ F ∈ G.crossingChangeMixedSidePentagonPartners C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F := by
  have hcounted {F} (hF : F ∈ G.crossingChangeMixedSidePentagonPartners C t x z) :=
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp
      (G.crossingChangeMixedSidePentagonPartners_subset C t x z hF)).1
  refine Finset.sum_bij_of_rel
    (fun D F => D.toRectangleDecomposition = F.toRectangleDecomposition)
    (fun D hD => ?_)
    (fun _ _ _ _ _ _ hDF hEF =>
      GridPentagonPairDecomposition.toRectangleDecomposition_injective (hDF.trans hEF.symm))
    (fun _ _ F hF F' hF' hDF hDF' =>
      injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
        (hcounted hF) (hcounted hF') (hDF.symm.trans hDF'))
    (fun F hF => ((G.mem_crossingChangeMixedSidePentagonPartners C t F).mp hF).2)
  obtain ⟨F, hF, hDF, hw⟩ := G.exists_crossingChangeMixedSidePartner C t R hst hX hzx hD
  exact ⟨F, (G.mem_crossingChangeMixedSidePentagonPartners C t F).mpr ⟨hF, D, hD, hDF⟩,
    hDF, hw.symm⟩

/-! ### Partitioning the unpaired composites and proving the homotopy equation -/

/-- No unpaired composite belongs to both the same-side recut image and the mixed-side image:
the replaced grid line `b` is a common side column of the latter and never of the former. -/
theorem disjoint_crossingChangeSameSidePentagonPartners_mixedSide {x z : GridState n} :
    Disjoint (G.crossingChangeSameSidePentagonPartners C t x z)
      (G.crossingChangeMixedSidePentagonPartners C t x z) := by
  rw [Finset.disjoint_left]
  intro F hS hM
  obtain ⟨-, D, hD, hrecut⟩ := (G.mem_crossingChangeSameSidePentagonPartners C t F).mp hS
  obtain ⟨-, E, -, hEF⟩ := (G.mem_crossingChangeMixedSidePentagonPartners C t F).mp hM
  have hb : b ∈ F.toRectangleDecomposition.commonSideColumns :=
    hEF ▸ E.finRotate_mem_commonSideColumns
  obtain ⟨-, hside⟩ := (G.mem_crossingChangeSameSidePentagonPairs C t D).mp hD
  rcases D with ⟨m, P | P, Q | Q⟩
  · have hcommon := hrecut.isRecutOfRightEqRight (by
      simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl, P.right_eq, Q.right_eq])
    apply hcommon.first_right_notMem_commonSideColumns
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl, P.right_eq] using hb
  · simp at hside
  · simp at hside
  · have hcommon := hrecut.isRecutOfLeftEqLeft (by
      simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr, P.left_eq, Q.left_eq])
    apply hcommon.first_left_notMem_commonSideColumns
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr, P.left_eq] using hb

open scoped Classical in
/-- Off the diagonal, when the annulus carries no `X`-marking, the same-side and mixed-side
partner images exhaust all unpaired crossing-change hexagon composites. -/
theorem crossingChangeSameSidePentagonPartners_union_mixedSide
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    G.crossingChangeSameSidePentagonPartners C t x z ∪
        G.crossingChangeMixedSidePentagonPartners C t x z =
      G.crossingChangeUnpairedHexagonComposites C t x z := by
  refine Finset.Subset.antisymm
    (Finset.union_subset (G.crossingChangeSameSidePentagonPartners_subset C t x z)
      (G.crossingChangeMixedSidePentagonPartners_subset C t x z))
    fun F hF => ?_
  rw [Finset.mem_union, mem_crossingChangeSameSidePentagonPartners,
    mem_crossingChangeMixedSidePentagonPartners]
  obtain ⟨D, hD, ⟨hside, hrec⟩ | ⟨hside, hrec⟩⟩ :=
    exists_pentagonPair_of_mem_crossingChangeUnpairedHexagonComposites hX hzx hF
  · exact Or.inl ⟨hF, D, (G.mem_crossingChangeSameSidePentagonPairs C t D).mpr
      ⟨(G.mem_crossingChangePentagonPairDecompositions C t D).mpr hD, hside⟩, hrec⟩
  · exact Or.inr ⟨hF, D, (G.mem_crossingChangeMixedSidePentagonPairs C t D).mpr
      ⟨(G.mem_crossingChangePentagonPairDecompositions C t D).mpr hD, hside⟩, hrec⟩

/-- **Off-diagonal matching of the crossing-change homotopy equation.** For distinct turn rows,
an `X`-free annulus, and distinct grid states `x ≠ z`, the unpaired crossing-change hexagon
composites from `x` to `z` have the same total polynomial weight as the round-trip pentagon
coefficient products, over *every* commutative semiring. -/
theorem sum_crossingChangeHexagonCompositeWeight_unpaired_eq
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hxz : x ≠ z) :
    ∑ D ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
        G.crossingChangeHexagonCompositeWeight C t R D =
      ∑ y : GridState n,
        rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
          (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  classical
  have hdisjPairs : Disjoint (G.crossingChangeSameSidePentagonPairs C t x z)
      (G.crossingChangeMixedSidePentagonPairs C t x z) :=
    Finset.disjoint_filter.mpr fun _ _ h₁ h₂ => h₂ h₁
  have hunionPairs : G.crossingChangeSameSidePentagonPairs C t x z ∪
        G.crossingChangeMixedSidePentagonPairs C t x z =
      G.crossingChangePentagonPairDecompositions C t x z := by
    ext D
    simp only [Finset.mem_union, mem_crossingChangeSameSidePentagonPairs,
      mem_crossingChangeMixedSidePentagonPairs]
    tauto
  rw [← G.crossingChangeSameSidePentagonPartners_union_mixedSide C t hX hxz.symm,
    Finset.sum_union (G.disjoint_crossingChangeSameSidePentagonPartners_mixedSide C t),
    ← G.sum_crossingChangePentagonPairWeight_sameSide_eq_sum_partners C t R hX hxz.symm,
    ← G.sum_crossingChangePentagonPairWeight_mixedSide_eq_sum_partners C t R hst hX hxz.symm,
    ← Finset.sum_union hdisjPairs, hunionPairs,
    G.sum_rename_commutationPentagonCoefficient_mul_eq_sum_crossingChangePentagonPairs C t R]

/-- **The crossing-change homotopy equation.** If the turn rows `C.turnRow` and `t` differ and the
annulus squares carry no `X`-marking, then over any commutative semiring of characteristic two,
`∂ ∘ H + H ∘ ∂ = w • · + Ψ ∘ Φ` with `w = crossingChangeAnnulusWeight R C t`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq
    (R : Type*) [CommSemiring R] [CharP R 2] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      G.crossingChangeAnnulusWeight R C t • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired R hst hX).mpr
    (fun _ _ hxz => G.sum_crossingChangeHexagonCompositeWeight_unpaired_eq C t R hst hX hxz) c

/-- **The crossing-change homotopy equation**, for markings in the cyclic order
`O_b, O_a, X_b, X_a`: when the segments of `a` and `b = finRotate n a` interleave with `O_a` on the
arc of column `b`, and the crossing change maps turn in the rows of `O_a` and `X_b`,
`∂ ∘ H + H ∘ ∂ = V_b • · + Ψ ∘ Φ` in characteristic two. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc
    (R : Type*) [CommSemiring R] [CharP R 2]
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b)
    (hs : C.turnRow = G.O a) (ht : t = G.X b) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X b : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired_of_mem_columnArc R
    h hO hs ht).mpr
    (fun _ _ hxz => G.sum_crossingChangeHexagonCompositeWeight_unpaired_eq C t R
      (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.1)
      (disjoint_crossingChangeAnnulusSquares_XSet_of_mem_columnArc h hO hs ht) hxz) c

/-- **The crossing-change homotopy equation**, for markings in the cyclic order
`O_b, X_a, X_b, O_a`: when the segments of `a` and `b = finRotate n a` interleave with `O_a` off
the arc of column `b`, and the crossing change maps turn in the rows of `X_a` and `O_b`,
`∂ ∘ H + H ∘ ∂ = V_a • · + Ψ ∘ Φ` in characteristic two. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc
    (R : Type*) [CommSemiring R] [CharP R 2]
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∉ G.columnArc b)
    (hs : C.turnRow = G.X a) (ht : t = G.O b) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X a : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired_of_notMem_columnArc R
    h hO hs ht).mpr
    (fun _ _ hxz => G.sum_crossingChangeHexagonCompositeWeight_unpaired_eq C t R
      (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.2)
      (disjoint_crossingChangeAnnulusSquares_XSet_of_notMem_columnArc h hO hs ht) hxz) c

end GridDiagram

end TauCeti
