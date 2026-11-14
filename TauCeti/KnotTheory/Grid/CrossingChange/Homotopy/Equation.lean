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
the unpaired hexagon composites and the pentagon-pair products of `Ψ ∘ Φ`. That off-diagonal
identity holds over *every* commutative semiring: same-side pentagon pairs match bijectively by
recutting (`Homotopy.SameSide`), mixed-side pentagon pairs match bijectively by sharing the same
two rectangles (`Homotopy.Mixed`, unifying both mixed-side branches alongside
`Homotopy.TerminalInitialSum`), the two partner images are disjoint because the replaced grid line
is a common side of mixed-side pairs and never of a same-side recut, and every unpaired composite
arises from one of the two families (`Homotopy.Unpaired`).

## Main definitions

* `TauCeti.GridDiagram.crossingChangePentagonPairs`,
  `TauCeti.GridDiagram.crossingChangePentagonPairWeight`: the counted pentagon pairs of `Ψ ∘ Φ` and
  their polynomial weights.
* `TauCeti.GridDiagram.crossingChangeSameSidePentagonPairs`,
  `TauCeti.GridDiagram.crossingChangeMixedSidePentagonPairs`: the split into same-side and
  mixed-side turn pairs.
* `TauCeti.GridDiagram.crossingChangeSameSidePentagonPartners`,
  `TauCeti.GridDiagram.crossingChangeMixedSidePentagonPartners`: their respective images among the
  unpaired hexagon composites.

## Main results

* `TauCeti.GridDiagram.crossingChangeUnpairedHexagonComposites_eq_union`: off the diagonal, the
  unpaired hexagon composites are the disjoint union of the same-side and mixed-side partner sets.
* `TauCeti.GridDiagram.sum_crossingChangeUnpairedHexagonComposites_eq_sum_pentagonCoefficient`: off
  the diagonal, the unpaired composites have the total weight of the pentagon coefficient products
  over every commutative semiring.
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

/-! ### Pentagon pairs of a crossing change round trip -/

/-- The counted pentagon pairs in the composite `Ψ ∘ Φ`, consisting of a counted pentagon of `G`
turning at `C` followed by a counted pentagon of `G.swapColumns a b` turning at
`C.withTurnRow t`. -/
noncomputable def crossingChangePentagonPairs (x z : GridState n) :
    Finset (GridPentagonPairDecomposition a C.turnRow a t x z) :=
  GridTwoStepDecomposition.decompositionsOf
    (fun x y => (G.pentagons C x y).disjSum (G.initialPentagons C x y))
    (fun y z => ((G.swapColumns a b).pentagons (C.withTurnRow t) y z).disjSum
      ((G.swapColumns a b).initialPentagons (C.withTurnRow t) y z))
    x z

/-- A pentagon pair is counted in `Ψ ∘ Φ` exactly when both of its pentagons are counted. -/
@[simp]
theorem mem_crossingChangePentagonPairs {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    D ∈ G.crossingChangePentagonPairs C t x z ↔
      D.first ∈ (G.pentagons C x D.middle).disjSum (G.initialPentagons C x D.middle) ∧
        D.second ∈ ((G.swapColumns a b).pentagons (C.withTurnRow t) D.middle z).disjSum
          ((G.swapColumns a b).initialPentagons (C.withTurnRow t) D.middle z) := by
  rw [crossingChangePentagonPairs, GridTwoStepDecomposition.mem_decompositionsOf]

/-- Both underlying rectangles of a counted crossing-change pentagon pair are empty. -/
theorem isEmpty_of_mem_crossingChangePentagonPairs {x z : GridState n}
    {D : GridPentagonPairDecomposition a C.turnRow a t x z}
    (hD : D ∈ G.crossingChangePentagonPairs C t x z) :
    D.toRectangleDecomposition.first.IsEmpty ∧ D.toRectangleDecomposition.second.IsEmpty := by
  obtain ⟨hP, hQ⟩ := (G.mem_crossingChangePentagonPairs C t D).mp hD
  have hp : D.toRectangleDecomposition.first.IsEmpty := by
    rcases D with ⟨m, P | P, Q⟩
    · simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl] using
        ((G.mem_pentagons P).mp (Finset.inl_mem_disjSum.mp hP)).1
    · simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using
        ((G.mem_initialPentagons P).mp (Finset.inr_mem_disjSum.mp hP)).1
  have hq : D.toRectangleDecomposition.second.IsEmpty := by
    rcases D with ⟨m, P, Q | Q⟩
    · simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl] using
        (((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) Q).mp
          (Finset.inl_mem_disjSum.mp hQ)).1
    · simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using
        (((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) Q).mp
          (Finset.inr_mem_disjSum.mp hQ)).1
  exact ⟨hp, hq⟩

/-- The polynomial weight of a crossing-change pentagon pair: the forward pentagon weight renamed
along the column swap, multiplied by the second pentagon weight on `G.swapColumns a b`. -/
noncomputable def crossingChangePentagonPairWeight (R : Type*) [CommSemiring R]
    {x z : GridState n} (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    MvPolynomial (Fin n) R :=
  rename (Equiv.swap a b)
      (D.first.elim (G.pentagonWeight R C) (G.initialPentagonWeight R C)) *
    D.second.elim ((G.swapColumns a b).pentagonWeight R (C.withTurnRow t))
      ((G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t))

/-- Explicit formula for the weight of a crossing-change pentagon pair. -/
theorem crossingChangePentagonPairWeight_def (R : Type*) [CommSemiring R]
    {x z : GridState n} (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    G.crossingChangePentagonPairWeight C t R D =
      rename (Equiv.swap a b)
          (D.first.elim (G.pentagonWeight R C) (G.initialPentagonWeight R C)) *
        D.second.elim ((G.swapColumns a b).pentagonWeight R (C.withTurnRow t))
          ((G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t)) :=
  (rfl)

/-- The matrix product of the pentagon coefficients of `Φ` (renamed by the column swap) and `Ψ` is
the sum of the weights of the counted crossing-change pentagon pairs. -/
theorem sum_rename_commutationPentagonCoefficient_mul_withTurnRow
    (R : Type*) [CommSemiring R] (x z : GridState n) :
    ∑ y : GridState n,
        rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
          (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z =
      ∑ D ∈ G.crossingChangePentagonPairs C t x z,
        G.crossingChangePentagonPairWeight C t R D := by
  have hcoeff (G' : GridDiagram n) (T : ColumnTurn n) (u v : GridState n) :
      G'.commutationPentagonCoefficient R T u v =
        ∑ P ∈ (G'.pentagons T u v).disjSum (G'.initialPentagons T u v),
          P.elim (G'.pentagonWeight R T) (G'.initialPentagonWeight R T) := by
    rw [G'.commutationPentagonCoefficient_def R T, G'.pentagonCoefficient_def R T u v,
      G'.initialPentagonCoefficient_def R T u v, Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr]
  simp_rw [hcoeff G C, hcoeff (G.swapColumns a b) (C.withTurnRow t), map_sum, Finset.sum_mul_sum]
  exact (GridTwoStepDecomposition.sum_decompositionsOf
    (fun x y => (G.pentagons C x y).disjSum (G.initialPentagons C x y))
    (fun y z => ((G.swapColumns a b).pentagons (C.withTurnRow t) y z).disjSum
      ((G.swapColumns a b).initialPentagons (C.withTurnRow t) y z))
    (fun _ P Q => rename (Equiv.swap a b) (P.elim (G.pentagonWeight R C)
      (G.initialPentagonWeight R C)) * Q.elim ((G.swapColumns a b).pentagonWeight R
        (C.withTurnRow t)) ((G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t)))).symm

/-! ### Same-side and mixed-side partner matchings -/

/-- The counted crossing-change pentagon pairs whose two pentagons turn on the same side of the
replaced grid line. -/
noncomputable def crossingChangeSameSidePentagonPairs (x z : GridState n) :
    Finset (GridPentagonPairDecomposition a C.turnRow a t x z) :=
  (G.crossingChangePentagonPairs C t x z).filter fun D => D.first.isLeft = D.second.isLeft

/-- Membership in `crossingChangeSameSidePentagonPairs` is countedness together with equal
turn-side indicators. -/
@[simp]
theorem mem_crossingChangeSameSidePentagonPairs {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    D ∈ G.crossingChangeSameSidePentagonPairs C t x z ↔
      D ∈ G.crossingChangePentagonPairs C t x z ∧ D.first.isLeft = D.second.isLeft := by
  simp only [crossingChangeSameSidePentagonPairs, Finset.mem_filter]

/-- Every same-side pair is a counted crossing-change pentagon pair. -/
theorem crossingChangeSameSidePentagonPairs_subset (x z : GridState n) :
    G.crossingChangeSameSidePentagonPairs C t x z ⊆ G.crossingChangePentagonPairs C t x z :=
  Finset.filter_subset _ _

/-- The counted crossing-change pentagon pairs whose two pentagons turn on opposite sides of the
replaced grid line. -/
noncomputable def crossingChangeMixedSidePentagonPairs (x z : GridState n) :
    Finset (GridPentagonPairDecomposition a C.turnRow a t x z) :=
  (G.crossingChangePentagonPairs C t x z).filter fun D => D.first.isLeft ≠ D.second.isLeft

/-- Membership in `crossingChangeMixedSidePentagonPairs` is countedness together with distinct
turn-side indicators. -/
@[simp]
theorem mem_crossingChangeMixedSidePentagonPairs {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    D ∈ G.crossingChangeMixedSidePentagonPairs C t x z ↔
      D ∈ G.crossingChangePentagonPairs C t x z ∧ D.first.isLeft ≠ D.second.isLeft := by
  simp only [crossingChangeMixedSidePentagonPairs, Finset.mem_filter]

/-- Every mixed-side pair is a counted crossing-change pentagon pair. -/
theorem crossingChangeMixedSidePentagonPairs_subset (x z : GridState n) :
    G.crossingChangeMixedSidePentagonPairs C t x z ⊆ G.crossingChangePentagonPairs C t x z :=
  Finset.filter_subset _ _

/-- The unpaired crossing-change hexagon composites obtained by recutting counted same-side
pentagon pairs. -/
noncomputable def crossingChangeSameSidePentagonPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.crossingChangeSameSidePentagonPairs C t x z,
      D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition

/-- Membership in `crossingChangeSameSidePentagonPartners` characterizes the recut image of counted
same-side pentagon pairs. -/
@[simp]
theorem mem_crossingChangeSameSidePentagonPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeSameSidePentagonPartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.crossingChangeSameSidePentagonPairs C t x z,
          D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition := by
  classical
  simp only [crossingChangeSameSidePentagonPartners, Finset.mem_filter]

/-- Every same-side partner is an unpaired crossing-change hexagon composite. -/
theorem crossingChangeSameSidePentagonPartners_subset (x z : GridState n) :
    G.crossingChangeSameSidePentagonPartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeSameSidePentagonPartners C t F).mp hF).1

/-- The unpaired crossing-change hexagon composites sharing their two underlying rectangles with a
counted mixed-side pentagon pair. -/
noncomputable def crossingChangeMixedSidePentagonPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.crossingChangeMixedSidePentagonPairs C t x z,
      D.toRectangleDecomposition = F.toRectangleDecomposition

/-- Membership in `crossingChangeMixedSidePentagonPartners` characterizes the rectangle-sharing
image of counted mixed-side pentagon pairs. -/
@[simp]
theorem mem_crossingChangeMixedSidePentagonPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeMixedSidePentagonPartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.crossingChangeMixedSidePentagonPairs C t x z,
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
    (hD : D ∈ G.crossingChangeSameSidePentagonPairs C t x z) :
    ∃ F ∈ G.crossingChangeSameSidePentagonPartners C t x z,
      D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition ∧
        G.crossingChangePentagonPairWeight C t R D =
          G.crossingChangeHexagonCompositeWeight C t R F := by
  obtain ⟨hD', hside⟩ := (G.mem_crossingChangeSameSidePentagonPairs C t D).mp hD
  obtain ⟨hP, hQ⟩ := (G.mem_crossingChangePentagonPairs C t D).mp hD'
  rcases D with ⟨m, P | P, Q | Q⟩
  · obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair R hX P Q
        (Finset.inl_mem_disjSum.mp hP) (Finset.inl_mem_disjSum.mp hQ) hzx
    have hrecut' : (GridPentagonPairDecomposition.toRectangleDecomposition
        (⟨m, .inl P, .inl Q⟩ : GridPentagonPairDecomposition a C.turnRow a t x z)).IsRecut
        F.toRectangleDecomposition := by
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl] using hrecut
    exact ⟨F, (G.mem_crossingChangeSameSidePentagonPartners C t F).mpr ⟨hF, _, hD, hrecut'⟩,
      hrecut', by simpa [crossingChangePentagonPairWeight_def] using (hw F hF hrecut).symm⟩
  · simp at hside
  · simp at hside
  · obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair R hX P Q
        (Finset.inr_mem_disjSum.mp hP) (Finset.inr_mem_disjSum.mp hQ) hzx
    have hrecut' : (GridPentagonPairDecomposition.toRectangleDecomposition
        (⟨m, .inr P, .inr Q⟩ : GridPentagonPairDecomposition a C.turnRow a t x z)).IsRecut
        F.toRectangleDecomposition := by
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hrecut
    exact ⟨F, (G.mem_crossingChangeSameSidePentagonPartners C t F).mpr ⟨hF, _, hD, hrecut'⟩,
      hrecut', by simpa [crossingChangePentagonPairWeight_def] using (hw F hF hrecut).symm⟩

private theorem exists_mixedSidePartner (R : Type*) [CommSemiring R]
    (hst : C.turnRow ≠ t) (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x)
    {D : GridPentagonPairDecomposition a C.turnRow a t x z}
    (hD : D ∈ G.crossingChangeMixedSidePentagonPairs C t x z) :
    ∃ F ∈ G.crossingChangeMixedSidePentagonPartners C t x z,
      D.toRectangleDecomposition = F.toRectangleDecomposition ∧
        G.crossingChangePentagonPairWeight C t R D =
          G.crossingChangeHexagonCompositeWeight C t R F := by
  obtain ⟨hD', hside⟩ := (G.mem_crossingChangeMixedSidePentagonPairs C t D).mp hD
  obtain ⟨hP, hQ⟩ := (G.mem_crossingChangePentagonPairs C t D).mp hD'
  rcases D with ⟨m, P | P, Q | Q⟩
  · simp at hside
  · obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalInitialPentagonPair R hst hX
        P Q (Finset.inl_mem_disjSum.mp hP) (Finset.inr_mem_disjSum.mp hQ) hzx
    have hFD' : GridPentagonPairDecomposition.toRectangleDecomposition
        (⟨m, .inl P, .inr Q⟩ : GridPentagonPairDecomposition a C.turnRow a t x z) =
        F.toRectangleDecomposition := by
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hFD.symm
    exact ⟨F, (G.mem_crossingChangeMixedSidePentagonPartners C t F).mpr ⟨hF, _, hD, hFD'⟩,
      hFD', by simpa [crossingChangePentagonPairWeight_def] using hw.symm⟩
  · obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialTerminalPentagonPair R hst hX
        P Q (Finset.inr_mem_disjSum.mp hP) (Finset.inl_mem_disjSum.mp hQ) hzx
    have hFD' : GridPentagonPairDecomposition.toRectangleDecomposition
        (⟨m, .inr P, .inl Q⟩ : GridPentagonPairDecomposition a C.turnRow a t x z) =
        F.toRectangleDecomposition := by
      simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hFD.symm
    exact ⟨F, (G.mem_crossingChangeMixedSidePentagonPartners C t F).mpr ⟨hF, _, hD, hFD'⟩,
      hFD', by simpa [crossingChangePentagonPairWeight_def] using hw.symm⟩
  · simp at hside

/-- Off the diagonal, if the annulus squares carry no `X`-marking, the counted same-side pentagon
pairs and their recut partners have equal total polynomial weight over every commutative
semiring. -/
theorem sum_crossingChangePentagonPairWeight_sameSide_eq_sum_partners
    (R : Type*) [CommSemiring R] (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ G.crossingChangeSameSidePentagonPairs C t x z,
        G.crossingChangePentagonPairWeight C t R D =
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
  · obtain ⟨hfD, hsD⟩ := G.isEmpty_of_mem_crossingChangePentagonPairs C t
      (G.crossingChangeSameSidePentagonPairs_subset C t x z hD)
    obtain ⟨hfE, hsE⟩ := G.isEmpty_of_mem_crossingChangePentagonPairs C t
      (G.crossingChangeSameSidePentagonPairs_subset C t x z hE)
    exact GridPentagonPairDecomposition.toRectangleDecomposition_injective
      (hDF.eq_of_isRecut hEF hfD hsD hfE hsE)
  · obtain ⟨hf, hs⟩ := G.isEmpty_of_mem_crossingChangePentagonPairs C t
      (G.crossingChangeSameSidePentagonPairs_subset C t x z hD)
    exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hunpaired hF) (hunpaired hF')
      ((D.toRectangleDecomposition.existsUnique_isRecut
        (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hDF) hf hs).unique hDF hDF')

/-- Off the diagonal, if the turn rows `s` and `t` differ and the annulus squares carry no
`X`-marking, the counted mixed-side pentagon pairs and their partners have equal total polynomial
weight over every commutative semiring. -/
theorem sum_crossingChangePentagonPairWeight_mixedSide_eq_sum_partners
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ G.crossingChangeMixedSidePentagonPairs C t x z,
        G.crossingChangePentagonPairWeight C t R D =
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

private theorem finRotate_mem_commonSideColumns_of_crossingChangePentagonPair {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    b ∈ D.toRectangleDecomposition.commonSideColumns := by
  rcases D with ⟨m, P | P, Q | Q⟩
  · simp [P.right_eq, Q.right_eq]
  · simp [P.right_eq, Q.left_eq]
  · simp [P.left_eq, Q.right_eq]
  · simp [P.left_eq, Q.left_eq]

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
  have hb : b ∈ F.toRectangleDecomposition.commonSideColumns :=
    hEF ▸ finRotate_mem_commonSideColumns_of_crossingChangePentagonPair C t E
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
  have hD' : D ∈ G.crossingChangePentagonPairs C t x z :=
    (G.mem_crossingChangePentagonPairs C t D).mpr hD
  rw [Finset.mem_union]
  rcases hmatch with ⟨hside, hrecut⟩ | ⟨hside, hrect⟩
  · exact Or.inl ((G.mem_crossingChangeSameSidePentagonPartners C t F).mpr
      ⟨hF, D, (G.mem_crossingChangeSameSidePentagonPairs C t D).mpr ⟨hD', hside⟩, hrecut⟩)
  · exact Or.inr ((G.mem_crossingChangeMixedSidePentagonPartners C t F).mpr
      ⟨hF, D, (G.mem_crossingChangeMixedSidePentagonPairs C t D).mpr ⟨hD', hside⟩, hrect⟩)

/-- **Off-diagonal weight identity for the crossing-change homotopy.** If the turn rows `s` and
`t` differ and the annulus squares carry no `X`-marking, then for distinct grid states `x ≠ z` the
unpaired crossing-change hexagon composites from `x` to `z` have the total polynomial weight of the
products of the pentagon coefficients of `Φ` (renamed by the column swap) and `Ψ`, over *every*
commutative semiring. -/
theorem sum_crossingChangeUnpairedHexagonComposites_eq_sum_pentagonCoefficient
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
    ← G.sum_crossingChangePentagonPairWeight_sameSide_eq_sum_partners C t R hX hxz.symm,
    ← G.sum_crossingChangePentagonPairWeight_mixedSide_eq_sum_partners C t R hst hX hxz.symm,
    crossingChangeSameSidePentagonPairs, crossingChangeMixedSidePentagonPairs,
    Finset.sum_filter_add_sum_filter_not,
    G.sum_rename_commutationPentagonCoefficient_mul_withTurnRow C t R]

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
      G.sum_crossingChangeUnpairedHexagonComposites_eq_sum_pentagonCoefficient C t R hst hX hxz) c

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
    (fun _ _ hxz => G.sum_crossingChangeUnpairedHexagonComposites_eq_sum_pentagonCoefficient C t R
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
    (fun _ _ hxz => G.sum_crossingChangeUnpairedHexagonComposites_eq_sum_pentagonCoefficient C t R
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
