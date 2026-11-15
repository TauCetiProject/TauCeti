/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.SameSide
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.TerminalInitialSum
import TauCeti.Algebra.BigOperators.Finset.Pairing

/-!
# Summing pentagon-pair partners in the crossing-change homotopy

The round trip `Ψ ∘ Φ` of two crossing-change maps counts pairs of pentagons: a forward pentagon
of `G` turning in row `C.turnRow` followed by a return pentagon of `G.swapColumns a b` turning in
row `t`. Off the diagonal (`z ≠ x`), when the turn rows differ and the crossing-change annulus
carries no `X`-marking, each of the four turn-side branches matches bijectively with a family of
unpaired hexagon composites of the crossing-change homotopy, preserving polynomial weight:

* terminal--initial pairs are summed in
  `TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.TerminalInitialSum`;
* initial--terminal pairs share their underlying two-rectangle decompositions with their
  unpaired composite partners (`GridDiagram` theorem
  `existsUnique_crossingChangeUnpairedHexagonComposite_of_initialTerminalPentagonPair`);
* same-side pairs (terminal--terminal and initial--initial) recut to their unpaired composite
  partners
  (`GridDiagram.existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair` and
  `GridDiagram.existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair`).

This file sums the initial--terminal and same-side branches over every commutative semiring and
proves that the resulting three partner families inside
`GridDiagram.crossingChangeUnpairedHexagonComposites` are pairwise disjoint.

## Main definitions and results

* `TauCeti.GridDiagram.crossingChangeInitialTerminalPairs` and
  `TauCeti.GridDiagram.crossingChangeInitialTerminalPartners`: the counted initial--terminal
  pentagon pairs and their exact image among unpaired composites, with weight identity
  `sum_rename_initialPentagonCoefficient_mul_eq_sum_crossingChangeInitialTerminalPartners`.
* `TauCeti.GridDiagram.crossingChangeSameSidePairs` and
  `TauCeti.GridDiagram.crossingChangeSameSidePartners`: the counted same-side pentagon pairs and
  their exact recut image among unpaired composites, with weight identity
  `sum_rename_sameSidePentagonCoefficient_eq_sum_crossingChangeSameSidePartners`.
* `TauCeti.GridDiagram.disjoint_crossingChangeTerminalInitialPartners_initialTerminalPartners`,
  `TauCeti.GridDiagram.disjoint_crossingChangeSameSidePartners_terminalInitialPartners`, and
  `TauCeti.GridDiagram.disjoint_crossingChangeSameSidePartners_initialTerminalPartners`: pairwise
  disjointness of the three partner families.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 6.1.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Initial--terminal partners -/

/-- The initial--terminal pentagon pairs in the round trip through the exchanged diagram.
The first pentagon turns on its initial side in row `C.turnRow`, the second on its terminal side
in row `t`. -/
noncomputable def crossingChangeInitialTerminalPairs (x z : GridState n) :
    Finset (GridTwoStepDecomposition (GridInitialPentagonBetween a C.turnRow)
      (GridPentagonBetween a t) x z) :=
  GridTwoStepDecomposition.decompositionsOf (G.initialPentagons C)
    ((G.swapColumns a b).pentagons (C.withTurnRow t)) x z

/-- An initial--terminal pair is counted exactly when each of its pentagons is counted. -/
@[simp]
theorem mem_crossingChangeInitialTerminalPairs {x z : GridState n}
    (D : GridTwoStepDecomposition (GridInitialPentagonBetween a C.turnRow)
      (GridPentagonBetween a t) x z) :
    D ∈ G.crossingChangeInitialTerminalPairs C t x z ↔
      D.first ∈ G.initialPentagons C x D.middle ∧
        D.second ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) D.middle z := by
  rw [crossingChangeInitialTerminalPairs, GridTwoStepDecomposition.mem_decompositionsOf]

/-- The exact image of counted initial--terminal pentagon pairs among the unpaired crossing-change
hexagon composites. -/
noncomputable def crossingChangeInitialTerminalPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.crossingChangeInitialTerminalPairs C t x z,
      (⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩ :
        GridRectangleDecomposition x z) = F.toRectangleDecomposition

/-- Initial--terminal partners are the unpaired composites sharing the two rectangles of a counted
initial--terminal pair. -/
@[simp]
theorem mem_crossingChangeInitialTerminalPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeInitialTerminalPartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.crossingChangeInitialTerminalPairs C t x z,
          (⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩ :
            GridRectangleDecomposition x z) = F.toRectangleDecomposition := by
  classical
  simp only [crossingChangeInitialTerminalPartners, Finset.mem_filter]

/-- Every initial--terminal partner belongs to the unpaired-composite sum. -/
theorem crossingChangeInitialTerminalPartners_subset (x z : GridState n) :
    G.crossingChangeInitialTerminalPartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeInitialTerminalPartners C t F).mp hF).1

/-- Off the diagonal (`z ≠ x`), for distinct turn rows and with no `X`-marking in the
crossing-change annulus, the initial--terminal terms of the round-trip coefficient sum have the
same total weight as their unpaired hexagon-composite partners over every commutative semiring. -/
theorem sum_rename_initialPentagonCoefficient_mul_eq_sum_crossingChangeInitialTerminalPartners
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    (∑ y : GridState n,
      MvPolynomial.rename (Equiv.swap a b) (G.initialPentagonCoefficient R C x y) *
        (G.swapColumns a b).pentagonCoefficient R (C.withTurnRow t) y z) =
      ∑ F ∈ G.crossingChangeInitialTerminalPartners C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F := by
  classical
  let rect (D : GridTwoStepDecomposition (GridInitialPentagonBetween a C.turnRow)
      (GridPentagonBetween a t) x z) : GridRectangleDecomposition x z :=
    ⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩
  have hinj : Function.Injective rect := fun _ _ h =>
    GridTwoStepDecomposition.ext_of_middle_eq
      (congrArg (fun F : GridRectangleDecomposition x z => F.middle) h)
  have hcounted {F} (hF : F ∈ G.crossingChangeInitialTerminalPartners C t x z) :=
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp
      (G.crossingChangeInitialTerminalPartners_subset C t x z hF)).1
  simp_rw [G.initialPentagonCoefficient_def R C,
    (G.swapColumns a b).pentagonCoefficient_def R (C.withTurnRow t),
    map_sum, Finset.sum_mul_sum]
  rw [← GridTwoStepDecomposition.sum_decompositionsOf]
  refine Finset.sum_bij_of_rel (fun D F => rect D = F.toRectangleDecomposition)
    (fun D hD => ?_) (fun _ _ _ _ _ _ hDF hEF => hinj (hDF.trans hEF.symm))
    (fun _ _ F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ((G.mem_crossingChangeInitialTerminalPartners C t F).mp hF).2)
  · obtain ⟨hP, hQ⟩ := (G.mem_crossingChangeInitialTerminalPairs C t D).mp hD
    obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialTerminalPentagonPair
        R hst hX D.first D.second hP hQ hzx
    exact ⟨F, (G.mem_crossingChangeInitialTerminalPartners C t F).mpr
      ⟨hF, D, hD, hFD.symm⟩, hFD.symm, hw.symm⟩
  · exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hcounted hF) (hcounted hF') (hDF.symm.trans hDF')

/-! ### Same-side partners -/

/-- The counted pentagon pairs in the round trip through the exchanged diagram whose two pentagons
turn on the same side of the replaced grid line: terminal--terminal and initial--initial pairs. -/
noncomputable def crossingChangeSameSidePairs (x z : GridState n) :
    Finset (GridPentagonPairDecomposition a C.turnRow a t x z) :=
  (GridTwoStepDecomposition.decompositionsOf
    (fun u v => (G.pentagons C u v).disjSum (G.initialPentagons C u v))
    (fun u v => ((G.swapColumns a b).pentagons (C.withTurnRow t) u v).disjSum
      ((G.swapColumns a b).initialPentagons (C.withTurnRow t) u v))
    x z).filter fun D => D.first.isLeft = D.second.isLeft

/-- A pentagon pair is a counted same-side crossing-change pair exactly when both pentagons are
counted and turn on the same side. -/
@[simp]
theorem mem_crossingChangeSameSidePairs {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    D ∈ G.crossingChangeSameSidePairs C t x z ↔
      (D.first ∈ (G.pentagons C x D.middle).disjSum (G.initialPentagons C x D.middle) ∧
        D.second ∈ ((G.swapColumns a b).pentagons (C.withTurnRow t) D.middle z).disjSum
          ((G.swapColumns a b).initialPentagons (C.withTurnRow t) D.middle z)) ∧
        D.first.isLeft = D.second.isLeft := by
  rw [crossingChangeSameSidePairs, Finset.mem_filter,
    GridTwoStepDecomposition.mem_decompositionsOf]

/-- Both underlying rectangles of a counted same-side pentagon pair are empty. -/
private theorem isEmpty_of_mem_crossingChangeSameSidePairs {x z : GridState n}
    {D : GridPentagonPairDecomposition a C.turnRow a t x z}
    (hD : D ∈ G.crossingChangeSameSidePairs C t x z) :
    D.toRectangleDecomposition.first.IsEmpty ∧ D.toRectangleDecomposition.second.IsEmpty := by
  obtain ⟨⟨hP, hQ⟩, hside⟩ := (G.mem_crossingChangeSameSidePairs C t D).mp hD
  rcases D with ⟨m, P | P, Q | Q⟩
  · simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl] using
      And.intro ((G.mem_pentagons (C := C) P).mp (Finset.inl_mem_disjSum.mp hP)).1
        (((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) Q).mp
          (Finset.inl_mem_disjSum.mp hQ)).1
  · simp at hside
  · simp at hside
  · simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr] using
      And.intro ((G.mem_initialPentagons (C := C) P).mp (Finset.inr_mem_disjSum.mp hP)).1
        (((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) Q).mp
          (Finset.inr_mem_disjSum.mp hQ)).1

/-- The polynomial weight of a crossing-change pentagon pair, with the first factor renamed by the
column swap. -/
private noncomputable def crossingChangeSameSidePairWeight (R : Type*) [CommSemiring R]
    {x z : GridState n} (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    MvPolynomial (Fin n) R :=
  MvPolynomial.rename (Equiv.swap a b)
      (D.first.elim (G.pentagonWeight R C) (G.initialPentagonWeight R C)) *
    D.second.elim ((G.swapColumns a b).pentagonWeight R (C.withTurnRow t))
      ((G.swapColumns a b).initialPentagonWeight R (C.withTurnRow t))

/-- The terminal--terminal and initial--initial coefficient products sum to the weights of the
counted same-side pentagon pairs. -/
private theorem sum_rename_sameSidePentagonCoefficient_eq_sum_pairs
    (R : Type*) [CommSemiring R] (x z : GridState n) :
    (∑ y : GridState n,
      MvPolynomial.rename (Equiv.swap a b) (G.pentagonCoefficient R C x y) *
        (G.swapColumns a b).pentagonCoefficient R (C.withTurnRow t) y z) +
    (∑ y : GridState n,
      MvPolynomial.rename (Equiv.swap a b) (G.initialPentagonCoefficient R C x y) *
        (G.swapColumns a b).initialPentagonCoefficient R (C.withTurnRow t) y z) =
      ∑ D ∈ G.crossingChangeSameSidePairs C t x z,
        G.crossingChangeSameSidePairWeight C t R D := by
  let S₁ := GridTwoStepDecomposition.decompositionsOf (G.pentagons C)
    ((G.swapColumns a b).pentagons (C.withTurnRow t)) x z
  let S₂ := GridTwoStepDecomposition.decompositionsOf (G.initialPentagons C)
    ((G.swapColumns a b).initialPentagons (C.withTurnRow t)) x z
  let emb₁ : GridTwoStepDecomposition (GridPentagonBetween a C.turnRow)
      (GridPentagonBetween a t) x z ↪
      GridPentagonPairDecomposition a C.turnRow a t x z :=
    ⟨fun D => ⟨D.middle, .inl D.first, .inl D.second⟩, by
      rintro ⟨m, P, Q⟩ ⟨m', P', Q'⟩ h
      have hm : m = m' := congrArg GridTwoStepDecomposition.middle h
      subst hm
      simp only [GridTwoStepDecomposition.mk.injEq, Sum.inl.injEq, heq_eq_eq, true_and] at h
      rw [h.1, h.2]⟩
  let emb₂ : GridTwoStepDecomposition (GridInitialPentagonBetween a C.turnRow)
      (GridInitialPentagonBetween a t) x z ↪
      GridPentagonPairDecomposition a C.turnRow a t x z :=
    ⟨fun D => ⟨D.middle, .inr D.first, .inr D.second⟩, by
      rintro ⟨m, P, Q⟩ ⟨m', P', Q'⟩ h
      have hm : m = m' := congrArg GridTwoStepDecomposition.middle h
      subst hm
      simp only [GridTwoStepDecomposition.mk.injEq, Sum.inr.injEq, heq_eq_eq, true_and] at h
      rw [h.1, h.2]⟩
  have hdisj : Disjoint (S₁.map emb₁) (S₂.map emb₂) := by
    rw [Finset.disjoint_left]
    intro D h₁ h₂
    obtain ⟨_, -, rfl⟩ := Finset.mem_map.mp h₁
    obtain ⟨_, -, h⟩ := Finset.mem_map.mp h₂
    exact Bool.false_ne_true (congrArg (fun E => E.first.isLeft) h)
  have hunion : (S₁.map emb₁).disjUnion (S₂.map emb₂) hdisj =
      G.crossingChangeSameSidePairs C t x z := by
    ext D
    rw [Finset.mem_disjUnion]
    constructor
    · rintro (h | h)
      · obtain ⟨⟨m, P, Q⟩, hD, rfl⟩ := Finset.mem_map.mp h
        obtain ⟨hP, hQ⟩ := (GridTwoStepDecomposition.mem_decompositionsOf ..).mp hD
        exact (G.mem_crossingChangeSameSidePairs C t _).mpr
          ⟨⟨Finset.inl_mem_disjSum.mpr hP, Finset.inl_mem_disjSum.mpr hQ⟩, rfl⟩
      · obtain ⟨⟨m, P, Q⟩, hD, rfl⟩ := Finset.mem_map.mp h
        obtain ⟨hP, hQ⟩ := (GridTwoStepDecomposition.mem_decompositionsOf ..).mp hD
        exact (G.mem_crossingChangeSameSidePairs C t _).mpr
          ⟨⟨Finset.inr_mem_disjSum.mpr hP, Finset.inr_mem_disjSum.mpr hQ⟩, rfl⟩
    · intro h
      obtain ⟨⟨hP, hQ⟩, hside⟩ := (G.mem_crossingChangeSameSidePairs C t D).mp h
      rcases D with ⟨m, P | P, Q | Q⟩
      · exact Or.inl (Finset.mem_map.mpr ⟨⟨m, P, Q⟩,
          (GridTwoStepDecomposition.mem_decompositionsOf ..).mpr
            ⟨Finset.inl_mem_disjSum.mp hP, Finset.inl_mem_disjSum.mp hQ⟩, rfl⟩)
      · simp at hside
      · simp at hside
      · exact Or.inr (Finset.mem_map.mpr ⟨⟨m, P, Q⟩,
          (GridTwoStepDecomposition.mem_decompositionsOf ..).mpr
            ⟨Finset.inr_mem_disjSum.mp hP, Finset.inr_mem_disjSum.mp hQ⟩, rfl⟩)
  rw [← hunion, Finset.sum_disjUnion, Finset.sum_map, Finset.sum_map]
  simp_rw [G.pentagonCoefficient_def R C,
    (G.swapColumns a b).pentagonCoefficient_def R (C.withTurnRow t),
    G.initialPentagonCoefficient_def R C,
    (G.swapColumns a b).initialPentagonCoefficient_def R (C.withTurnRow t),
    map_sum, Finset.sum_mul_sum]
  rw [← GridTwoStepDecomposition.sum_decompositionsOf,
    ← GridTwoStepDecomposition.sum_decompositionsOf]
  rfl

/-- Off the diagonal, each counted same-side crossing-change pentagon pair recuts to a unique
unpaired composite of the same weight. -/
private theorem existsUnique_crossingChangeSameSidePartner (R : Type*) [CommSemiring R]
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n} (hzx : z ≠ x)
    {D : GridPentagonPairDecomposition a C.turnRow a t x z}
    (hD : D ∈ G.crossingChangeSameSidePairs C t x z) :
    ∃ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
      D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition ∧
        G.crossingChangeHexagonCompositeWeight C t R F =
          G.crossingChangeSameSidePairWeight C t R D := by
  obtain ⟨⟨hP, hQ⟩, hside⟩ := (G.mem_crossingChangeSameSidePairs C t D).mp hD
  rcases D with ⟨m, P | P, Q | Q⟩
  · obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair R hX P Q
        (Finset.inl_mem_disjSum.mp hP) (Finset.inl_mem_disjSum.mp hQ) hzx
    refine ⟨F, hF, ?_, hw F hF hrecut⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl] using hrecut
  · simp at hside
  · simp at hside
  · obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair R hX P Q
        (Finset.inr_mem_disjSum.mp hP) (Finset.inr_mem_disjSum.mp hQ) hzx
    refine ⟨F, hF, ?_, hw F hF hrecut⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hrecut

/-- The exact recut image of counted same-side pentagon pairs among the unpaired crossing-change
hexagon composites. -/
noncomputable def crossingChangeSameSidePartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.crossingChangeSameSidePairs C t x z,
      D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition

/-- Same-side partners are the unpaired composites recutting a counted same-side pentagon pair. -/
@[simp]
theorem mem_crossingChangeSameSidePartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeSameSidePartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.crossingChangeSameSidePairs C t x z,
          D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition := by
  classical
  simp only [crossingChangeSameSidePartners, Finset.mem_filter]

/-- Every same-side partner belongs to the unpaired-composite sum. -/
theorem crossingChangeSameSidePartners_subset (x z : GridState n) :
    G.crossingChangeSameSidePartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeSameSidePartners C t F).mp hF).1

/-- Off the diagonal (`z ≠ x`), with no `X`-marking in the crossing-change annulus, the same-side
terms of the round-trip coefficient sum have the same total weight as their unpaired
hexagon-composite recut partners over every commutative semiring. -/
theorem sum_rename_sameSidePentagonCoefficient_eq_sum_crossingChangeSameSidePartners
    (R : Type*) [CommSemiring R] (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    (∑ y : GridState n,
      MvPolynomial.rename (Equiv.swap a b) (G.pentagonCoefficient R C x y) *
        (G.swapColumns a b).pentagonCoefficient R (C.withTurnRow t) y z) +
    (∑ y : GridState n,
      MvPolynomial.rename (Equiv.swap a b) (G.initialPentagonCoefficient R C x y) *
        (G.swapColumns a b).initialPentagonCoefficient R (C.withTurnRow t) y z) =
      ∑ F ∈ G.crossingChangeSameSidePartners C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F := by
  have hcounted {F} (hF : F ∈ G.crossingChangeSameSidePartners C t x z) :=
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp
      (G.crossingChangeSameSidePartners_subset C t x z hF)).1
  rw [G.sum_rename_sameSidePentagonCoefficient_eq_sum_pairs C t R x z]
  refine Finset.sum_bij_of_rel
    (fun D F => D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition)
    (fun D hD => ?_) (fun _ hD _ hE _ _ hDF hEF => ?_) (fun D hD F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ((G.mem_crossingChangeSameSidePartners C t F).mp hF).2)
  · obtain ⟨F, hF, hrecut, hw⟩ :=
      G.existsUnique_crossingChangeSameSidePartner C t R hX hzx hD
    exact ⟨F, (G.mem_crossingChangeSameSidePartners C t F).mpr ⟨hF, D, hD, hrecut⟩, hrecut,
      hw.symm⟩
  · obtain ⟨hfD, hsD⟩ := G.isEmpty_of_mem_crossingChangeSameSidePairs C t hD
    obtain ⟨hfE, hsE⟩ := G.isEmpty_of_mem_crossingChangeSameSidePairs C t hE
    exact GridPentagonPairDecomposition.toRectangleDecomposition_injective
      (hDF.eq_of_isRecut hEF hfD hsD hfE hsE)
  · obtain ⟨hfD, hsD⟩ := G.isEmpty_of_mem_crossingChangeSameSidePairs C t hD
    exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hcounted hF) (hcounted hF')
      ((D.toRectangleDecomposition.existsUnique_isRecut
        (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hDF) hfD hsD).unique hDF hDF')

/-! ### Disjointness of the three partner families -/

/-- No unpaired composite is both a terminal--initial partner and an initial--terminal partner:
the first rectangle of an initial--terminal pair has initial side `b`, whereas that of a
terminal--initial pair does not. -/
theorem disjoint_crossingChangeTerminalInitialPartners_initialTerminalPartners
    (x z : GridState n) :
    Disjoint (G.crossingChangeTerminalInitialPartners C t x z)
      (G.crossingChangeInitialTerminalPartners C t x z) := by
  rw [Finset.disjoint_left]
  intro F hTI hIT
  obtain ⟨-, D₁, -, hD₁⟩ := (G.mem_crossingChangeTerminalInitialPartners C t F).mp hTI
  obtain ⟨-, D₂, -, hD₂⟩ := (G.mem_crossingChangeInitialTerminalPartners C t F).mp hIT
  have hl : D₁.first.left = D₂.first.left :=
    congrArg (fun E : GridRectangleDecomposition x z => E.first.left) (hD₁.trans hD₂.symm)
  exact D₁.first.left_ne (hl.trans D₂.first.left_eq)

/-- The replaced column `b` is never a common side column of a same-side recut partner. -/
private theorem finRotate_notMem_commonSideColumns_of_mem_crossingChangeSameSidePartners
    {x z : GridState n} {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeSameSidePartners C t x z) :
    b ∉ F.toRectangleDecomposition.commonSideColumns := by
  obtain ⟨-, D, hD, hrecut⟩ := (G.mem_crossingChangeSameSidePartners C t F).mp hF
  obtain ⟨-, hside⟩ := (G.mem_crossingChangeSameSidePairs C t D).mp hD
  rcases D with ⟨m, P | P, Q | Q⟩
  · have hcommon := hrecut.isRecutOfRightEqRight (by
      simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl, P.right_eq, Q.right_eq])
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl, P.right_eq] using
      hcommon.first_right_notMem_commonSideColumns
  · simp at hside
  · simp at hside
  · have hcommon := hrecut.isRecutOfLeftEqLeft (by
      simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr, P.left_eq, Q.left_eq])
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr, P.left_eq] using
      hcommon.first_left_notMem_commonSideColumns

/-- No unpaired composite is both a same-side recut partner and a terminal--initial partner: the
replaced column `b` is a common side of the latter but not of the former. -/
theorem disjoint_crossingChangeSameSidePartners_terminalInitialPartners (x z : GridState n) :
    Disjoint (G.crossingChangeSameSidePartners C t x z)
      (G.crossingChangeTerminalInitialPartners C t x z) := by
  rw [Finset.disjoint_left]
  intro F hS hTI
  obtain ⟨-, D, -, hDF⟩ := (G.mem_crossingChangeTerminalInitialPartners C t F).mp hTI
  refine G.finRotate_notMem_commonSideColumns_of_mem_crossingChangeSameSidePartners C t hS ?_
  rw [← hDF]
  simp [D.first.right_eq, D.second.left_eq]

/-- No unpaired composite is both a same-side recut partner and an initial--terminal partner: the
replaced column `b` is a common side of the latter but not of the former. -/
theorem disjoint_crossingChangeSameSidePartners_initialTerminalPartners (x z : GridState n) :
    Disjoint (G.crossingChangeSameSidePartners C t x z)
      (G.crossingChangeInitialTerminalPartners C t x z) := by
  rw [Finset.disjoint_left]
  intro F hS hIT
  obtain ⟨-, D, -, hDF⟩ := (G.mem_crossingChangeInitialTerminalPartners C t F).mp hIT
  refine G.finRotate_notMem_commonSideColumns_of_mem_crossingChangeSameSidePartners C t hS ?_
  rw [← hDF]
  simp [D.first.left_eq, D.second.right_eq]

end TauCeti.GridDiagram
