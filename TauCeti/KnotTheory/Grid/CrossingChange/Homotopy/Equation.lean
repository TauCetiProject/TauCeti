/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Partners
import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Unpaired

/-!
# The homotopy equation of a grid crossing change

Let `C` be a column turn at the cyclically adjacent columns `a = C.column` and `b = finRotate n a`
of a grid diagram `G`, turning in row `C.turnRow`, and let `t` be a second row. Write
`Φ : GC⁻(G) → GC⁻(G')` for the commutation map of `C`, where `G' = G.swapColumns a b`,
`Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning in row `t`, and
`H : GC⁻(G) → GC⁻(G)` for the hexagon-counting map `GridDiagram.crossingChangeHomotopy` with
corners in `C.turnRow` and `t`.

When `C.turnRow ≠ t` and the annulus squares `GridDiagram.crossingChangeAnnulusSquares C t` carry
no `X`-marking, `Homotopy/Recut.lean` reduces the characteristic-two chain homotopy equation
`∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ` (where `w` is the annulus weight) to matching the off-diagonal
unpaired hexagon composites with the pentagon pairs counted by `Ψ ∘ Φ`. Off the diagonal, every
unpaired composite is the partner of a counted pentagon pair (`Homotopy/Unpaired.lean`), so the
unpaired composites partition into the three pairwise-disjoint partner families summed in
`Homotopy/TerminalInitialSum.lean` and `Homotopy/Partners.lean`.

Specializing `C.turnRow` and `t` to the turn rows of two interleaving columns yields the two
crossing-change homotopy equations of Ozsváth--Stipsicz--Szabó:

* `∂ ∘ H + H ∘ ∂ = V_b + Ψ ∘ Φ` when `O_a` lies on the arc of column `b`, turning at `O_a` and
  `X_b`;
* `∂ ∘ H + H ∘ ∂ = V_a + Ψ ∘ Φ` when `O_a` lies off the arc of column `b`, turning at `X_a` and
  `O_b`.

## Main results

* `TauCeti.GridDiagram.crossingChangeUnpairedHexagonComposites_eq_union`: off the diagonal, the
  unpaired composites are the union of the same-side, terminal--initial, and initial--terminal
  partner families.
* `TauCeti.GridDiagram` theorem
  `sum_crossingChangeUnpairedHexagonComposites_eq_sum_rename_commutationPentagonCoefficient_mul`:
  off the diagonal, the unpaired composites have the total weight of the round-trip pentagon
  coefficient products over every commutative semiring.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq`: the general
  homotopy equation `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ` in characteristic two.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc` and
  `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc`:
  the two crossing-change homotopy equations `∂ ∘ H + H ∘ ∂ = V_b + Ψ ∘ Φ` and
  `∂ ∘ H + H ∘ ∂ = V_a + Ψ ∘ Φ` for interleaving columns in characteristic two.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 6.1, Lemma 6.1.3.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3.
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Partitioning the unpaired composites -/

open scoped Classical in
/-- Off the diagonal (`z ≠ x`), when the crossing-change annulus carries no `X`-marking, the
unpaired hexagon composites are exhausted by the same-side, terminal--initial, and
initial--terminal pentagon-pair partner families. -/
theorem crossingChangeUnpairedHexagonComposites_eq_union
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    G.crossingChangeUnpairedHexagonComposites C t x z =
      G.crossingChangeSameSidePartners C t x z ∪
        G.crossingChangeTerminalInitialPartners C t x z ∪
        G.crossingChangeInitialTerminalPartners C t x z := by
  refine Finset.Subset.antisymm (fun F hF => ?_)
    (Finset.union_subset
      (Finset.union_subset (G.crossingChangeSameSidePartners_subset C t x z)
        (G.crossingChangeTerminalInitialPartners_subset C t x z))
      (G.crossingChangeInitialTerminalPartners_subset C t x z))
  obtain ⟨D, ⟨hP, hQ⟩, hcase⟩ :=
    exists_pentagonPair_of_mem_crossingChangeUnpairedHexagonComposites hX hzx hF
  simp only [Finset.mem_union]
  rcases hcase with ⟨hside, hrecut⟩ | ⟨hside, hrect⟩
  · exact Or.inl (Or.inl ((G.mem_crossingChangeSameSidePartners C t F).mpr
      ⟨hF, D, (G.mem_crossingChangeSameSidePairs C t D).mpr ⟨⟨hP, hQ⟩, hside⟩, hrecut⟩))
  · rcases D with ⟨m, P | P, Q | Q⟩
    · simp at hside
    · simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] at hrect
      exact Or.inl (Or.inr ((G.mem_crossingChangeTerminalInitialPartners C t F).mpr
        ⟨hF, ⟨m, P, Q⟩, (G.mem_crossingChangeTerminalInitialPairs C t _).mpr
          ⟨Finset.inl_mem_disjSum.mp hP, Finset.inr_mem_disjSum.mp hQ⟩, hrect⟩))
    · simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl] at hrect
      exact Or.inr ((G.mem_crossingChangeInitialTerminalPartners C t F).mpr
        ⟨hF, ⟨m, P, Q⟩, (G.mem_crossingChangeInitialTerminalPairs C t _).mpr
          ⟨Finset.inr_mem_disjSum.mp hP, Finset.inl_mem_disjSum.mp hQ⟩, hrect⟩)
    · simp at hside

/-- Off the diagonal (`z ≠ x`), for distinct turn rows and with no `X`-marking in the
crossing-change annulus, the unpaired hexagon composites have the same total polynomial weight as
the round-trip pentagon coefficient products over every commutative semiring. -/
theorem sum_crossingChangeUnpairedHexagonComposites_eq_sum_rename_commutationPentagonCoefficient_mul
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    ∑ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F =
      ∑ y : GridState n,
        rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
          (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  classical
  have hdisj₁ := G.disjoint_crossingChangeSameSidePartners_terminalInitialPartners C t x z
  have hdisj₂ : Disjoint
      (G.crossingChangeSameSidePartners C t x z ∪
        G.crossingChangeTerminalInitialPartners C t x z)
      (G.crossingChangeInitialTerminalPartners C t x z) :=
    Finset.disjoint_union_left.mpr
      ⟨G.disjoint_crossingChangeSameSidePartners_initialTerminalPartners C t x z,
        G.disjoint_crossingChangeTerminalInitialPartners_initialTerminalPartners C t x z⟩
  rw [G.crossingChangeUnpairedHexagonComposites_eq_union C t hX hzx,
    Finset.sum_union hdisj₂, Finset.sum_union hdisj₁,
    ← G.sum_rename_sameSidePentagonCoefficient_eq_sum_crossingChangeSameSidePartners C t R hX hzx,
    ← G.sum_rename_pentagonCoefficient_mul_eq_sum_crossingChangeTerminalInitialPartners
        C t R hst hX hzx,
    ← G.sum_rename_initialPentagonCoefficient_mul_eq_sum_crossingChangeInitialTerminalPartners
        C t R hst hX hzx,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [G.commutationPentagonCoefficient_def R C,
    (G.swapColumns a b).commutationPentagonCoefficient_def R (C.withTurnRow t), map_add]
  simp only [add_mul, mul_add]
  ac_rfl

/-! ### The chain homotopy equations -/

variable {G C t}

/-- **The general crossing-change homotopy equation.** If the turn rows `C.turnRow` and `t` differ
and the crossing-change annulus squares carry no `X`-marking, then over any commutative semiring of
characteristic two, `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ` on every chain, where `w` is the annulus weight. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq
    (R : Type*) [CommSemiring R] [CharP R 2] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      G.crossingChangeAnnulusWeight R C t • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (G.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired R hst hX).mpr
    (fun _ _ hxz =>
      G.sum_crossingChangeUnpairedHexagonComposites_eq_sum_rename_commutationPentagonCoefficient_mul
        C t R hst hX hxz.symm) c

/-- **The crossing-change homotopy equation for `O_a` on the arc of column `b`.** If the segments
of columns `a` and `b = finRotate n a` interleave with `O_a` on the arc of column `b`, and the
crossing-change maps turn in the rows of `O_a` and `X_b`, then over any commutative semiring of
characteristic two, `∂ ∘ H + H ∘ ∂ = V_b + Ψ ∘ Φ`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc
    (R : Type*) [CommSemiring R] [CharP R 2] (h : G.ColumnsInterleaving a b)
    (hO : G.O a ∈ G.columnArc b) (hs : C.turnRow = G.O a) (ht : t = G.X b)
    (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X b : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) := by
  rw [← crossingChangeAnnulusWeight_eq_X_next_of_mem_columnArc R h hO hs ht]
  exact unblockedDifferential_crossingChangeHomotopy_add_eq R
    (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.1)
    (disjoint_crossingChangeAnnulusSquares_XSet_of_mem_columnArc h hO hs ht) c

/-- **The crossing-change homotopy equation for `O_a` off the arc of column `b`.** If the segments
of columns `a` and `b = finRotate n a` interleave with `O_a` off the arc of column `b`, and the
crossing-change maps turn in the rows of `X_a` and `O_b`, then over any commutative semiring of
characteristic two, `∂ ∘ H + H ∘ ∂ = V_a + Ψ ∘ Φ`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc
    (R : Type*) [CommSemiring R] [CharP R 2] (h : G.ColumnsInterleaving a b)
    (hO : G.O a ∉ G.columnArc b) (hs : C.turnRow = G.X a) (ht : t = G.O b)
    (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X a : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) := by
  rw [← crossingChangeAnnulusWeight_eq_X_column_of_notMem_columnArc R h hO hs ht]
  exact unblockedDifferential_crossingChangeHomotopy_add_eq R
    (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.2)
    (disjoint_crossingChangeAnnulusSquares_XSet_of_notMem_columnArc h hO hs ht) c

end TauCeti.GridDiagram
