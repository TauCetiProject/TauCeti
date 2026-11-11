/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Unpaired
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Mixed.Side
import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Pentagon.Partner
import TauCeti.Algebra.CharP.Two

/-!
# The homotopy equation of a grid commutation

Let `C` be a validated column commutation of a grid diagram `G`, with commutation map
`Φ : GC⁻(G) → GC⁻(G')`, reverse commutation map `Ψ : GC⁻(G') → GC⁻(G)` and hexagon-counting map
`H : GC⁻(G) → GC⁻(G)`. This file proves the homotopy equation

  `∂ ∘ H + H ∘ ∂ = 1 + Ψ ∘ Φ`

over every commutative semiring of characteristic two.

By the diagonal, disjoint, recut and pentagon-pair cancellations, the equation says that, off
the diagonal, every unpaired hexagon composite is the partner of a pentagon pair: either the recut
of a same-side pair, or the composite with the rectangles of a mixed-side pair. This is
`GridDiagram.unblockedDifferential_commutationHomotopy_add_eq_iff_sum_residual_eq_zero`.
An unpaired composite has a mixed-side overlap
(`GridDiagram.hasMixedSideOverlap_of_mem_unpairedHexagonComposites`), and the case analysis
showing that such a composite is a pentagon partner is shared with the homotopy of a crossing
change: it is `GridDiagram.exists_pentagonPair_of_hasMixedSideOverlap_of_mem_iff`, applied with
the reverse commutation, whose turn row is the opposite intersection row. Its hypotheses on the
`X`-markings of the commuted columns are the facts that these markings lie in the bigons between
the two intersection rows.

## Main results

* `TauCeti.GridDiagram.mem_sameSidePentagonPartners_or_mem_mixedSidePentagonPartners`: off the
  diagonal, every unpaired hexagon composite is a same-side or a mixed-side pentagon partner.
* `TauCeti.GridDiagram.unblockedDifferential_commutationHomotopy_add_eq`: the homotopy equation
  `∂ ∘ H + H ∘ ∂ = 1 + Ψ ∘ Φ` in characteristic two.
* `TauCeti.GridDiagram.unblockedDifferential_commutationHomotopy_reverse_add_eq`: the homotopy
  equation `∂' ∘ H' + H' ∘ ∂' = 1 + Φ ∘ Ψ` of the reverse commutation, on the commuted diagram.
* `TauCeti.GridDiagram.commutationMap_reverse_commutationMap_of_mem_ker` and
  `TauCeti.GridDiagram.commutationMap_commutationMap_reverse_of_mem_ker`: on cycles, both round
  trips are the identity up to a boundary.

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

/-! ### Exhausting the unpaired composites -/

/-- Off the diagonal, every unpaired hexagon composite is a pentagon partner: the recut of a
counted same-side pentagon pair, or the composite with the rectangles of a counted mixed-side
pentagon pair. -/
theorem mem_sameSidePentagonPartners_or_mem_mixedSidePentagonPartners {x z : GridState n}
    (hzx : z ≠ x) {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.unpairedHexagonComposites C x z) :
    F ∈ G.sameSidePentagonPartners C x z ∨ F ∈ G.mixedSidePentagonPartners C x z := by
  rw [mem_sameSidePentagonPartners, mem_mixedSidePentagonPartners]
  obtain ⟨hFc, -, hnot⟩ := (G.mem_unpairedHexagonComposites C F).mp hF
  obtain ⟨⟨m, P, Q⟩, ⟨hP, hQ⟩, hD⟩ := exists_pentagonPair_of_hasMixedSideOverlap_of_mem_iff G C
    C.reverse C.reverse_column C.reverse_turnRow C.X_column_below C.X_next_above
    (G.mem_commutationHexagons_iff_XSet_inter_eq C)
    (G.cutColumn_X_mem_toGridRectangle_coveredSquares C)
    ((G.mem_hexagonCompositeDecompositions_iff_mem_disjSum C F).mp hFc)
    (fun F' hF' => hnot F' ((G.mem_hexagonCompositeDecompositions_iff_mem_disjSum C F').mpr hF'))
    (G.hasMixedSideOverlap_of_mem_unpairedHexagonComposites C hzx hF)
  -- The counted commutation pentagons are the counted pentagons of both turn-side kinds.
  have hpair : (⟨m, P, Q⟩ : GridPentagonPairDecomposition _ _ _ _ x z) ∈
      G.pentagonPairDecompositions C x z := by
    rw [mem_pentagonPairDecompositions]
    constructor
    · cases P <;> simpa using hP
    · cases Q <;> simpa using hQ
  rcases hD with ⟨hside, hrec⟩ | ⟨hside, hrec⟩
  · exact Or.inl ⟨hF, _, (G.mem_sameSidePentagonPairs C _).mpr ⟨hpair, hside⟩, hrec⟩
  · exact Or.inr ⟨hF, _, (G.mem_mixedSidePentagonPairs C _).mpr ⟨hpair, hside⟩, hrec⟩

/-- The homotopy equation `∂ ∘ H + H ∘ ∂ = 1 + Ψ ∘ Φ` of a column commutation, over any
commutative semiring of characteristic two: the hexagon-counting map `H` is a chain homotopy
between the identity of `GC⁻(G)` and the round trip through the commuted diagram. -/
theorem unblockedDifferential_commutationHomotopy_add_eq
    (R : Type*) [CommSemiring R] [CharP R 2] (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.commutationHomotopy R C c) +
        G.commutationHomotopy R C (G.unblockedDifferential R c) =
      c + (G.swapColumns a b).commutationMap R C.reverse (G.commutationMap R C c) :=
  (G.unblockedDifferential_commutationHomotopy_add_eq_iff_sum_residual_eq_zero C R).mpr
    (fun _ _ hzx => Finset.sum_eq_zero fun F hF => by
      simp only [Finset.mem_sdiff] at hF
      exact ((G.mem_sameSidePentagonPartners_or_mem_mixedSidePentagonPartners C hzx hF.1.1).elim
        hF.1.2 hF.2).elim) c

/-- **The homotopy equation on the commuted diagram.** The hexagon map `H'` of the reverse
commutation is a chain homotopy between the identity of `GC⁻(G')` and the round trip `Φ ∘ Ψ`
through `G`: `∂' ∘ H' + H' ∘ ∂' = 1 + Φ ∘ Ψ`. -/
theorem unblockedDifferential_commutationHomotopy_reverse_add_eq
    (R : Type*) [CommSemiring R] [CharP R 2] (c : GridChainMinus R n) :
    (G.swapColumns a b).unblockedDifferential R
          ((G.swapColumns a b).commutationHomotopy R C.reverse c) +
        (G.swapColumns a b).commutationHomotopy R C.reverse
          ((G.swapColumns a b).unblockedDifferential R c) =
      c + G.commutationMap R C ((G.swapColumns a b).commutationMap R C.reverse c) := by
  have h := (G.swapColumns a b).unblockedDifferential_commutationHomotopy_add_eq C.reverse R c
  -- The type of the twice-reversed data mentions the doubly swapped diagram, so its turn is
  -- replaced by that of `C` before that diagram is rewritten to `G`.
  have hturn : (C.reverse.reverse : ColumnTurn n) = C := ColumnTurn.ext (by simp) (by simp)
  rw [hturn] at h
  simpa only [ColumnCommutationData.reverse_column, swapColumns_swapColumns] using h

/-- On a cycle `z` of `GC⁻(G)`, the round trip `Ψ ∘ Φ` through the commuted diagram is the
identity up to the boundary of `H z`. -/
theorem commutationMap_reverse_commutationMap_of_mem_ker
    (R : Type*) [CommSemiring R] [CharP R 2] {z : GridChainMinus R n}
    (hz : z ∈ LinearMap.ker (G.unblockedDifferential R)) :
    (G.swapColumns a b).commutationMap R C.reverse (G.commutationMap R C z) =
      z + G.unblockedDifferential R (G.commutationHomotopy R C z) := by
  have h := G.unblockedDifferential_commutationHomotopy_add_eq C R z
  rw [LinearMap.mem_ker.mp hz, map_zero, add_zero] at h
  rw [h, ← add_assoc, add_self_eq_zero_of_charTwo (MvPolynomial (Fin n) R) z, zero_add]

/-- On a cycle `z` of `GC⁻(G')`, the round trip `Φ ∘ Ψ` through `G` is the identity up to the
boundary of `H' z`. -/
theorem commutationMap_commutationMap_reverse_of_mem_ker
    (R : Type*) [CommSemiring R] [CharP R 2] {z : GridChainMinus R n}
    (hz : z ∈ LinearMap.ker ((G.swapColumns a b).unblockedDifferential R)) :
    G.commutationMap R C ((G.swapColumns a b).commutationMap R C.reverse z) =
      z + (G.swapColumns a b).unblockedDifferential R
        ((G.swapColumns a b).commutationHomotopy R C.reverse z) := by
  have h := G.unblockedDifferential_commutationHomotopy_reverse_add_eq C R z
  rw [LinearMap.mem_ker.mp hz, map_zero, add_zero] at h
  rw [h, ← add_assoc, add_self_eq_zero_of_charTwo (MvPolynomial (Fin n) R) z, zero_add]

end TauCeti.GridDiagram
