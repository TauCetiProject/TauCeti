/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Grading
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Equation
public import TauCeti.KnotTheory.Grid.CrossingChange.UnknottingNumber
public import TauCeti.KnotTheory.Grid.Homology.Commutation.Tau
public import TauCeti.KnotTheory.Grid.Move.Tau
import TauCeti.KnotTheory.Grid.Homology.Transpose

/-!
# Crossing change maps, the invariant `τ`, and the unknotting bound

Let `C` be a column turn at the columns `a = C.column` and `b = finRotate n a` of a grid diagram
`G`, and let `G' = G.swapColumns a b`. Write `Φ : GC⁻(G) → GC⁻(G')` for the commutation map of
`C` and `Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning at the same columns in
another row `t`; the target of `Ψ` is the complex of `G'.swapColumns a b`, which is `G`. This file
proves the unconditional crossing-change inequalities for `τ` and deduces the lower bound
`|τ(K)| ≤ u(K)` on the unknotting number of a grid knot.

The comparison along a single column turn is in `Homology/Commutation/Tau.lean`: if
`ΨΦ` is chain homotopic to multiplication by `p` with `p(U, …, U) = U ^ k`, then `GH⁻(G')` is not
torsion if `GH⁻(G)` is not (`GridDiagram.IsKnot.not_isTorsion_swapColumns_of_homotopy`), and
`τ(G')` is at most `τ(G)` minus the Alexander degree of `Φ`
(`GridDiagram.IsKnot.tau_swapColumns_le_of_homotopy`).

If the segments of the columns `a` and `b` interleave with `O_a` on the arc of column `b`, the
crossing change maps are the commutation map `Φ` turning in the row of `O_a`, of Alexander degree
`0`, and the commutation map `Ψ` of `G'` turning in the row of `X_b`, of Alexander degree `-1`
(`GridDiagram.commutationBidegree_eq_zero_of_mem_columnArc` and
`GridDiagram.commutationBidegree_eq_of_notMem_columnArc`). By the crossing-change homotopy
equations (`CrossingChange/Homotopy/Equation.lean`), `ΨΦ` and `ΦΨ` are chain homotopic to
multiplication by `V_b` and `V_a`, so `τ(G) - 1 ≤ τ(G') ≤ τ(G)`
(`GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_mem_columnArc`), while in the opposite cyclic order
`τ(G) ≤ τ(G') ≤ τ(G) + 1` (`GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_notMem_columnArc`).
Diagonal reflection preserves `τ` (`GridDiagram.IsKnot.tau_transpose`) and exchanges row and column
cross-commutations, so any cross-commutation changes `τ` by at most `1`
(`GridDiagram.IsKnot.natAbs_tau_sub_le_one_of_isCrossCommutation`).

Passing to `GridLink` modulo grid moves, `τ` is `1`-Lipschitz along the crossing-change graph
(`GridLink.IsKnot.natAbs_tau_sub_le_edist`). Evaluating at the unknot over any field of
characteristic two gives `|τ(L)| ≤ u(L)` (`GridLink.IsKnot.natAbs_tau_le_unknottingNumber`).

## Main results

* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_homotopy`: `τ(G) - 1 ≤ τ(G') ≤ τ(G)` from
  abstract crossing-change homotopies.
* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_mem_columnArc` and
  `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_notMem_columnArc`: **the unconditional
  crossing-change inequalities** for interleaving adjacent columns.
* `TauCeti.GridDiagram.IsKnot.tau_transpose`: diagonal reflection preserves `τ`.
* `TauCeti.GridDiagram.IsKnot.natAbs_tau_sub_le_one_of_isCrossCommutation` and
  `TauCeti.GridLink.IsCrossingChange.natAbs_tau_sub_le_one`: a cross-commutation or crossing change
  changes `τ` by at most `1`.
* `TauCeti.GridLink.IsKnot.natAbs_tau_sub_le_edist`: `|τ(L) - τ(L')|` is bounded by the
  crossing-change graph distance.
* `TauCeti.GridLink.IsKnot.natAbs_tau_le_unknottingNumber`: **the unknotting bound**
  `|τ(L)| ≤ u(L)` over any field of characteristic two.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 6.1 and 6.2: the crossing change maps, their composites, and
  the bound `|τ(K)| ≤ u(K)` (Corollary 6.2.4).
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  arXiv:1011.5265: the crossing change inequality and unknotting bound from grid diagrams.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

namespace IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- Exchanging the same two columns twice returns the original knot grid, with the same `τ`. -/
private theorem tau_swapColumns_swapColumns {c d : Fin n} :
    ((hG.swapColumns c d).swapColumns c d).tau K = hG.tau K := by
  have key : ∀ {G₁ : GridDiagram n} (h₁ : G₁.IsKnot), G₁ = G → h₁.tau K = hG.tau K := by
    rintro _ _ rfl
    rfl
  exact key _ (swapColumns_swapColumns ..)

section Homotopy

variable (C : ColumnTurn n)

local notation "a" => C.column
local notation "b" => finRotate n C.column
local notation "G'" => G.swapColumns a b

/-- Exchanging the same two columns twice returns the original knot grid, whose `GH⁻` is torsion
exactly when it was before. -/
private theorem isTorsion_swapColumns_swapColumns_iff :
    letI := hG.unblockedHomologyModule K
    letI := ((hG.swapColumns a b).swapColumns a b).unblockedHomologyModule K
    Module.IsTorsion (Polynomial K) (((G').swapColumns a b).unblockedHomology K) ↔
      Module.IsTorsion (Polynomial K) (G.unblockedHomology K) := by
  have key : ∀ {G₁ : GridDiagram n} (h₁ : G₁.IsKnot), G₁ = G →
      (letI := hG.unblockedHomologyModule K
       letI := h₁.unblockedHomologyModule K
       Module.IsTorsion (Polynomial K) (G₁.unblockedHomology K) ↔
        Module.IsTorsion (Polynomial K) (G.unblockedHomology K)) := by
    rintro _ _ rfl
    exact Iff.rfl
  exact key _ (swapColumns_swapColumns ..)

variable {K C}

/-- **The crossing change inequality for `τ`.** Let the segments of the columns `a` and
`b = finRotate n a` of a knot grid `G` interleave with `O_a` on the arc of column `b`, and let `C`
turn in the row of `O_a`. Suppose that the crossing change maps, the commutation map `Φ` of `C`
and the commutation map `Ψ` of `G' = G.swapColumns a b` turning in the row of `X_b`, have
composites `ΨΦ` and `ΦΨ` chain homotopic to multiplication by `V_b` and `V_a`. Then
`τ(G) - 1 ≤ τ(G') ≤ τ(G)`. -/
theorem tau_swapColumns_mem_Icc_of_homotopy
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b) (hs : C.turnRow = G.O a)
    (hH : ∃ H : GridChainMinus K n →ₗ[MvPolynomial (Fin n) K] GridChainMinus K n,
      ∀ c, G.unblockedDifferential K (H c) + H (G.unblockedDifferential K c) =
        (MvPolynomial.X b : MvPolynomial (Fin n) K) • c +
          (G').commutationMap K (C.withTurnRow (G.X b)) (G.commutationMap K C c))
    (hH' : ∃ H' : GridChainMinus K n →ₗ[MvPolynomial (Fin n) K] GridChainMinus K n,
      ∀ c, (G').unblockedDifferential K (H' c) + H' ((G').unblockedDifferential K c) =
        (MvPolynomial.X a : MvPolynomial (Fin n) K) • c +
          ((G').swapColumns a b).commutationMap K ((C.withTurnRow (G.X b)).withTurnRow (G.O a))
            ((G').commutationMap K (C.withTurnRow (G.X b)) c)) :
    (hG.swapColumns a b).tau K ∈ Set.Icc (hG.tau K - 1) (hG.tau K) := by
  obtain ⟨H, hH⟩ := hH
  obtain ⟨H', hH'⟩ := hH'
  let _ := hG.unblockedHomologyModule K
  let _ := (hG.swapColumns a b).unblockedHomologyModule K
  let _ := ((hG.swapColumns a b).swapColumns a b).unblockedHomologyModule K
  have hp (c : Fin n) :
      aeval (fun _ => (Polynomial.X : Polynomial K)) (MvPolynomial.X c : MvPolynomial (Fin n) K) =
        Polynomial.X ^ 1 := by
    rw [aeval_X, pow_one]
  -- In `G'` the markings of the exchanged columns appear in the other cyclic order, so the
  -- commutation map back has the bidegree of multiplication by `U`.
  have hΦ := commutationBidegree_eq_zero_of_mem_columnArc C h hO hs
  have hΨ := commutationBidegree_eq_of_notMem_columnArc (G := G') (C.withTurnRow (G.X b))
    (((columnsInterleaving_swapColumns G _ _).mpr h.symm))
    (fun hO' => h.O_swapColumns_mem_columnArc_iff.mp hO' hO)
    (by simp [swapColumns_X, GridState.swapColumns_apply])
  have hΨ' := (hG.swapColumns a b).not_isTorsion_swapColumns_of_homotopy K
    (C.withTurnRow (G.X b)) (G.O a) H' (hp a) hH'
  by_cases hT : Module.IsTorsion (Polynomial K) (G.unblockedHomology K)
  · -- Both homologies are torsion, and both invariants vanish.
    have hT' : Module.IsTorsion (Polynomial K) ((G').unblockedHomology K) := by
      by_contra hT'
      exact (hΨ' hT') ((isTorsion_swapColumns_swapColumns_iff hG K C).mpr hT)
    rw [hG.tau_eq_zero_of_isTorsion K hT, (hG.swapColumns a b).tau_eq_zero_of_isTorsion K hT']
    simp
  · have h₁ := hG.tau_swapColumns_le_of_homotopy K C (G.X b) H (hp b) hH hT
    have h₂ := (hG.swapColumns a b).tau_swapColumns_le_of_homotopy K (C.withTurnRow (G.X b))
      (G.O a) H' (hp a) hH' (hG.not_isTorsion_swapColumns_of_homotopy K C (G.X b) H (hp b) hH hT)
    rw [hΦ, Prod.snd_zero, sub_zero] at h₁
    rw [hΨ, tau_swapColumns_swapColumns hG K, sub_neg_eq_add] at h₂
    exact ⟨by linarith, h₁⟩

end Homotopy

/-! ### Unconditional crossing-change bounds on knot diagrams -/

section DiagramBounds

/-- **The crossing-change inequality for `O_a` on the arc of column `b`.** If the segments of the
columns `a` and `b = finRotate n a` of a knot grid `G` interleave with `O_a` on the arc of column
`b`, then `τ(G) - 1 ≤ τ(G.swapColumns a b) ≤ τ(G)`. -/
theorem tau_swapColumns_mem_Icc_of_mem_columnArc {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a))
    (hO : G.O a ∈ G.columnArc (finRotate n a)) :
    (hG.swapColumns a (finRotate n a)).tau K ∈ Set.Icc (hG.tau K - 1) (hG.tau K) := by
  let C : ColumnTurn n := ⟨a, G.O a, h.ne⟩
  refine hG.tau_swapColumns_mem_Icc_of_homotopy (C := C) h hO rfl
    ⟨G.crossingChangeHomotopy K C (G.X (finRotate n a)),
      unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc K h hO rfl rfl⟩
    ⟨(G.swapColumns a (finRotate n a)).crossingChangeHomotopy K
        (C.withTurnRow (G.X (finRotate n a))) (G.O a),
      unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc K
        ((columnsInterleaving_swapColumns G a (finRotate n a)).mpr h.symm)
        (fun hO' => h.O_swapColumns_mem_columnArc_iff.mp hO' hO)
        (by simp [C, swapColumns_X, GridState.swapColumns_apply])
        (by simp [C, swapColumns_O, GridState.swapColumns_apply])⟩

/-- **The crossing-change inequality for `O_a` off the arc of column `b`.** If the segments of the
columns `a` and `b = finRotate n a` of a knot grid `G` interleave with `O_a` off the arc of column
`b`, then `τ(G) ≤ τ(G.swapColumns a b) ≤ τ(G) + 1`. -/
theorem tau_swapColumns_mem_Icc_of_notMem_columnArc {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a))
    (hO : G.O a ∉ G.columnArc (finRotate n a)) :
    (hG.swapColumns a (finRotate n a)).tau K ∈ Set.Icc (hG.tau K) (hG.tau K + 1) := by
  obtain ⟨h₁, h₂⟩ := (hG.swapColumns a (finRotate n a)).tau_swapColumns_mem_Icc_of_mem_columnArc K
    ((columnsInterleaving_swapColumns G a (finRotate n a)).mpr h.symm)
    (h.O_swapColumns_mem_columnArc_iff.mpr hO)
  rw [tau_swapColumns_swapColumns hG K] at h₁ h₂
  exact ⟨h₂, by linarith⟩

/-- Exchanging two cyclically adjacent interleaving columns of a knot grid changes `τ` by at most
`1`. -/
theorem natAbs_tau_swapColumns_sub_le_one {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a)) :
    ((hG.swapColumns a (finRotate n a)).tau K - hG.tau K).natAbs ≤ 1 := by
  by_cases hO : G.O a ∈ G.columnArc (finRotate n a)
  · obtain ⟨h₁, h₂⟩ := hG.tau_swapColumns_mem_Icc_of_mem_columnArc K h hO
    omega
  · obtain ⟨h₁, h₂⟩ := hG.tau_swapColumns_mem_Icc_of_notMem_columnArc K h hO
    omega

omit hG in
/-- Diagonal reflection of a knot grid preserves `τ`. -/
@[simp]
theorem tau_transpose (hGt : G.transpose.IsKnot) :
    hGt.tau K = (G.isKnot_transpose.mp hGt).tau K :=
  ((G.isKnot_transpose.mp hGt).unblockedHomologyIsomorphic_transpose K).symm.tau_eq

/-- A column cross-commutation between knot grids changes `τ` by at most `1`. -/
theorem natAbs_tau_sub_le_one_of_isColumnCrossCommutation {H : GridDiagram n} (hH : H.IsKnot)
    (h : G.IsColumnCrossCommutation H) :
    (hH.tau K - hG.tau K).natAbs ≤ 1 := by
  rcases (isColumnCrossCommutation_iff G H).mp h with ⟨a, ha, rfl⟩
  exact hG.natAbs_tau_swapColumns_sub_le_one K ha

/-- A row cross-commutation between knot grids changes `τ` by at most `1`. -/
theorem natAbs_tau_sub_le_one_of_isRowCrossCommutation {H : GridDiagram n} (hH : H.IsKnot)
    (h : G.IsRowCrossCommutation H) :
    (hH.tau K - hG.tau K).natAbs ≤ 1 := by
  have hG' : G.transpose.IsKnot := G.isKnot_transpose.mpr hG
  have hH' : H.transpose.IsKnot := H.isKnot_transpose.mpr hH
  simpa only [tau_transpose] using hG'.natAbs_tau_sub_le_one_of_isColumnCrossCommutation K hH'
    ((isColumnCrossCommutation_transpose G H).mpr h)

/-- Any cross-commutation (row or column) between knot grids changes `τ` by at most `1`. -/
theorem natAbs_tau_sub_le_one_of_isCrossCommutation {H : GridDiagram n} (hH : H.IsKnot)
    (h : G.IsCrossCommutation H) :
    (hH.tau K - hG.tau K).natAbs ≤ 1 := by
  rcases (isCrossCommutation_iff G H).mp h with h | h
  · exact hG.natAbs_tau_sub_le_one_of_isRowCrossCommutation K hH h
  · exact hG.natAbs_tau_sub_le_one_of_isColumnCrossCommutation K hH h

/-- Any cross-commutation between knot grids keeps `τ` within `[τ(G) - 1, τ(G) + 1]`. -/
theorem tau_mem_Icc_of_isCrossCommutation {H : GridDiagram n} (hH : H.IsKnot)
    (h : G.IsCrossCommutation H) :
    hH.tau K ∈ Set.Icc (hG.tau K - 1) (hG.tau K + 1) := by
  have hle := hG.natAbs_tau_sub_le_one_of_isCrossCommutation K hH h
  exact ⟨by omega, by omega⟩

end DiagramBounds

end IsKnot

end GridDiagram

/-! ### Crossing changes, graph distance, and the unknotting bound on grid knots -/

namespace GridLink

/-- A crossing change preserves whether a grid link is a knot. -/
theorem IsCrossingChange.isKnot_iff {L L' : GridLink} (h : IsCrossingChange L L') :
    L'.IsKnot ↔ L.IsKnot := by
  rw [isKnot_def, h.componentCount_eq, isKnot_def]

/-- Diagonal reflection of a grid knot preserves `τ`. -/
@[simp]
theorem IsKnot.tau_transpose {L : GridLink} (hL : L.transpose.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    hL.tau K = (isKnot_transpose.mp hL).tau K := by
  induction L using GridLink.ind with
  | h G =>
    have hG : G.IsKnot := (isKnot_toGridLink G).mp (isKnot_transpose.mp hL)
    rw [hL.tau_eq_of_toGridLink_eq K (G.isKnot_transpose.mpr hG) (transpose_toGridLink G).symm,
      IsKnot.tau_toGridLink, GridDiagram.IsKnot.tau_transpose]

/-- A single crossing change between grid knots changes `τ` by at most `1`. -/
theorem IsCrossingChange.natAbs_tau_sub_le_one {L L' : GridLink} (h : IsCrossingChange L L')
    (hL : L.IsKnot) (hL' : L'.IsKnot) (K : Type*) [CommRing K] [CharP K 2] :
    (hL'.tau K - hL.tau K).natAbs ≤ 1 := by
  obtain ⟨n, G, G', hcross, rfl, rfl⟩ := (isCrossingChange_iff L L').mp h
  rw [IsKnot.tau_toGridLink, IsKnot.tau_toGridLink]
  exact ((isKnot_toGridLink G).mp hL).natAbs_tau_sub_le_one_of_isCrossCommutation K
    ((isKnot_toGridLink G').mp hL') hcross

/-- Along a single crossing change between grid knots, `|τ(L') - τ(L)| ≤ 1`. -/
theorem IsCrossingChange.abs_tau_sub_le_one {L L' : GridLink} (h : IsCrossingChange L L')
    (hL : L.IsKnot) (hL' : L'.IsKnot) (K : Type*) [CommRing K] [CharP K 2] :
    |hL'.tau K - hL.tau K| ≤ 1 := by
  rw [Int.abs_eq_natAbs]
  exact Nat.cast_le.mpr (h.natAbs_tau_sub_le_one hL hL' K)

/-- Along a single crossing change between grid knots, `τ(L') ∈ [τ(L) - 1, τ(L) + 1]`. -/
theorem IsCrossingChange.tau_mem_Icc {L L' : GridLink} (h : IsCrossingChange L L')
    (hL : L.IsKnot) (hL' : L'.IsKnot) (K : Type*) [CommRing K] [CharP K 2] :
    hL'.tau K ∈ Set.Icc (hL.tau K - 1) (hL.tau K + 1) := by
  have hle := h.natAbs_tau_sub_le_one hL hL' K
  exact ⟨by omega, by omega⟩

namespace IsKnot

/-- Along any walk in the crossing-change graph starting at a knot, `τ` changes by at most the
length of the walk. -/
theorem natAbs_tau_sub_le_walk_length {L L' : GridLink} (hL : L.IsKnot) (hL' : L'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] (w : crossingChangeGraph.Walk L L') :
    (hL.tau K - hL'.tau K).natAbs ≤ w.length := by
  induction w with
  | nil => simp
  | @cons _ v _ hadj w ih =>
    have hcross : IsCrossingChange _ v := (crossingChangeGraph_adj.mp hadj).2
    have hv : v.IsKnot := hcross.isKnot_iff.mpr hL
    have hstep := hcross.natAbs_tau_sub_le_one hL hv K
    have hrest := ih hv hL'
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- **`τ` is `1`-Lipschitz on the crossing-change graph.** For any two grid knots `L` and `L'`,
`|τ(L) - τ(L')|` is bounded by the extended distance `crossingChangeGraph.edist L L'`. -/
theorem natAbs_tau_sub_le_edist {L L' : GridLink} (hL : L.IsKnot) (hL' : L'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    ((hL.tau K - hL'.tau K).natAbs : ℕ∞) ≤ crossingChangeGraph.edist L L' := by
  rw [SimpleGraph.edist_eq_sInf, le_sInf_iff]
  rintro _ ⟨w, rfl⟩
  exact Nat.cast_le.mpr (hL.natAbs_tau_sub_le_walk_length hL' K w)

/-- **The unknotting bound `|τ(L)| ≤ u(L)`.** Over any field of characteristic two, the absolute
value of `τ(L)` of a grid knot `L` is at most its unknotting number. -/
theorem natAbs_tau_le_unknottingNumber {L : GridLink} (hL : L.IsKnot)
    (K : Type*) [Field K] [CharP K 2] :
    ((hL.tau K).natAbs : ℕ∞) ≤ L.unknottingNumber := by
  simpa only [unknottingNumber_def, tau_unknot, sub_zero] using
    hL.natAbs_tau_sub_le_edist isKnot_unknot K

end IsKnot

/-- For a grid link `L` with finite unknotting number, `(τ(L)).natAbs ≤ u(L).toNat` over any field
of characteristic two. -/
theorem natAbs_tau_le_toNat_unknottingNumber {L : GridLink} (h : L.unknottingNumber ≠ ⊤)
    (K : Type*) [Field K] [CharP K 2] :
    ((isKnot_of_unknottingNumber_ne_top h).tau K).natAbs ≤ L.unknottingNumber.toNat :=
  ENat.natCast_le_natCast.mp <| by
    rw [ENat.natCast_toNat h]
    exact (isKnot_of_unknottingNumber_ne_top h).natAbs_tau_le_unknottingNumber K

/-- For a grid link `L` with finite unknotting number, `|τ(L)| ≤ u(L).toNat` as integers over any
field of characteristic two. -/
theorem abs_tau_le_toNat_unknottingNumber {L : GridLink} (h : L.unknottingNumber ≠ ⊤)
    (K : Type*) [Field K] [CharP K 2] :
    |(isKnot_of_unknottingNumber_ne_top h).tau K| ≤ (L.unknottingNumber.toNat : ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact Nat.cast_le.mpr (natAbs_tau_le_toNat_unknottingNumber h K)

end GridLink

/-- **The unknotting bound on a knot grid diagram.** Over any field of characteristic two, the
absolute value of `τ(G)` is at most the unknotting number of the grid knot presented by `G`. -/
theorem GridDiagram.IsKnot.natAbs_tau_le_unknottingNumber {n : ℕ} {G : GridDiagram n}
    (hG : G.IsKnot) (K : Type*) [Field K] [CharP K 2] :
    ((hG.tau K).natAbs : ℕ∞) ≤ G.toGridLink.unknottingNumber := by
  simpa only [GridLink.IsKnot.tau_toGridLink] using
    ((GridLink.isKnot_toGridLink G).mpr hG).natAbs_tau_le_unknottingNumber K

end TauCeti
