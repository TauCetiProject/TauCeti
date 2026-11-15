/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Grading
public import TauCeti.KnotTheory.Grid.Homology.Commutation.Tau
import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Equation
import TauCeti.KnotTheory.Grid.Homology.Transpose

/-!
# Crossing change maps and the invariant `τ`

Let `C` be a column turn at the columns `a = C.column` and `b = finRotate n a` of a grid diagram
`G`, and let `G' = G.swapColumns a b`. Write `Φ : GC⁻(G) → GC⁻(G')` for the commutation map of
`C` and `Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning at the same columns in
another row `t`; the target of `Ψ` is the complex of `G'.swapColumns a b`, which is `G`. This file
turns the chain homotopies of the crossing change maps into the crossing change inequality for `τ`.

The comparison along a single column turn is in `Homology/Commutation/Tau.lean`: if
`ΨΦ` is chain homotopic to multiplication by `p` with `p(U, …, U) = U ^ k`, then `GH⁻(G')` is not
torsion if `GH⁻(G)` is not (`GridDiagram.IsKnot.not_isTorsion_swapColumns_of_homotopy`), and
`τ(G')` is at most `τ(G)` minus the Alexander degree of `Φ`
(`GridDiagram.IsKnot.tau_swapColumns_le_of_homotopy`).

The main application is to a crossing change. If the segments of the columns `a` and `b`
interleave with `O_a` on the arc of column `b`, the crossing change maps are the commutation map
`Φ` turning in the row of `O_a`, of Alexander degree `0`, and the commutation map `Ψ` of `G'`
turning in the row of `X_b`, of Alexander degree `-1`
(`GridDiagram.commutationBidegree_eq_zero_of_mem_columnArc` and
`GridDiagram.commutationBidegree_eq_of_notMem_columnArc`). By the hexagon chain homotopies of
`CrossingChange/Homotopy/Equation.lean`, `ΨΦ` is chain homotopic to multiplication by `V_b` and
`ΦΨ` to multiplication by `V_a`, giving `τ(G) - 1 ≤ τ(G') ≤ τ(G)`
(`GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_mem_columnArc`), and in the opposite cyclic order
`τ(G) ≤ τ(G') ≤ τ(G) + 1` (`GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_notMem_columnArc`). No
assumption that `GH⁻` is non-torsion is needed: the two composites show that `GH⁻(G)` and
`GH⁻(G')` are torsion together, and then both invariants vanish. Diagonal reflection extends the
resulting bound `|τ(G') - τ(G)| ≤ 1` from column cross-commutations to row cross-commutations and
hence to all cross-commutations (`GridDiagram.IsCrossCommutation.natAbs_tau_sub_le_one`).

## Main results

* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_homotopy`: the abstract crossing change
  inequality `τ(G) - 1 ≤ τ(G') ≤ τ(G)` from given chain homotopies.
* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_mem_columnArc` and
  `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_notMem_columnArc`: **the directional
  crossing change inequalities** `τ(G) - 1 ≤ τ(G') ≤ τ(G)` and `τ(G) ≤ τ(G') ≤ τ(G) + 1` across
  exchanging two adjacent interleaving columns.
* `TauCeti.GridDiagram.IsKnot.natAbs_tau_swapColumns_sub_le_one` and
  `TauCeti.GridDiagram.IsCrossCommutation.natAbs_tau_sub_le_one`: any cross-commutation of knot
  grids changes `τ` by at most `1`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 6.1 and 6.2: the crossing change maps, their composites, and
  the resulting inequality for `τ`.
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  arXiv:1011.5265: the crossing change inequality for `τ` from grid diagrams.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

namespace IsKnot

section Homotopy

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]
  (C : ColumnTurn n)

local notation "a" => C.column
local notation "b" => finRotate n C.column
local notation "G'" => G.swapColumns a b

/-- Exchanging the same two columns twice returns the original knot grid, with the same `τ`. -/
private theorem tau_swapColumns_swapColumns :
    ((hG.swapColumns a b).swapColumns a b).tau K = hG.tau K := by
  have key : ∀ {G₁ : GridDiagram n} (h₁ : G₁.IsKnot), G₁ = G → h₁.tau K = hG.tau K := by
    rintro _ _ rfl
    rfl
  exact key _ (swapColumns_swapColumns ..)

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
    rw [hΨ, tau_swapColumns_swapColumns hG K C, sub_neg_eq_add] at h₂
    exact ⟨by linarith, h₁⟩

end Homotopy

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- **The crossing change inequality for `τ` when `O_a` lies on the arc of column `b`.** If the
segments of the cyclically adjacent columns `a` and `finRotate n a` of a knot grid `G` interleave
with `O_a` on the arc of column `finRotate n a`, then over any commutative ring of characteristic
two, `τ(G) - 1 ≤ τ(G.swapColumns a (finRotate n a)) ≤ τ(G)`. -/
theorem tau_swapColumns_mem_Icc_of_mem_columnArc {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a))
    (hO : G.O a ∈ G.columnArc (finRotate n a)) :
    (hG.swapColumns a (finRotate n a)).tau K ∈ Set.Icc (hG.tau K - 1) (hG.tau K) := by
  let C : ColumnTurn n := ⟨a, G.O a, h.ne⟩
  refine hG.tau_swapColumns_mem_Icc_of_homotopy (C := C) h hO rfl
    ⟨G.crossingChangeHomotopy K C (G.X (finRotate n a)),
      unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc
        (G := G) (C := C) (t := G.X (finRotate n a)) K h hO rfl rfl⟩
    ⟨(G.swapColumns a (finRotate n a)).crossingChangeHomotopy K
        (C.withTurnRow (G.X (finRotate n a))) (G.O a),
      unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc
        (G := G.swapColumns a (finRotate n a))
        (C := C.withTurnRow (G.X (finRotate n a))) (t := G.O a) K
        ((columnsInterleaving_swapColumns G a (finRotate n a)).mpr h.symm)
        (fun hO' => h.O_swapColumns_mem_columnArc_iff.mp hO' hO)
        (by simp [C, swapColumns_X, GridState.swapColumns_apply])
        (by simp [C, swapColumns_O, GridState.swapColumns_apply])⟩

/-- **The crossing change inequality for `τ` when `O_a` lies off the arc of column `b`.** If the
segments of the cyclically adjacent columns `a` and `finRotate n a` of a knot grid `G` interleave
with `O_a` off the arc of column `finRotate n a`, then over any commutative ring of characteristic
two, `τ(G) ≤ τ(G.swapColumns a (finRotate n a)) ≤ τ(G) + 1`. -/
theorem tau_swapColumns_mem_Icc_of_notMem_columnArc {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a))
    (hO : G.O a ∉ G.columnArc (finRotate n a)) :
    (hG.swapColumns a (finRotate n a)).tau K ∈ Set.Icc (hG.tau K) (hG.tau K + 1) := by
  have hmem := (hG.swapColumns a (finRotate n a)).tau_swapColumns_mem_Icc_of_mem_columnArc K
    ((columnsInterleaving_swapColumns G a (finRotate n a)).mpr h.symm)
    (h.O_swapColumns_mem_columnArc_iff.mpr hO)
  rw [tau_swapColumns_swapColumns hG K ⟨a, a, h.ne⟩] at hmem
  exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩

/-- Exchanging two cyclically adjacent interleaving columns of a knot grid changes `τ` by at most
one. -/
theorem natAbs_tau_swapColumns_sub_le_one {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a)) :
    ((hG.swapColumns a (finRotate n a)).tau K - hG.tau K).natAbs ≤ 1 := by
  by_cases hO : G.O a ∈ G.columnArc (finRotate n a)
  · obtain ⟨h₁, h₂⟩ := hG.tau_swapColumns_mem_Icc_of_mem_columnArc K h hO
    omega
  · obtain ⟨h₁, h₂⟩ := hG.tau_swapColumns_mem_Icc_of_notMem_columnArc K h hO
    omega

end IsKnot

/-- A column cross-commutation between knot grids changes `τ` by at most one. -/
theorem IsColumnCrossCommutation.natAbs_tau_sub_le_one {n : ℕ} {G G' : GridDiagram n}
    (h : G.IsColumnCrossCommutation G') (hG : G.IsKnot) (hG' : G'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    (hG'.tau K - hG.tau K).natAbs ≤ 1 := by
  obtain ⟨a, ha, rfl⟩ := (isColumnCrossCommutation_iff G G').mp h
  exact hG.natAbs_tau_swapColumns_sub_le_one K ha

/-- A row cross-commutation between knot grids changes `τ` by at most one, by diagonal reflection
to a column cross-commutation. -/
theorem IsRowCrossCommutation.natAbs_tau_sub_le_one {n : ℕ} {G G' : GridDiagram n}
    (h : G.IsRowCrossCommutation G') (hG : G.IsKnot) (hG' : G'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    (hG'.tau K - hG.tau K).natAbs ≤ 1 := by
  rw [(hG.unblockedHomologyIsomorphic_transpose K).tau_eq,
    (hG'.unblockedHomologyIsomorphic_transpose K).tau_eq]
  exact ((isColumnCrossCommutation_transpose G G').mpr h).natAbs_tau_sub_le_one
    ((G.isKnot_transpose).mpr hG) ((G'.isKnot_transpose).mpr hG') K

/-- Any cross-commutation, of rows or of columns, between knot grids changes `τ` by at most one. -/
theorem IsCrossCommutation.natAbs_tau_sub_le_one {n : ℕ} {G G' : GridDiagram n}
    (h : G.IsCrossCommutation G') (hG : G.IsKnot) (hG' : G'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    (hG'.tau K - hG.tau K).natAbs ≤ 1 :=
  ((isCrossCommutation_iff G G').mp h).elim (fun h => h.natAbs_tau_sub_le_one hG hG' K)
    (fun h => h.natAbs_tau_sub_le_one hG hG' K)

end GridDiagram

end TauCeti
