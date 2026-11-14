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

/-!
# Crossing change maps, the crossing-change inequality for `τ`, and the unknotting bound

Let `C` be a column turn at the columns `a = C.column` and `b = finRotate n a` of a grid diagram
`G`, and let `G' = G.swapColumns a b`. Write `Φ : GC⁻(G) → GC⁻(G')` for the commutation map of
`C` and `Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning at the same columns in
another row `t`; the target of `Ψ` is the complex of `G'.swapColumns a b`, which is `G`. This file
combines the crossing-change chain homotopies (`CrossingChange/Homotopy/Equation.lean`) with the
graded transfer lemmas (`Homology/Commutation/Tau.lean`) to prove the unconditional crossing-change
inequality for `τ` and the bound of `|τ|` by the unknotting number of a grid knot.

If the segments of the columns `a` and `b` interleave with `O_a` on the arc of column `b`, the
crossing-change maps are the commutation map `Φ` turning in the row of `O_a`, of Alexander degree
`0`, and the commutation map `Ψ` of `G'` turning in the row of `X_b`, of Alexander degree `-1`. By
`GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc` and
`GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc`, the hexagon
homotopies exhibit `Ψ ∘ Φ` as chain homotopic to multiplication by `V_b` and `Φ ∘ Ψ` as chain
homotopic to multiplication by `V_a` over any commutative ring of characteristic two. Consequently
`τ(G) - 1 ≤ τ(G') ≤ τ(G)` (`GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_mem_columnArc`), while in
the opposite cyclic order `τ(G) ≤ τ(G') ≤ τ(G) + 1`
(`GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_notMem_columnArc`).

Diagonal reflection reduces row cross-commutations to column cross-commutations, so any single
cross-commutation of knot diagrams changes `τ` by at most `1`
(`GridDiagram.IsCrossCommutation.abs_tau_sub_le_one`). Descending to `GridLink`, a crossing change
between grid knots changes `τ` by at most `1` (`GridLink.IsCrossingChange.abs_tau_sub_le_one`),
summing along paths in `GridLink.crossingChangeGraph` bounds `|τ(L) - τ(L')|` by the graph distance,
and over a field of characteristic two (where `τ(unknot) = 0`) this yields the fundamental bound
`|τ(L)| ≤ u(L)` (`GridLink.IsKnot.natAbs_tau_le_unknottingNumber` and
`GridLink.IsKnot.abs_tau_le_of_unknottingNumber_le`).

## Main results

* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_mem_columnArc` and
  `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_notMem_columnArc`: the unconditional
  directed crossing-change inequalities for `τ` across adjacent interleaving columns.
* `TauCeti.GridDiagram.IsCrossCommutation.abs_tau_sub_le_one`: any row or column cross-commutation
  changes `τ` by at most `1`.
* `TauCeti.GridLink.IsCrossingChange.abs_tau_sub_le_one`: a crossing change between grid knots
  changes `τ` by at most `1`.
* `TauCeti.GridLink.IsKnot.natAbs_tau_sub_le_edist`: `|τ(L) - τ(L')|` is bounded by distance in
  `GridLink.crossingChangeGraph`.
* `TauCeti.GridLink.IsKnot.natAbs_tau_le_unknottingNumber` and
  `TauCeti.GridLink.IsKnot.abs_tau_le_of_unknottingNumber_le`: **the unknotting bound `|τ| ≤ u`**
  for grid knots over any field of characteristic two.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 6.1 and 6.2, Corollary 6.2.4 (`|τ(K)| ≤ u(K)`).
* P. Ozsváth, Z. Szabó, *Knot Floer homology and the four-ball genus*, Geom. Topol. 7 (2003),
  615--639.
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  arXiv:1011.5265: the crossing change inequality for `τ` from grid diagrams.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

namespace IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

section Homotopy

variable (C : ColumnTurn n)

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

/-- **The crossing change inequality for `τ` from abstract chain homotopies.** Let the segments of
the columns `a` and `b = finRotate n a` of a knot grid `G` interleave with `O_a` on the arc of
column `b`, and let `C` turn in the row of `O_a`. Suppose that the crossing change maps, the
commutation map `Φ` of `C` and the commutation map `Ψ` of `G' = G.swapColumns a b` turning in the
row of `X_b`, have composites `ΨΦ` and `ΦΨ` chain homotopic to multiplication by `V_b` and `V_a`.
Then `τ(G) - 1 ≤ τ(G') ≤ τ(G)`. -/
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

/-- **The crossing-change inequality for `τ` (`O_a` on the arc of column `b`).** If the segments of
the adjacent columns `a` and `b = finRotate n a` of a knot grid `G` interleave with `O_a` on the
arc of column `b`, then over any commutative ring `K` of characteristic two,
`τ(G) - 1 ≤ τ(G.swapColumns a b) ≤ τ(G)`. -/
theorem tau_swapColumns_mem_Icc_of_mem_columnArc {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a))
    (hO : G.O a ∈ G.columnArc (finRotate n a)) :
    (hG.swapColumns a (finRotate n a)).tau K ∈ Set.Icc (hG.tau K - 1) (hG.tau K) := by
  let C : ColumnTurn n := ⟨a, G.O a, h.ne⟩
  refine hG.tau_swapColumns_mem_Icc_of_homotopy (C := C) h hO rfl
    ⟨G.crossingChangeHomotopy K C (G.X (finRotate n a)),
      G.unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc
        C (G.X (finRotate n a)) K h hO rfl rfl⟩
    ⟨(G.swapColumns a (finRotate n a)).crossingChangeHomotopy K
        (C.withTurnRow (G.X (finRotate n a))) (G.O a),
      (G.swapColumns a (finRotate n a))
        |>.unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc
          (C.withTurnRow (G.X (finRotate n a))) (G.O a) K
          ((columnsInterleaving_swapColumns G a (finRotate n a)).mpr h.symm)
          (fun hO' => h.O_swapColumns_mem_columnArc_iff.mp hO' hO)
          (by simp [C, swapColumns_X, GridState.swapColumns_apply])
          (by simp [C, swapColumns_O, GridState.swapColumns_apply])⟩

/-- **The crossing-change inequality for `τ` (`O_a` off the arc of column `b`).** If the segments
of the adjacent columns `a` and `b = finRotate n a` of a knot grid `G` interleave with `O_a` off
the arc of column `b`, then over any commutative ring `K` of characteristic two,
`τ(G) ≤ τ(G.swapColumns a b) ≤ τ(G) + 1`. -/
theorem tau_swapColumns_mem_Icc_of_notMem_columnArc {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a))
    (hO : G.O a ∉ G.columnArc (finRotate n a)) :
    (hG.swapColumns a (finRotate n a)).tau K ∈ Set.Icc (hG.tau K) (hG.tau K + 1) := by
  have hIcc := (hG.swapColumns a (finRotate n a)).tau_swapColumns_mem_Icc_of_mem_columnArc K
    ((columnsInterleaving_swapColumns G a (finRotate n a)).mpr h.symm)
    (h.O_swapColumns_mem_columnArc_iff.mpr hO)
  rw [tau_swapColumns_swapColumns hG K ⟨a, G.O a, h.ne⟩, Set.mem_Icc] at hIcc
  rw [Set.mem_Icc]
  omega

/-- Exchanging two cyclically adjacent interleaving columns of a knot grid changes `τ` by at most
`1`. -/
theorem abs_tau_swapColumns_sub_le_one {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a)) :
    |(hG.swapColumns a (finRotate n a)).tau K - hG.tau K| ≤ 1 := by
  by_cases hO : G.O a ∈ G.columnArc (finRotate n a)
  · have hIcc := Set.mem_Icc.mp (hG.tau_swapColumns_mem_Icc_of_mem_columnArc K h hO)
    exact abs_le.mpr ⟨by omega, by omega⟩
  · have hIcc := Set.mem_Icc.mp (hG.tau_swapColumns_mem_Icc_of_notMem_columnArc K h hO)
    exact abs_le.mpr ⟨by omega, by omega⟩

end IsKnot

section CrossCommutation

variable {n : ℕ} {G G' : GridDiagram n}

/-- A column cross-commutation between knot grid diagrams changes `τ` by at most `1`. -/
theorem IsColumnCrossCommutation.abs_tau_sub_le_one
    (h : G.IsColumnCrossCommutation G') (K : Type*) [CommRing K] [CharP K 2]
    (hG : G.IsKnot) (hG' : G'.IsKnot) :
    |hG'.tau K - hG.tau K| ≤ 1 := by
  obtain ⟨a, ha, rfl⟩ := (isColumnCrossCommutation_iff G G').mp h
  exact hG.abs_tau_swapColumns_sub_le_one K ha

/-- A row cross-commutation between knot grid diagrams changes `τ` by at most `1`. -/
theorem IsRowCrossCommutation.abs_tau_sub_le_one
    (h : G.IsRowCrossCommutation G') (K : Type*) [CommRing K] [CharP K 2]
    (hG : G.IsKnot) (hG' : G'.IsKnot) :
    |hG'.tau K - hG.tau K| ≤ 1 := by
  have hcol : G.transpose.IsColumnCrossCommutation G'.transpose :=
    (isColumnCrossCommutation_transpose G G').mpr h
  simpa only [IsKnot.tau_transpose] using
    hcol.abs_tau_sub_le_one K ((G.isKnot_transpose).mpr hG) ((G'.isKnot_transpose).mpr hG')

/-- Any cross-commutation, whether of rows or of columns, changes `τ` by at most `1`. -/
theorem IsCrossCommutation.abs_tau_sub_le_one
    (h : G.IsCrossCommutation G') (K : Type*) [CommRing K] [CharP K 2]
    (hG : G.IsKnot) (hG' : G'.IsKnot) :
    |hG'.tau K - hG.tau K| ≤ 1 := by
  rcases (isCrossCommutation_iff G G').mp h with h | h
  · exact h.abs_tau_sub_le_one K hG hG'
  · exact h.abs_tau_sub_le_one K hG hG'

end CrossCommutation

end GridDiagram

namespace GridLink

/-- A crossing change between grid knots changes `τ` by at most `1`. -/
theorem IsCrossingChange.abs_tau_sub_le_one {L L' : GridLink}
    (h : IsCrossingChange L L') (K : Type*) [CommRing K] [CharP K 2]
    (hL : L.IsKnot) (hL' : L'.IsKnot) :
    |hL'.tau K - hL.tau K| ≤ 1 := by
  obtain ⟨n, G, G', hcross, rfl, rfl⟩ := (isCrossingChange_iff L L').mp h
  rw [IsKnot.tau_toGridLink, IsKnot.tau_toGridLink]
  exact hcross.abs_tau_sub_le_one K ((isKnot_toGridLink G).mp hL) ((isKnot_toGridLink G').mp hL')

namespace IsKnot

/-- Along a walk in the crossing-change graph between two grid knots, `τ` changes by at most the
length of the walk. -/
theorem abs_tau_sub_le_walk_length {L L' : GridLink} (hL : L.IsKnot) (hL' : L'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] (w : crossingChangeGraph.Walk L L') :
    |hL.tau K - hL'.tau K| ≤ w.length := by
  induction w with
  | nil => simp
  | @cons u v _ hadj w ih =>
    have hcross : IsCrossingChange u v := (crossingChangeGraph_adj.mp hadj).2
    have hv : v.IsKnot := hcross.isKnot_iff.mpr hL
    have h₁ := hcross.symm.abs_tau_sub_le_one K hv hL
    have h₂ := ih hv hL'
    have htri := abs_sub_le (hL.tau K) (hv.tau K) (hL'.tau K)
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- For any two grid knots `L` and `L'`, `|τ(L) - τ(L')|` is bounded by their distance in the
crossing-change graph. -/
theorem natAbs_tau_sub_le_edist {L L' : GridLink} (hL : L.IsKnot) (hL' : L'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    ((hL.tau K - hL'.tau K).natAbs : ℕ∞) ≤ crossingChangeGraph.edist L L' := by
  rcases eq_or_ne (crossingChangeGraph.edist L L') ⊤ with htop | hfin
  · rw [htop]
    exact le_top
  · obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top hfin
    rw [← hw, Nat.cast_le, ← Int.ofNat_le, Int.natCast_natAbs]
    exact hL.abs_tau_sub_le_walk_length hL' K w

variable {L : GridLink} (hL : L.IsKnot) (K : Type*) [Field K] [CharP K 2]

/-- **The unknotting bound for `τ` (`|τ(L)| ≤ u(L)`).** Over any field of characteristic two, the
absolute value of `τ` of a grid knot is at most its unknotting number. -/
theorem natAbs_tau_le_unknottingNumber :
    ((hL.tau K).natAbs : ℕ∞) ≤ L.unknottingNumber := by
  simpa [unknottingNumber_def, tau_unknot] using hL.natAbs_tau_sub_le_edist isKnot_unknot K

/-- Over any field of characteristic two, if a grid knot can be unknotted in at most `u` crossing
changes, then `|τ(L)| ≤ u`. -/
theorem abs_tau_le_of_unknottingNumber_le {u : ℕ} (hu : L.unknottingNumber ≤ u) :
    |hL.tau K| ≤ u := by
  have h := (hL.natAbs_tau_le_unknottingNumber K).trans hu
  rw [Nat.cast_le, ← Int.ofNat_le, Int.natCast_natAbs] at h
  exact h

end IsKnot

end GridLink

end TauCeti
