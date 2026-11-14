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
# Crossing change maps, `τ`, and the unknotting-number bound

Let `C` be a column turn at the columns `a = C.column` and `b = finRotate n a` of a grid diagram
`G`, and let `G' = G.swapColumns a b`. Write `Φ : GC⁻(G) → GC⁻(G')` for the commutation map of
`C` and `Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning at the same columns in
another row `t`; the target of `Ψ` is the complex of `G'.swapColumns a b`, which is `G`. This file
combines the crossing-change homotopy equations of `CrossingChange/Homotopy/Equation.lean` with the
grading computations of `CrossingChange/Grading.lean` to prove the crossing-change inequality for
`τ` and deduce the bound `|τ(L)| ≤ u(L)` by the unknotting number.

The comparison along a single column turn is in `Homology/Commutation/Tau.lean`: if
`ΨΦ` is chain homotopic to multiplication by `p` with `p(U, …, U) = U ^ k`, then `GH⁻(G')` is not
torsion if `GH⁻(G)` is not (`GridDiagram.IsKnot.not_isTorsion_swapColumns_of_homotopy`), and
`τ(G')` is at most `τ(G)` minus the Alexander degree of `Φ`
(`GridDiagram.IsKnot.tau_swapColumns_le_of_homotopy`).

If the segments of the columns `a` and `b` interleave with `O_a` on the arc of column `b`, the
crossing change maps are the commutation map `Φ` turning in the row of `O_a`, of Alexander degree
`0`, and the commutation map `Ψ` of `G'` turning in the row of `X_b`, of Alexander degree `-1`
(`GridDiagram.commutationBidegree_eq_zero_of_mem_columnArc` and
`GridDiagram.commutationBidegree_eq_of_notMem_columnArc`). By
`GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc` and
`GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc`, their two
composites `ΨΦ` and `ΦΨ` are chain homotopic to multiplication by `V_b` and `V_a`, so
`τ(G) - 1 ≤ τ(G') ≤ τ(G)` (`GridDiagram.IsKnot.tau_swapColumns_mem_Icc`). No assumption that `GH⁻`
is non-torsion is needed: the two composites show that `GH⁻(G)` and `GH⁻(G')` are torsion together,
and then both invariants vanish.

Exchanging the roles of `G` and `G'` covers the opposite cyclic order of markings, and diagonal
reflection (`GridDiagram.IsKnot.tau_transpose`) transports column cross-commutations to row
cross-commutations, so `|τ(G') - τ(G)| ≤ 1` across every cross-commutation
(`GridDiagram.IsKnot.abs_tau_sub_le_one_of_isCrossCommutation`). Descending to grid knots, `τ`
changes by at most `1` along every edge of `GridLink.crossingChangeGraph`, so
`|τ(L) - τ(L')| ≤ edist(L, L')` (`GridLink.IsKnot.natAbs_tau_sub_le_edist`) over any commutative
ring of characteristic two. Over a field of characteristic two, where `τ(unknot) = 0`, this gives
`|τ(L)| ≤ u(L)` (`GridLink.IsKnot.natAbs_tau_le_unknottingNumber`).

## Main results

* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_homotopy` and
  `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc`: `τ(G) - 1 ≤ τ(G') ≤ τ(G)` when `O_a` lies
  on the arc of column `b`.
* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_notMem_columnArc`:
  `τ(G) ≤ τ(G') ≤ τ(G) + 1` when `O_a` lies off the arc of column `b`.
* `TauCeti.GridDiagram.IsKnot.abs_tau_sub_le_one_of_isCrossCommutation`: `|τ(G') - τ(G)| ≤ 1`
  across any row or column cross-commutation.
* `TauCeti.GridLink.IsCrossingChange.abs_tau_sub_le_one`: `|τ(L) - τ(L')| ≤ 1` across a crossing
  change of grid knots.
* `TauCeti.GridLink.IsKnot.natAbs_tau_sub_le_edist`: `|τ(L) - τ(L')|` is bounded by distance in
  `GridLink.crossingChangeGraph` over every commutative ring of characteristic two.
* `TauCeti.GridLink.IsKnot.natAbs_tau_le_unknottingNumber` and
  `TauCeti.GridLink.IsKnot.abs_tau_le_of_unknottingNumber_le`: **the unknotting-number bound**,
  `|τ(L)| ≤ u(L)` over any field of characteristic two.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 6.1 and 6.2: the crossing change maps, their composites, the
  crossing change inequality for `τ`, and Corollary 6.2.4 (`|τ(K)| ≤ u(K)`).
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  arXiv:1011.5265: the crossing change inequality and unknotting bound for `τ` from grid diagrams.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

namespace IsKnot

section ColumnTurn

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

/-- **The crossing change inequality for `τ` from given homotopies.** Let the segments of the
columns `a` and `b = finRotate n a` of a knot grid `G` interleave with `O_a` on the arc of column
`b`, and let `C` turn in the row of `O_a`. Suppose that the crossing change maps, the commutation
map `Φ` of `C` and the commutation map `Ψ` of `G' = G.swapColumns a b` turning in the row of `X_b`,
have composites `ΨΦ` and `ΦΨ` chain homotopic to multiplication by `V_b` and `V_a`. Then
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

end ColumnTurn

/-! ### Unconditional crossing-change inequalities on knot diagrams -/

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- **The crossing change inequality for `τ`.** If the segments of `a` and `b = finRotate n a` in a
knot grid `G` interleave with `O_a` on the arc of column `b`, then
`τ(G) - 1 ≤ τ(G.swapColumns a b) ≤ τ(G)`. -/
theorem tau_swapColumns_mem_Icc {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a))
    (hO : G.O a ∈ G.columnArc (finRotate n a)) :
    (hG.swapColumns a (finRotate n a)).tau K ∈ Set.Icc (hG.tau K - 1) (hG.tau K) := by
  let b := finRotate n a
  let C : ColumnTurn n := ⟨a, G.O a, h.ne⟩
  let G' := G.swapColumns a b
  exact hG.tau_swapColumns_mem_Icc_of_homotopy (C := C) h hO rfl
    ⟨G.crossingChangeHomotopy K C (G.X b),
      G.unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc
        C (G.X b) K h hO rfl rfl⟩
    ⟨(G').crossingChangeHomotopy K (C.withTurnRow (G.X b)) (G.O a),
      (G').unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc
        (C.withTurnRow (G.X b)) (G.O a) K
        ((columnsInterleaving_swapColumns G a b).mpr h.symm)
        (fun hO' => h.O_swapColumns_mem_columnArc_iff.mp hO' hO)
        (by simp [G', b, C, swapColumns_X, GridState.swapColumns_apply])
        (by simp [G', b, C, swapColumns_O, GridState.swapColumns_apply])⟩

/-- **The crossing change inequality for `τ`**, for the opposite marking order: if the segments of
`a` and `b = finRotate n a` in a knot grid `G` interleave with `O_a` off the arc of column `b`,
then `τ(G) ≤ τ(G.swapColumns a b) ≤ τ(G) + 1`. -/
theorem tau_swapColumns_mem_Icc_of_notMem_columnArc {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a))
    (hO : G.O a ∉ G.columnArc (finRotate n a)) :
    (hG.swapColumns a (finRotate n a)).tau K ∈ Set.Icc (hG.tau K) (hG.tau K + 1) := by
  let b := finRotate n a
  have hrev := (hG.swapColumns a b).tau_swapColumns_mem_Icc K
    ((columnsInterleaving_swapColumns G a b).mpr h.symm)
    (h.O_swapColumns_mem_columnArc_iff.mpr hO)
  rw [tau_swapColumns_swapColumns hG K ⟨a, G.O a, h.ne⟩, Set.mem_Icc] at hrev
  exact ⟨by omega, by omega⟩

/-- Exchanging two cyclically adjacent interleaving columns of a knot grid changes `τ` by at most
one. -/
theorem abs_tau_swapColumns_sub_le_one {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a)) :
    |(hG.swapColumns a (finRotate n a)).tau K - hG.tau K| ≤ 1 := by
  by_cases hO : G.O a ∈ G.columnArc (finRotate n a)
  · obtain ⟨h₁, h₂⟩ := Set.mem_Icc.mp (hG.tau_swapColumns_mem_Icc K h hO)
    exact abs_le.mpr ⟨by omega, by omega⟩
  · obtain ⟨h₁, h₂⟩ := Set.mem_Icc.mp (hG.tau_swapColumns_mem_Icc_of_notMem_columnArc K h hO)
    exact abs_le.mpr ⟨by omega, by omega⟩

/-- A column cross-commutation between knot grids changes `τ` by at most one. -/
theorem abs_tau_sub_le_one_of_isColumnCrossCommutation {G' : GridDiagram n} (hG' : G'.IsKnot)
    (h : G.IsColumnCrossCommutation G') :
    |hG'.tau K - hG.tau K| ≤ 1 := by
  rcases (isColumnCrossCommutation_iff G G').mp h with ⟨a, ha, rfl⟩
  exact hG.abs_tau_swapColumns_sub_le_one K ha

/-- A row cross-commutation between knot grids changes `τ` by at most one, by diagonal reflection
to a column cross-commutation. -/
theorem abs_tau_sub_le_one_of_isRowCrossCommutation {G' : GridDiagram n} (hG' : G'.IsKnot)
    (h : G.IsRowCrossCommutation G') :
    |hG'.tau K - hG.tau K| ≤ 1 := by
  rw [← hG.tau_transpose K, ← hG'.tau_transpose K]
  exact ((G.isKnot_transpose).mpr hG).abs_tau_sub_le_one_of_isColumnCrossCommutation K
    ((G'.isKnot_transpose).mpr hG') ((isColumnCrossCommutation_transpose G G').mpr h)

/-- Any cross-commutation between knot grids changes `τ` by at most one. -/
theorem abs_tau_sub_le_one_of_isCrossCommutation {G' : GridDiagram n} (hG' : G'.IsKnot)
    (h : G.IsCrossCommutation G') :
    |hG'.tau K - hG.tau K| ≤ 1 := by
  rcases (isCrossCommutation_iff G G').mp h with h | h
  · exact hG.abs_tau_sub_le_one_of_isRowCrossCommutation K hG' h
  · exact hG.abs_tau_sub_le_one_of_isColumnCrossCommutation K hG' h

end IsKnot

end GridDiagram

/-! ### Crossing changes and the unknotting-number bound on grid knots -/

namespace GridLink

/-- A crossing change between grid knots changes `τ` by at most one. -/
theorem IsCrossingChange.abs_tau_sub_le_one {L L' : GridLink} (h : IsCrossingChange L L')
    (K : Type*) [CommRing K] [CharP K 2] (hL : L.IsKnot) (hL' : L'.IsKnot) :
    |hL.tau K - hL'.tau K| ≤ 1 := by
  rcases (isCrossingChange_iff L L').mp h with ⟨n, G, G', hcross, rfl, rfl⟩
  rw [IsKnot.tau_toGridLink, IsKnot.tau_toGridLink, abs_sub_comm]
  exact ((isKnot_toGridLink G).mp hL).abs_tau_sub_le_one_of_isCrossCommutation K
    ((isKnot_toGridLink G').mp hL') hcross

/-- Natural-number form of `IsCrossingChange.abs_tau_sub_le_one`. -/
theorem IsCrossingChange.natAbs_tau_sub_le_one {L L' : GridLink} (h : IsCrossingChange L L')
    (K : Type*) [CommRing K] [CharP K 2] (hL : L.IsKnot) (hL' : L'.IsKnot) :
    (hL.tau K - hL'.tau K).natAbs ≤ 1 :=
  Int.ofNat_le.mp
    (by simpa only [Int.natCast_natAbs, Nat.cast_one] using h.abs_tau_sub_le_one K hL hL')

namespace IsKnot

/-- Along any walk in `crossingChangeGraph` starting at a grid knot, `τ` changes by at most the
length of the walk. -/
theorem natAbs_tau_sub_le_walk_length {L L' : GridLink} (hL : L.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] (hL' : L'.IsKnot)
    (p : crossingChangeGraph.Walk L L') :
    (hL.tau K - hL'.tau K).natAbs ≤ p.length := by
  induction p with
  | nil => simp
  | @cons u v w hadj q ih =>
    have hcross : IsCrossingChange u v := (crossingChangeGraph_adj.mp hadj).2
    have hv : v.IsKnot := by
      rw [isKnot_def, hcross.componentCount_eq, ← isKnot_def]
      exact hL
    have hstep := hcross.natAbs_tau_sub_le_one K hL hv
    have hq := ih hv hL'
    have htri := Int.natAbs_add_le (hL.tau K - hv.tau K) (hv.tau K - hL'.tau K)
    rw [sub_add_sub_cancel] at htri
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- **Crossing-change Lipschitz bound for `τ`.** Over any commutative ring of characteristic two,
`|τ(L) - τ(L')|` is bounded by the crossing-change distance between the grid knots `L` and `L'`. -/
theorem natAbs_tau_sub_le_edist {L L' : GridLink} (hL : L.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] (hL' : L'.IsKnot) :
    ((hL.tau K - hL'.tau K).natAbs : ℕ∞) ≤ crossingChangeGraph.edist L L' := by
  by_cases htop : crossingChangeGraph.edist L L' = ⊤
  · simp [htop]
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
    rw [← hp]
    exact_mod_cast hL.natAbs_tau_sub_le_walk_length K hL' p

/-- **The unknotting-number bound for `τ`.** Over a field of characteristic two, the absolute value
of `τ` of a grid knot is at most its unknotting number: `|τ(L)| ≤ u(L)`. -/
theorem natAbs_tau_le_unknottingNumber {L : GridLink} (hL : L.IsKnot)
    (K : Type*) [Field K] [CharP K 2] :
    ((hL.tau K).natAbs : ℕ∞) ≤ L.unknottingNumber := by
  simpa only [unknottingNumber_def, tau_unknot, sub_zero] using
    hL.natAbs_tau_sub_le_edist K isKnot_unknot

/-- If a grid knot can be unknotted in at most `m` crossing changes, then `(τ(L)).natAbs ≤ m` over
any field of characteristic two. -/
theorem natAbs_tau_le_of_unknottingNumber_le {L : GridLink} (hL : L.IsKnot)
    (K : Type*) [Field K] [CharP K 2] {m : ℕ} (hu : L.unknottingNumber ≤ m) :
    (hL.tau K).natAbs ≤ m :=
  Nat.cast_le.mp ((hL.natAbs_tau_le_unknottingNumber K).trans hu)

/-- If a grid knot can be unknotted in at most `m` crossing changes, then `|τ(L)| ≤ m` over any
field of characteristic two. -/
theorem abs_tau_le_of_unknottingNumber_le {L : GridLink} (hL : L.IsKnot)
    (K : Type*) [Field K] [CharP K 2] {m : ℕ} (hu : L.unknottingNumber ≤ m) :
    |hL.tau K| ≤ m := by
  simpa only [Int.natCast_natAbs] using
    Int.ofNat_le.mpr (hL.natAbs_tau_le_of_unknottingNumber_le K hu)

end IsKnot

end GridLink

end TauCeti
