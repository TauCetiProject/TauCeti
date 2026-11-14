/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Grading
public import TauCeti.KnotTheory.Grid.CrossingChange.UnknottingNumber
public import TauCeti.KnotTheory.Grid.Homology.Commutation.Tau
public import TauCeti.KnotTheory.Grid.Move.Tau
import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Equation

/-!
# Crossing change maps, the invariant `τ`, and the unknotting bound

Let `C` be a column turn at the columns `a = C.column` and `b = finRotate n a` of a grid diagram
`G`, and let `G' = G.swapColumns a b`. Write `Φ : GC⁻(G) → GC⁻(G')` for the commutation map of
`C` and `Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning at the same columns in
another row `t`; the target of `Ψ` is the complex of `G'.swapColumns a b`, which is `G`. This file
turns the chain homotopies of the crossing change maps into the crossing change inequality for `τ`,
the Gordian distance bound on `crossingChangeGraph`, and the bound `|τ(L)| ≤ u(L)` by the
unknotting number.

The comparison along a single column turn is in `Homology/Commutation/Tau.lean`: if
`ΨΦ` is chain homotopic to multiplication by `p` with `p(U, …, U) = U ^ k`, then `GH⁻(G')` is not
torsion if `GH⁻(G)` is not (`GridDiagram.IsKnot.not_isTorsion_swapColumns_of_homotopy`), and
`τ(G')` is at most `τ(G)` minus the Alexander degree of `Φ`
(`GridDiagram.IsKnot.tau_swapColumns_le_of_homotopy`).

When the segments of the columns `a` and `b` interleave with `O_a` on the arc of column `b`, the
crossing change maps are the commutation map `Φ` turning in the row of `O_a`, of Alexander degree
`0`, and the commutation map `Ψ` of `G'` turning in the row of `X_b`, of Alexander degree `-1`
(`GridDiagram.commutationBidegree_eq_zero_of_mem_columnArc` and
`GridDiagram.commutationBidegree_eq_of_notMem_columnArc`). By
`CrossingChange/Homotopy/Equation.lean`, the hexagon maps `GridDiagram.crossingChangeHomotopy`
satisfy `∂ ∘ H + H ∘ ∂ = V_b • 1 + Ψ ∘ Φ` and `∂' ∘ H' + H' ∘ ∂' = V_a • 1 + Φ ∘ Ψ` in
characteristic two. Supplying these homotopies to
`GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_homotopy` yields the unconditional inequalities
`τ(G) - 1 ≤ τ(G') ≤ τ(G)` when `O_a ∈ columnArc b` and `τ(G) ≤ τ(G') ≤ τ(G) + 1` when
`O_a ∉ columnArc b`, over every commutative ring of characteristic two. No assumption that `GH⁻` is
non-torsion is needed: the two composites show that `GH⁻(G)` and `GH⁻(G')` are torsion together,
and then both invariants vanish.

Diagonal reflection transports column cross-commutations to row cross-commutations while preserving
`τ`, so every cross-commutation of knot diagrams and every crossing change of grid knots changes
`τ` by at most `1`. Inducting along walks in `GridLink.crossingChangeGraph` bounds `|τ(L) - τ(L')|`
by the extended crossing-change distance; specializing to `L' = unknot` over a field of
characteristic two (where `τ(unknot) = 0`) gives `|τ(L)| ≤ u(L)`.

## Main results

* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_homotopy`: `τ(G) - 1 ≤ τ(G') ≤ τ(G)` from
  abstract chain homotopies for `ΨΦ` and `ΦΨ`.
* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_mem_columnArc`,
  `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_notMem_columnArc`: **the unconditional
  crossing-change inequalities** `τ(G) - 1 ≤ τ(G') ≤ τ(G)` and `τ(G) ≤ τ(G') ≤ τ(G) + 1`.
* `TauCeti.GridDiagram.IsKnot.abs_tau_sub_tau_le_one_of_isCrossCommutation`,
  `TauCeti.GridLink.IsCrossingChange.abs_tau_sub_tau_le_one`: any cross-commutation or grid-link
  crossing change alters `τ` by at most `1`.
* `TauCeti.GridLink.IsKnot.natAbs_tau_sub_tau_le_crossingChangeGraph_edist`: **the Gordian distance
  bound**, `|τ(L) - τ(L')| ≤ edist(L, L')` in `crossingChangeGraph`.
* `TauCeti.GridLink.IsKnot.natAbs_tau_le_unknottingNumber`,
  `TauCeti.GridLink.IsKnot.abs_tau_le_of_unknottingNumber_le`: **the unknotting bound**
  `|τ(L)| ≤ u(L)` over any field of characteristic two.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 6.1 and 6.2: the crossing change maps, their composites,
  Corollary 6.1.4, and Corollary 6.1.5 (`|τ(K)| ≤ u(K)`).
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

/-- **The crossing change inequality for `τ`, from chain homotopies.** Let the segments of the
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

variable {n : ℕ} {G G' : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- **The crossing-change inequality for `O_a ∈ columnArc b`.** If the segments of columns `a` and
`b = finRotate n a` of a knot grid `G` interleave with `O_a` on the arc of column `b`, then
`τ(G) - 1 ≤ τ(G.swapColumns a b) ≤ τ(G)` over any commutative ring `K` of characteristic two. -/
theorem tau_swapColumns_mem_Icc_of_mem_columnArc {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a))
    (hO : G.O a ∈ G.columnArc (finRotate n a)) :
    (hG.swapColumns a (finRotate n a)).tau K ∈ Set.Icc (hG.tau K - 1) (hG.tau K) := by
  let C : ColumnTurn n := ⟨a, G.O a, h.ne⟩
  have hswap : (G.swapColumns a (finRotate n a)).ColumnsInterleaving a (finRotate n a) :=
    (columnsInterleaving_swapColumns G a (finRotate n a)).mpr h.symm
  have hO' : (G.swapColumns a (finRotate n a)).O a ∉
      (G.swapColumns a (finRotate n a)).columnArc (finRotate n a) :=
    fun hmem => h.O_swapColumns_mem_columnArc_iff.mp hmem hO
  exact hG.tau_swapColumns_mem_Icc_of_homotopy (C := C) h hO rfl
    ⟨G.crossingChangeHomotopy K C (G.X (finRotate n a)),
      G.unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc K h hO rfl rfl⟩
    ⟨(G.swapColumns a (finRotate n a)).crossingChangeHomotopy K
        (C.withTurnRow (G.X (finRotate n a))) (G.O a),
      GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc K
        hswap hO' (by simp [C, swapColumns_X, GridState.swapColumns_apply])
        (by simp [C, swapColumns_O, GridState.swapColumns_apply])⟩

/-- **The crossing-change inequality for `O_a ∉ columnArc b`.** If the segments of columns `a` and
`b = finRotate n a` of a knot grid `G` interleave with `O_a` off the arc of column `b`, then
`τ(G) ≤ τ(G.swapColumns a b) ≤ τ(G) + 1` over any commutative ring `K` of characteristic two. -/
theorem tau_swapColumns_mem_Icc_of_notMem_columnArc {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a))
    (hO : G.O a ∉ G.columnArc (finRotate n a)) :
    (hG.swapColumns a (finRotate n a)).tau K ∈ Set.Icc (hG.tau K) (hG.tau K + 1) := by
  let C : ColumnTurn n := ⟨a, G.O a, h.ne⟩
  have hmem := (hG.swapColumns a (finRotate n a)).tau_swapColumns_mem_Icc_of_mem_columnArc K
    ((columnsInterleaving_swapColumns G a (finRotate n a)).mpr h.symm)
    (h.O_swapColumns_mem_columnArc_iff.mpr hO)
  rw [tau_swapColumns_swapColumns hG K C, Set.mem_Icc] at hmem
  rw [Set.mem_Icc]
  omega

/-- Exchanging two cyclically adjacent interleaving columns of a knot grid changes `τ` by at most
`1` in `ℕ`-valued absolute value. -/
theorem natAbs_tau_swapColumns_sub_tau_le_one {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a)) :
    ((hG.swapColumns a (finRotate n a)).tau K - hG.tau K).natAbs ≤ 1 := by
  by_cases hO : G.O a ∈ G.columnArc (finRotate n a)
  · have hmem := hG.tau_swapColumns_mem_Icc_of_mem_columnArc K h hO
    rw [Set.mem_Icc] at hmem
    omega
  · have hmem := hG.tau_swapColumns_mem_Icc_of_notMem_columnArc K h hO
    rw [Set.mem_Icc] at hmem
    omega

/-- Exchanging two cyclically adjacent interleaving columns of a knot grid changes `τ` by at most
`1`. -/
theorem abs_tau_swapColumns_sub_tau_le_one {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a)) :
    |(hG.swapColumns a (finRotate n a)).tau K - hG.tau K| ≤ 1 := by
  rw [← Int.natCast_natAbs]
  exact_mod_cast hG.natAbs_tau_swapColumns_sub_tau_le_one K h

/-- A column cross-commutation between knot grids changes `τ` by at most `1`. -/
theorem natAbs_tau_sub_tau_le_one_of_isColumnCrossCommutation (hG' : G'.IsKnot)
    (h : G.IsColumnCrossCommutation G') :
    (hG.tau K - hG'.tau K).natAbs ≤ 1 := by
  obtain ⟨a, ha, rfl⟩ := (isColumnCrossCommutation_iff G G').mp h
  have hle := hG.natAbs_tau_swapColumns_sub_tau_le_one K ha
  omega

/-- A row cross-commutation between knot grids changes `τ` by at most `1`: diagonal reflection
preserves `τ` and turns a row cross-commutation into a column cross-commutation. -/
theorem natAbs_tau_sub_tau_le_one_of_isRowCrossCommutation (hG' : G'.IsKnot)
    (h : G.IsRowCrossCommutation G') :
    (hG.tau K - hG'.tau K).natAbs ≤ 1 := by
  rw [(hG.unblockedHomologyIsomorphic_transpose K).tau_eq,
    (hG'.unblockedHomologyIsomorphic_transpose K).tau_eq]
  exact ((G.isKnot_transpose).mpr hG).natAbs_tau_sub_tau_le_one_of_isColumnCrossCommutation K
    ((G'.isKnot_transpose).mpr hG') ((isColumnCrossCommutation_transpose G G').mpr h)

/-- Any cross-commutation (row or column) between knot grids changes `τ` by at most `1` in
`ℕ`-valued absolute value. -/
theorem natAbs_tau_sub_tau_le_one_of_isCrossCommutation (hG' : G'.IsKnot)
    (h : G.IsCrossCommutation G') :
    (hG.tau K - hG'.tau K).natAbs ≤ 1 := by
  rcases (isCrossCommutation_iff G G').mp h with h | h
  · exact hG.natAbs_tau_sub_tau_le_one_of_isRowCrossCommutation K hG' h
  · exact hG.natAbs_tau_sub_tau_le_one_of_isColumnCrossCommutation K hG' h

/-- Any cross-commutation between knot grids changes `τ` by at most `1`. -/
theorem abs_tau_sub_tau_le_one_of_isCrossCommutation (hG' : G'.IsKnot)
    (h : G.IsCrossCommutation G') :
    |hG.tau K - hG'.tau K| ≤ 1 := by
  rw [← Int.natCast_natAbs]
  exact_mod_cast hG.natAbs_tau_sub_tau_le_one_of_isCrossCommutation K hG' h

/-- Across any cross-commutation of knot grids, `τ(G') ∈ [τ(G) - 1, τ(G) + 1]`. -/
theorem tau_mem_Icc_of_isCrossCommutation (hG' : G'.IsKnot) (h : G.IsCrossCommutation G') :
    hG'.tau K ∈ Set.Icc (hG.tau K - 1) (hG.tau K + 1) := by
  have hle := hG.natAbs_tau_sub_tau_le_one_of_isCrossCommutation K hG' h
  rw [Set.mem_Icc]
  omega

end IsKnot

end GridDiagram

/-! ### Crossing changes, Gordian distance, and the unknotting bound on grid links -/

namespace GridLink

section CommRing

variable {L L' : GridLink}

/-- A crossing change between two grid knots alters `τ` by at most `1` in `ℕ`-valued absolute
value. -/
theorem IsCrossingChange.natAbs_tau_sub_tau_le_one (h : IsCrossingChange L L')
    (hL : L.IsKnot) (hL' : L'.IsKnot) (K : Type*) [CommRing K] [CharP K 2] :
    (hL.tau K - hL'.tau K).natAbs ≤ 1 := by
  obtain ⟨n, G, G', hcross, rfl, rfl⟩ := (isCrossingChange_iff L L').mp h
  rw [IsKnot.tau_toGridLink, IsKnot.tau_toGridLink]
  exact ((isKnot_toGridLink G).mp hL).natAbs_tau_sub_tau_le_one_of_isCrossCommutation K
    ((isKnot_toGridLink G').mp hL') hcross

/-- A crossing change between two grid knots alters `τ` by at most `1`. -/
theorem IsCrossingChange.abs_tau_sub_tau_le_one (h : IsCrossingChange L L')
    (hL : L.IsKnot) (hL' : L'.IsKnot) (K : Type*) [CommRing K] [CharP K 2] :
    |hL.tau K - hL'.tau K| ≤ 1 := by
  rw [← Int.natCast_natAbs]
  exact_mod_cast h.natAbs_tau_sub_tau_le_one hL hL' K

/-- Across a crossing change between grid knots, `τ(L') ∈ [τ(L) - 1, τ(L) + 1]`. -/
theorem IsCrossingChange.tau_mem_Icc (h : IsCrossingChange L L')
    (hL : L.IsKnot) (hL' : L'.IsKnot) (K : Type*) [CommRing K] [CharP K 2] :
    hL'.tau K ∈ Set.Icc (hL.tau K - 1) (hL.tau K + 1) := by
  have hle := h.natAbs_tau_sub_tau_le_one hL hL' K
  rw [Set.mem_Icc]
  omega

private theorem natAbs_tau_sub_tau_le_walk_length (K : Type*) [CommRing K] [CharP K 2]
    {L L' : GridLink} (w : crossingChangeGraph.Walk L L') (hL : L.IsKnot) (hL' : L'.IsKnot) :
    (hL.tau K - hL'.tau K).natAbs ≤ w.length := by
  induction w with
  | nil => simp
  | @cons u v z hadj p ih =>
    have hcross := (crossingChangeGraph_adj.mp hadj).2
    have hv : v.IsKnot := by rwa [isKnot_def, hcross.componentCount_eq, ← isKnot_def]
    have hstep := hcross.natAbs_tau_sub_tau_le_one hL hv K
    have hrest := ih hv hL'
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- **The Gordian distance bound for `τ`.** For any two grid knots `L` and `L'` and any commutative
ring `K` of characteristic two, `|τ(L) - τ(L')|` is bounded by the extended crossing-change
distance between `L` and `L'`. -/
theorem IsKnot.natAbs_tau_sub_tau_le_crossingChangeGraph_edist
    (hL : L.IsKnot) (hL' : L'.IsKnot) (K : Type*) [CommRing K] [CharP K 2] :
    ((hL.tau K - hL'.tau K).natAbs : ℕ∞) ≤ crossingChangeGraph.edist L L' := by
  rw [SimpleGraph.edist_eq_sInf, le_sInf_iff]
  rintro _ ⟨w, rfl⟩
  exact Nat.cast_le.mpr (natAbs_tau_sub_tau_le_walk_length K w hL hL')

end CommRing

section Field

variable {L : GridLink} (K : Type*) [Field K] [CharP K 2]

/-- **The unknotting bound for `τ`.** Over any field `K` of characteristic two, the absolute value
of `τ` of a grid knot is at most its unknotting number. -/
theorem IsKnot.natAbs_tau_le_unknottingNumber (hL : L.IsKnot) :
    ((hL.tau K).natAbs : ℕ∞) ≤ L.unknottingNumber := by
  have h := hL.natAbs_tau_sub_tau_le_crossingChangeGraph_edist isKnot_unknot K
  rwa [tau_unknot, sub_zero, ← unknottingNumber_def] at h

/-- **Integer form of the unknotting bound `|τ(L)| ≤ u(L)`.** If a grid knot `L` can be unknotted
in at most `u` crossing changes, then `|τ(L)| ≤ u` over any field of characteristic two. -/
theorem IsKnot.abs_tau_le_of_unknottingNumber_le (hL : L.IsKnot) {u : ℕ}
    (hu : L.unknottingNumber ≤ u) :
    |hL.tau K| ≤ u := by
  rw [← Int.natCast_natAbs]
  exact_mod_cast Nat.cast_le.mp ((hL.natAbs_tau_le_unknottingNumber K).trans hu)

/-- If a grid link `L` has finite unknotting number, it is a knot and `|τ(L)| ≤ u(L)`. -/
theorem abs_tau_le_toNat_unknottingNumber (h : L.unknottingNumber ≠ ⊤) :
    |(isKnot_of_unknottingNumber_ne_top h).tau K| ≤ L.unknottingNumber.toNat :=
  (isKnot_of_unknottingNumber_ne_top h).abs_tau_le_of_unknottingNumber_le K
    (ENat.natCast_toNat h).ge

/-- **Diagram-level unknotting bound for `τ`.** On any knot grid diagram `G`, `|τ(G)|` is at most
the unknotting number of the presented grid link `G.toGridLink`. -/
theorem _root_.TauCeti.GridDiagram.IsKnot.natAbs_tau_le_unknottingNumber_toGridLink
    {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) :
    ((hG.tau K).natAbs : ℕ∞) ≤ G.toGridLink.unknottingNumber := by
  simpa only [IsKnot.tau_toGridLink] using
    ((isKnot_toGridLink G).mpr hG).natAbs_tau_le_unknottingNumber K

end Field

end GridLink

end TauCeti
