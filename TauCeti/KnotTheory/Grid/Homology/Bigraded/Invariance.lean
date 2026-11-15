/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Commutation
public import TauCeti.KnotTheory.Grid.Homology.Bigraded.CyclicPermutation
public import TauCeti.KnotTheory.Grid.Homology.Invariance
public import TauCeti.KnotTheory.Grid.Move.Unknot
public import TauCeti.KnotTheory.Grid.SmallGrid.Gradings
public import TauCeti.KnotTheory.Grid.Stabilization.Bigraded
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Grading
public import TauCeti.KnotTheory.Grid.TorusLink.Homology
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Maslov--Alexander bigraded invariance of `GH⁻` under grid moves

For a knot grid over a commutative ring `K` of characteristic two, every elementary grid move
preserves the unblocked grid homology `GH⁻` as a Maslov--Alexander bigraded `K[U]`-module, in the
sense of `GridDiagram.IsKnot.BigradedUnblockedHomologyIsomorphic`:
- cyclic row and column permutations (`bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate`,
  `bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate`);
- row and column commutations (`bigradedUnblockedHomologyIsomorphic_of_isCommutation`, in
  `Homology/Bigraded/Commutation.lean`);
- south-west and north-east corner `X`-stabilizations
  (`bigradedUnblockedHomologyIsomorphic_stabilizeX`,
  `bigradedUnblockedHomologyIsomorphic_stabilizeX_succ`), and hence all eight elementary
  stabilization types (`bigradedUnblockedHomologyIsomorphic_of_isStabilization`) and
  destabilizations.

Passing to the equivalence closure shows that knot grid diagrams connected by arbitrary grid moves
have isomorphic Maslov--Alexander bigraded `K[U]`-modules `GH⁻`
(`GridDiagram.IsKnot.bigradedUnblockedHomologyIsomorphic_of_movesTo`). In particular, for any grid
knot `L`, the ground-ring `finrank` of each homogeneous piece
(`GridLink.IsKnot.unblockedHomologyPieceFinrank`) is independent of the presenting knot grid
diagram.

On `GridLink.unknot`, evaluating on the `2 × 2` unknot diagram over any commutative ring `K` of
characteristic two shows that every bidegree outside the monomial cone of the two states `(0, 0)`
and `(-1, -1)` has piece `finrank` zero (`unblockedHomologyPieceFinrank_unknot_eq_zero`) and that
the `(0, 0)` piece has `finrank` `1` (`unblockedHomologyPieceFinrank_unknot_zero`). When `K` is
also Noetherian, the `U`-tower `U^k • λ⁻` gives positive `finrank` in every bidegree `(-2k, -k)`
(`unblockedHomologyPieceFinrank_unknot_pos`).

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Theorem 5.3.1 (Chapter 5).
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram.IsKnot

variable {n m : ℕ} {G : GridDiagram n} {G' : GridDiagram m}
  (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

open OddComponentGridDiagram in
/-- **Cyclic permutation of the rows preserves bigraded `GH⁻`** of a knot grid over `K[U]`. -/
theorem bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate :
    hG.BigradedUnblockedHomologyIsomorphic ((G.isKnot_relabelRows (finRotate n)).mpr hG) K := by
  refine .of_semilinearMap (σ := RingHom.id _) (fun _ ↦ rfl)
    (G.unblockedHomologyRelabelRowsFinRotateEquiv K).toLinearMap
    (G.unblockedHomologyRelabelRowsFinRotateEquiv K).bijective fun g y hy ↦ ?_
  rw [bigradedUnblockedHomologyGrading_piece] at hy ⊢
  exact (unblockedHomologyRelabelRowsFinRotateEquiv_mem_bigradedPiece_iff _ K).mpr hy

open OddComponentGridDiagram in
/-- **Cyclic permutation of the columns preserves bigraded `GH⁻`** of a knot grid over `K[U]`. -/
theorem bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate :
    hG.BigradedUnblockedHomologyIsomorphic ((G.isKnot_relabelColumns (finRotate n)).mpr hG) K := by
  refine .of_semilinearMap (fun p ↦ ?_)
    (G.unblockedHomologyRelabelColumnsFinRotateEquiv K).toLinearMap
    (G.unblockedHomologyRelabelColumnsFinRotateEquiv K).bijective fun g y hy ↦ ?_
  · simp [aeval_rename, Function.comp_def]
  · rw [bigradedUnblockedHomologyGrading_piece] at hy ⊢
    exact (unblockedHomologyRelabelColumnsFinRotateEquiv_mem_bigradedPiece_iff _ K).mpr hy

/-- **South-west corner `X`-stabilization preserves bigraded `GH⁻`** of a knot grid over `K[U]`. -/
theorem bigradedUnblockedHomologyIsomorphic_stabilizeX (s : Fin n) :
    hG.BigradedUnblockedHomologyIsomorphic
      ((G.isKnot_stabilizeX s.castSucc (G.X s).castSucc s).mpr hG) K := by
  refine (BigradedUnblockedHomologyIsomorphic.of_semilinearMap
    (fun p ↦ by rw [AlgHom.coe_toRingHom, aeval_rename, Function.comp_def])
    (G.stabilizeXHomologyMap s K) (G.stabilizeXHomologyMap_bijective s K) fun g y hy ↦ ?_).symm
  rw [bigradedUnblockedHomologyGrading_piece] at hy ⊢
  exact hG.toOddComponentGridDiagram.stabilizeXHomologyMap_mem_bigradedUnblockedHomologyPiece s K hy

/-- **North-east corner `X`-stabilization preserves bigraded `GH⁻`** of a knot grid over `K[U]`. -/
theorem bigradedUnblockedHomologyIsomorphic_stabilizeX_succ (s : Fin n) :
    hG.BigradedUnblockedHomologyIsomorphic
      ((G.isKnot_stabilizeX s.succ (G.X s).succ s).mpr hG) K := by
  refine (BigradedUnblockedHomologyIsomorphic.of_semilinearMap
    (fun p ↦ by rw [AlgHom.coe_toRingHom, aeval_rename, Function.comp_def])
    (G.stabilizeXSuccHomologyMap s K) (G.stabilizeXSuccHomologyMap_bijective s K)
    fun g y hy ↦ ?_).symm
  rw [bigradedUnblockedHomologyGrading_piece] at hy ⊢
  exact hG.toOddComponentGridDiagram.stabilizeXSuccHomologyMap_mem_bigradedUnblockedHomologyPiece
    s K hy

/-- Cyclic permutations and commutations preserve bigraded `GH⁻` along every size-preserving
sequence. -/
theorem bigradedUnblockedHomologyIsomorphic_of_commutationMovesTo {H : GridDiagram n}
    (hH : H.IsKnot) (h : G.CommutationMovesTo H) :
    hG.BigradedUnblockedHomologyIsomorphic hH K :=
  h.induction_on
    (motive := fun A B ↦ ∀ (hA : A.IsKnot) (hB : B.IsKnot),
      hA.BigradedUnblockedHomologyIsomorphic hB K)
    (fun _ hA _ ↦ hA.bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate K)
    (fun _ hA _ ↦ hA.bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate K)
    (fun h hA hB ↦ hA.bigradedUnblockedHomologyIsomorphic_of_isCommutation K hB h)
    (fun _ hA _ ↦ .refl hA K)
    (fun _ ih hA hB ↦ (ih hB hA).symm)
    (fun h _ ih ih' hA hB ↦
      (ih hA (h.movesTo.isKnot_iff.mpr hA)).trans
        (ih' (h.movesTo.isKnot_iff.mpr hA) hB)) hG hH

/-- Every elementary stabilization, of either marking and in any corner, preserves bigraded
`GH⁻`. -/
theorem bigradedUnblockedHomologyIsomorphic_of_isStabilization {H : GridDiagram (n + 1)}
    (hH : H.IsKnot) (h : G.IsStabilization H) :
    hG.BigradedUnblockedHomologyIsomorphic hH K := by
  obtain ⟨s, hs | hs⟩ := h.exists_commutationMovesTo
  · exact (hG.bigradedUnblockedHomologyIsomorphic_stabilizeX K s).trans
      (bigradedUnblockedHomologyIsomorphic_of_commutationMovesTo _ K hH hs.symm)
  · exact (hG.bigradedUnblockedHomologyIsomorphic_stabilizeX_succ K s).trans
      (bigradedUnblockedHomologyIsomorphic_of_commutationMovesTo _ K hH hs.symm)

/-- Each elementary grid move, including a destabilization, preserves `GH⁻` as a Maslov--Alexander
bigraded `K[U]`-module. -/
theorem bigradedUnblockedHomologyIsomorphic_of_isMove (hG' : G'.IsKnot)
    (h : IsMove ⟨n, G⟩ ⟨m, G'⟩) :
    hG.BigradedUnblockedHomologyIsomorphic hG' K := by
  cases h with
  | cyclicRows h =>
    rcases h with rfl | rfl
    · exact hG.bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate K
    · exact (hG'.bigradedUnblockedHomologyIsomorphic_relabelRows_finRotate K).symm
  | cyclicColumns h =>
    rcases h with rfl | rfl
    · exact hG.bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate K
    · exact (hG'.bigradedUnblockedHomologyIsomorphic_relabelColumns_finRotate K).symm
  | commutation h => exact hG.bigradedUnblockedHomologyIsomorphic_of_isCommutation K hG' h
  | stabilization h => exact hG.bigradedUnblockedHomologyIsomorphic_of_isStabilization K hG' h
  | destabilization h =>
    exact (hG'.bigradedUnblockedHomologyIsomorphic_of_isStabilization K hG
      ((isDestabilization_iff_isStabilization _ _).mp h)).symm

/-- **Maslov--Alexander bigraded invariance of `GH⁻` under grid moves.** Knot grid diagrams
connected by arbitrary grid moves have isomorphic unblocked grid homologies as Maslov--Alexander
bigraded `K[U]`-modules. -/
theorem bigradedUnblockedHomologyIsomorphic_of_movesTo (hG' : G'.IsKnot) (h : G.MovesTo G') :
    hG.BigradedUnblockedHomologyIsomorphic hG' K :=
  h.induction_on
    (motive := fun A B ↦ ∀ (hA : A.2.IsKnot) (hB : B.2.IsKnot),
      hA.BigradedUnblockedHomologyIsomorphic hB K)
    (fun h hA hB ↦ hA.bigradedUnblockedHomologyIsomorphic_of_isMove K hB h)
    (fun _ hA _ ↦ .refl hA K)
    (fun _ ih hA hB ↦ (ih hB hA).symm)
    (fun h _ ih ih' hA hB ↦
      (ih hA (h.isKnot_iff.mpr hA)).trans (ih' (h.isKnot_iff.mpr hA) hB)) hG hG'

/-- Knot grid diagrams connected by arbitrary grid moves have equal ground-ring `finrank` in every
Maslov--Alexander bidegree of `GH⁻`. -/
theorem finrank_bigradedUnblockedHomologyGrading_piece_eq_of_movesTo (hG' : G'.IsKnot)
    (h : G.MovesTo G') (g : ℤ × ℤ) :
    Module.finrank K ((hG.bigradedUnblockedHomologyGrading K).piece g) =
      Module.finrank K ((hG'.bigradedUnblockedHomologyGrading K).piece g) :=
  (hG.bigradedUnblockedHomologyIsomorphic_of_movesTo K hG' h).finrank_piece_eq g

end GridDiagram.IsKnot

/-! ### Grid-knot piece `finrank` invariant -/

namespace GridLink.IsKnot

variable {L : GridLink} (hL : L.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- The ground-ring `finrank` of the Maslov--Alexander bidegree-`g` piece of `GH⁻` for a grid knot,
evaluated on a presenting knot diagram.

It is independent of the representative diagram by
`GridDiagram.IsKnot.finrank_bigradedUnblockedHomologyGrading_piece_eq_of_movesTo`. -/
noncomputable def unblockedHomologyPieceFinrank (g : ℤ × ℤ) : ℕ :=
  let G := Classical.choose L.exists_gridDiagram
  let hG := (isKnot_toGridLink G.2).mp ((Classical.choose_spec L.exists_gridDiagram).symm ▸ hL)
  Module.finrank K ((hG.bigradedUnblockedHomologyGrading K).piece g)

/-- Evaluate `unblockedHomologyPieceFinrank` on any knot grid diagram presenting the grid knot. -/
theorem unblockedHomologyPieceFinrank_eq_of_toGridLink_eq {n : ℕ} {G : GridDiagram n}
    (hG : G.IsKnot) (h : G.toGridLink = L) (g : ℤ × ℤ) :
    hL.unblockedHomologyPieceFinrank K g =
      Module.finrank K ((hG.bigradedUnblockedHomologyGrading K).piece g) := by
  unfold unblockedHomologyPieceFinrank
  apply GridDiagram.IsKnot.finrank_bigradedUnblockedHomologyGrading_piece_eq_of_movesTo
  exact ((Classical.choose L.exists_gridDiagram).2.toGridLink_eq_iff_movesTo).mp
    ((Classical.choose_spec L.exists_gridDiagram).trans h.symm)

/-- On the grid knot presented by a diagram, `unblockedHomologyPieceFinrank` is the `finrank` of
that diagram's homogeneous piece. -/
@[simp]
theorem unblockedHomologyPieceFinrank_toGridLink {n : ℕ} {G : GridDiagram n}
    (hG : G.toGridLink.IsKnot) (g : ℤ × ℤ) :
    hG.unblockedHomologyPieceFinrank K g =
      Module.finrank K
        ((((isKnot_toGridLink G).mp hG).bigradedUnblockedHomologyGrading K).piece g) :=
  unblockedHomologyPieceFinrank_eq_of_toGridLink_eq hG K ((isKnot_toGridLink G).mp hG) rfl g

end GridLink.IsKnot

/-! ### Concrete evaluation on `GridLink.unknot` -/

namespace OddComponentGridDiagram

section TwoByTwo

variable (R : Type*) [CommSemiring R]

/-- On the `2 × 2` unknot diagram, every bidegree outside the monomial cone of the two states
`(0, 0)` and `(-1, -1)` has trivial chain piece. -/
theorem bigradedChainMinusPiece_twoByTwo_eq_bot {g : ℤ × ℤ}
    (hg : ¬ ((g.2 ≤ 0 ∧ g.1 = 2 * g.2) ∨ (g.2 < 0 ∧ g.1 = 2 * g.2 + 1))) :
    twoByTwo.bigradedChainMinusPiece R g = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro c hc
  by_contra hc0
  obtain ⟨x, hx⟩ := Finsupp.ne_iff.mp hc0
  obtain ⟨e, he⟩ := (support_nonempty (p := c x)).mpr (by simpa using hx)
  have hdeg := (twoByTwo.mem_bigradedChainMinusPiece.mp hc) x e he
  rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | rfl
  · have hfst := (twoByTwo.monomialBidegree_fst GridState.twoByTwoId e).symm.trans
      (congrArg Prod.fst hdeg)
    rw [GridDiagram.maslovOℤ_twoByTwo_twoByTwoId] at hfst
    have hsnd := (twoByTwo.monomialBidegree_snd GridState.twoByTwoId e).symm.trans
      (congrArg Prod.snd hdeg)
    have hb2 := congrArg Prod.snd bidegree_twoByTwo_twoByTwoId
    rw [bidegree_snd] at hb2
    exact hg (Or.inr ⟨by omega, by omega⟩)
  · have hfst := (twoByTwo.monomialBidegree_fst GridState.twoByTwoSwap e).symm.trans
      (congrArg Prod.fst hdeg)
    rw [GridDiagram.maslovOℤ_twoByTwo_twoByTwoSwap] at hfst
    have hsnd := (twoByTwo.monomialBidegree_snd GridState.twoByTwoSwap e).symm.trans
      (congrArg Prod.snd hdeg)
    have hb2 := congrArg Prod.snd bidegree_twoByTwo_twoByTwoSwap
    rw [bidegree_snd] at hb2
    exact hg (Or.inl ⟨by omega, by omega⟩)

/-- Every chain in bidegree `(0, 0)` on the `2 × 2` unknot diagram is a scalar multiple of the
`X`-marking state generator `twoByTwoSwap`. -/
theorem eq_smul_single_twoByTwoSwap_of_mem_bigradedChainMinusPiece_zero
    {c : GridChainMinus R 2} (hc : c ∈ twoByTwo.bigradedChainMinusPiece R (0, 0)) :
    c = ((c GridState.twoByTwoSwap).coeff 0) • Finsupp.single GridState.twoByTwoSwap 1 := by
  ext x : 1
  rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | rfl
  · rw [Finsupp.smul_single, Finsupp.single_eq_of_ne GridState.twoByTwoId_ne_twoByTwoSwap]
    by_contra hx
    obtain ⟨e, he⟩ := (support_nonempty (p := c GridState.twoByTwoId)).mpr hx
    have hdeg := (twoByTwo.mem_bigradedChainMinusPiece.mp hc) GridState.twoByTwoId e he
    have hsnd := (twoByTwo.monomialBidegree_snd GridState.twoByTwoId e).symm.trans
      (congrArg Prod.snd hdeg)
    have hb2 := congrArg Prod.snd bidegree_twoByTwo_twoByTwoId
    rw [bidegree_snd] at hb2
    omega
  · simp only [Finsupp.smul_single, Finsupp.single_eq_same, Algebra.smul_def, mul_one]
    ext e
    rcases eq_or_ne e 0 with rfl | he0
    · simp [algebraMap_eq, coeff_C]
    · rw [algebraMap_eq, coeff_C, ite_eq_right_iff.mpr fun h ↦ absurd h.symm he0]
      by_contra hne
      have hdeg := (twoByTwo.mem_bigradedChainMinusPiece.mp hc) GridState.twoByTwoSwap e
        (mem_support_iff.mpr hne)
      have hsnd := (twoByTwo.monomialBidegree_snd GridState.twoByTwoSwap e).symm.trans
        (congrArg Prod.snd hdeg)
      have hb2 := congrArg Prod.snd bidegree_twoByTwo_twoByTwoSwap
      rw [bidegree_snd] at hb2
      have hed : e.degree = 0 := by omega
      exact he0 ((Finsupp.degree_eq_zero_iff e).mp hed)

end TwoByTwo

end OddComponentGridDiagram

namespace GridLink

section CommRing

variable (K : Type*) [CommRing K] [CharP K 2]

/-- Over any commutative ring of characteristic two, `GH⁻` of the unknot has piece `finrank` zero
outside the bidegree cone `{(2a, a) | a ≤ 0} ∪ {(2a + 1, a) | a < 0}`. -/
theorem unblockedHomologyPieceFinrank_unknot_eq_zero {g : ℤ × ℤ}
    (hg : ¬ ((g.2 ≤ 0 ∧ g.1 = 2 * g.2) ∨ (g.2 < 0 ∧ g.1 = 2 * g.2 + 1))) :
    isKnot_unknot.unblockedHomologyPieceFinrank K g = 0 := by
  have : Nontrivial K := CharP.nontrivial_of_char_ne_one (v := 2) (by decide)
  have h2 : GridDiagram.twoByTwo.IsKnot := GridDiagram.unknot_zero ▸ GridDiagram.isKnot_unknot 0
  have hlink : GridDiagram.twoByTwo.toGridLink = unknot := by
    rw [← GridDiagram.unknot_zero, GridDiagram.toGridLink_unknot]
  rw [isKnot_unknot.unblockedHomologyPieceFinrank_eq_of_toGridLink_eq K h2 hlink g,
    h2.bigradedUnblockedHomologyGrading_piece]
  have hbot : h2.toOddComponentGridDiagram.bigradedUnblockedHomologyPiece K g = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (OddComponentGridDiagram.twoByTwo.mem_bigradedUnblockedHomologyPiece_iff
      K).mp hy
    rw [OddComponentGridDiagram.bigradedChainMinusPiece_twoByTwo_eq_bot K hg,
      Submodule.mem_bot] at hz
    have hz0 : z = 0 := Subtype.ext hz
    rw [hz0, map_zero]
  rw [hbot, finrank_bot]

private theorem eq_zero_of_smul_X_pow_smul_XMarkingClass_eq_zero {n : ℕ} {G : GridDiagram n}
    (hG : G.IsKnot) (hX : ∀ x : GridState n, Even (G.unblockedRectangles x G.X).card) (k : ℕ)
    {r : K} (hr : letI := hG.unblockedHomologyModule K
      r • ((Polynomial.X ^ k : Polynomial K) • G.XMarkingClass K) = 0) :
    r = 0 := by
  let _ := hG.unblockedHomologyModule K
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩
  have hU := hG.aeval_smul_unblockedHomology (R := K) (MvPolynomial.X i ^ k) (G.XMarkingClass K)
  rw [map_pow, aeval_X] at hU
  rw [hU, ← algebraMap_smul (MvPolynomial (Fin n) K) r, smul_smul, G.XMarkingClass_def,
    ← map_smul, G.unblockedHomologyClass_eq_zero_iff, Submodule.coe_smul,
    G.coe_XMarkingCycle] at hr
  have hev := G.eval_one_eq_zero_of_smul_single_mem_range K hX hr
  simpa [algebraMap_eq] using hev

/-- Over any commutative ring of characteristic two, the `(0, 0)` piece of `GH⁻` of the unknot has
`finrank` `1`. -/
@[simp]
theorem unblockedHomologyPieceFinrank_unknot_zero :
    isKnot_unknot.unblockedHomologyPieceFinrank K (0, 0) = 1 := by
  have : Nontrivial K := CharP.nontrivial_of_char_ne_one (v := 2) (by decide)
  have h2 : GridDiagram.twoByTwo.IsKnot := GridDiagram.unknot_zero ▸ GridDiagram.isKnot_unknot 0
  have hlink : GridDiagram.twoByTwo.toGridLink = unknot := by
    rw [← GridDiagram.unknot_zero, GridDiagram.toGridLink_unknot]
  rw [isKnot_unknot.unblockedHomologyPieceFinrank_eq_of_toGridLink_eq K h2 hlink (0, 0),
    h2.bigradedUnblockedHomologyGrading_piece]
  have hvmem : GridDiagram.twoByTwo.XMarkingClass K ∈
      OddComponentGridDiagram.twoByTwo.bigradedUnblockedHomologyPiece K (0, 0) := by
    have hm := h2.XMarkingClass_mem_bigradedUnblockedHomologyGrading_piece K
    rw [h2.bigradedUnblockedHomologyGrading_piece] at hm
    change GridDiagram.twoByTwo.XMarkingClass K ∈
      OddComponentGridDiagram.twoByTwo.bigradedUnblockedHomologyPiece K
        (OddComponentGridDiagram.twoByTwo.bidegree GridDiagram.twoByTwo.X) at hm
    rwa [GridDiagram.twoByTwo_X, OddComponentGridDiagram.bidegree_twoByTwo_twoByTwoSwap] at hm
  refine Module.finrank_of_bijective_toSpanSingleton (x := ⟨GridDiagram.twoByTwo.XMarkingClass K,
      hvmem⟩) ⟨fun r₁ r₂ hr ↦ ?_, fun w ↦ ?_⟩
  · have heven : ∀ x : GridState 2,
        Even (GridDiagram.twoByTwo.unblockedRectangles x GridDiagram.twoByTwo.X).card := by
      have heq : GridDiagram.twoByTwo = GridDiagram.torusLink 0 0 :=
        GridDiagram.unknot_zero.symm.trans (GridDiagram.torusLink_zero_right (p := 0)).symm
      rw [heq]
      exact GridDiagram.even_card_unblockedRectangles_torusLink_X (p := 0) (q := 0)
    let _ := h2.unblockedHomologyModule K
    have hr' : (r₁ - r₂) • ((Polynomial.X ^ 0 : Polynomial K) •
        GridDiagram.twoByTwo.XMarkingClass K) = 0 := by
      rw [pow_zero, one_smul, sub_smul, sub_eq_zero]
      exact congrArg Subtype.val hr
    exact sub_eq_zero.mp (eq_zero_of_smul_X_pow_smul_XMarkingClass_eq_zero K h2 heven 0 hr')
  · obtain ⟨z, hz, hzw⟩ :=
      (OddComponentGridDiagram.twoByTwo.mem_bigradedUnblockedHomologyPiece_iff K).mp w.2
    have hzc :=
      OddComponentGridDiagram.eq_smul_single_twoByTwoSwap_of_mem_bigradedChainMinusPiece_zero K hz
    let r0 : K := (z.1 GridState.twoByTwoSwap).coeff 0
    refine ⟨r0, Subtype.ext ?_⟩
    change r0 • GridDiagram.twoByTwo.XMarkingClass K = w.1
    have hzX : z = (algebraMap K (MvPolynomial (Fin 2) K) r0) •
        GridDiagram.twoByTwo.XMarkingCycle K := by
      apply Subtype.ext
      rw [Submodule.coe_smul, algebraMap_smul, GridDiagram.coe_XMarkingCycle,
        GridDiagram.twoByTwo_X]
      exact hzc
    rw [← hzw, hzX, GridDiagram.XMarkingClass_def, map_smul, algebraMap_smul]

end CommRing

section Noetherian

variable (K : Type*) [CommRing K] [CharP K 2] [IsNoetherianRing K]

/-- Over a Noetherian commutative ring of characteristic two, `GH⁻` of the unknot has positive
`finrank` in every bidegree `(-2k, -k)` along the `U`-tower (`k : ℕ`). -/
theorem unblockedHomologyPieceFinrank_unknot_pos (k : ℕ) :
    0 < isKnot_unknot.unblockedHomologyPieceFinrank K (-2 * (k : ℤ), -(k : ℤ)) := by
  have : Nontrivial K := CharP.nontrivial_of_char_ne_one (v := 2) (by decide)
  have hT : (GridDiagram.torusLink 0 0).IsKnot := by
    rw [GridDiagram.torusLink_zero_right]
    exact GridDiagram.isKnot_unknot 0
  have hX0 : hT.toOddComponentGridDiagram.bidegree (GridDiagram.torusLink 0 0).X = (0, 0) := by
    have heq : GridDiagram.torusLink 0 0 = GridDiagram.twoByTwo :=
      (GridDiagram.torusLink_zero_right (p := 0)).trans GridDiagram.unknot_zero
    revert hT
    rw [heq]
    intro _
    change OddComponentGridDiagram.twoByTwo.bidegree GridDiagram.twoByTwo.X = (0, 0)
    rw [GridDiagram.twoByTwo_X, OddComponentGridDiagram.bidegree_twoByTwo_twoByTwoSwap]
  have hlink : (GridDiagram.torusLink 0 0).toGridLink = unknot := by
    rw [GridDiagram.torusLink_zero_right, GridDiagram.toGridLink_unknot]
  rw [isKnot_unknot.unblockedHomologyPieceFinrank_eq_of_toGridLink_eq K hT hlink]
  let _ := hT.unblockedHomologyModule K
  have : Module.Finite K ((hT.bigradedUnblockedHomologyGrading K).piece
      (-2 * (k : ℤ), -(k : ℤ))) := by
    rw [hT.bigradedUnblockedHomologyGrading_piece]
    exact hT.toOddComponentGridDiagram.finite_bigradedUnblockedHomologyPiece K _
  have hmem := hT.X_pow_smul_mem_bigradedUnblockedHomologyGrading_piece K k
    (hT.XMarkingClass_mem_bigradedUnblockedHomologyGrading_piece K)
  have hsub : (0, 0) - (2 * (k : ℤ), (k : ℤ)) = (-2 * (k : ℤ), -(k : ℤ)) := by
    apply Prod.ext <;> simp
  rw [hX0, hsub] at hmem
  have hinj : Function.Injective (LinearMap.toSpanSingleton K
      ((hT.bigradedUnblockedHomologyGrading K).piece (-2 * (k : ℤ), -(k : ℤ)))
      ⟨(Polynomial.X ^ k : Polynomial K) • (GridDiagram.torusLink 0 0).XMarkingClass K, hmem⟩) := by
    intro r₁ r₂ hr
    have hr' : (r₁ - r₂) • ((Polynomial.X ^ k : Polynomial K) •
        (GridDiagram.torusLink 0 0).XMarkingClass K) = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact congrArg Subtype.val hr
    exact sub_eq_zero.mp (eq_zero_of_smul_X_pow_smul_XMarkingClass_eq_zero K hT
      GridDiagram.even_card_unblockedRectangles_torusLink_X k hr')
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_self] at hle
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one hle

end Noetherian

end GridLink

end TauCeti
