/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Invariance
public import TauCeti.KnotTheory.Grid.Move.Unknot
public import TauCeti.KnotTheory.Grid.SmallGrid.Unblocked
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import TauCeti.KnotTheory.Grid.TorusLink.Homology

/-!
# The bigraded `GH⁻` piece-`finrank` invariant of grid knots

For a grid link with one component, `GridLink.IsKnot.unblockedHomologyPieceFinrank` is the
ground-ring `finrank` of the Maslov--Alexander bidegree-`g` piece of `GH⁻` on any presenting knot
grid diagram. Independence of the chosen diagram follows from bigraded grid-move invariance
(`GridDiagram.IsKnot.finrank_bigradedUnblockedHomologyGrading_piece_eq_of_movesTo`). The computation
rules `unblockedHomologyPieceFinrank_eq_of_toGridLink_eq` and
`unblockedHomologyPieceFinrank_toGridLink` evaluate it on any chosen diagram.

On `GridLink.unknot`, evaluating on the standard `2 × 2` unknot diagram over any commutative ring
`K` of characteristic two shows that every bidegree outside the monomial cone of the two states
`(0, 0)` and `(-1, -1)` has piece `finrank` zero (`unblockedHomologyPieceFinrank_unknot_eq_zero`)
and that the `(0, 0)` piece has `finrank` `1` (`unblockedHomologyPieceFinrank_unknot_zero`). When
`K` is also Noetherian, the `U`-tower `U^k • λ⁻` gives positive `finrank` in every bidegree
`(-2k, -k)` (`unblockedHomologyPieceFinrank_unknot_neg_two_mul_neg_pos`).

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3, 4.6, Theorem 5.3.1
(Chapter 5), and Chapter 6. The lift to `GridLink.IsKnot` parallels
`TauCeti.KnotTheory.Grid.Move.Tau` (`GridLink.IsKnot.tau`), and the `U`-tower positivity uses
`TauCeti.KnotTheory.Grid.Homology.NonTorsion`
(`GridDiagram.eq_zero_of_monomial_smul_XMarkingClass_eq_zero` and
`GridDiagram.IsKnot.X_pow_smul_XMarkingClass_ne_zero`).
-/

public section

open MvPolynomial

namespace TauCeti

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

namespace GridLink

private theorem isKnot_twoByTwo : GridDiagram.twoByTwo.IsKnot :=
  GridDiagram.unknot_zero ▸ GridDiagram.isKnot_unknot 0

private theorem toGridLink_twoByTwo : GridDiagram.twoByTwo.toGridLink = unknot := by
  rw [← GridDiagram.unknot_zero, GridDiagram.toGridLink_unknot]

private theorem bidegree_twoByTwo_X :
    OddComponentGridDiagram.twoByTwo.bidegree GridDiagram.twoByTwo.X = (0, 0) := by
  rw [GridDiagram.twoByTwo_X, OddComponentGridDiagram.bidegree_twoByTwo_twoByTwoSwap]

private theorem even_card_unblockedRectangles_twoByTwo_X :
    ∀ x : GridState 2,
      Even (GridDiagram.twoByTwo.unblockedRectangles x GridDiagram.twoByTwo.X).card := by
  have heq : GridDiagram.twoByTwo = GridDiagram.torusLink 0 0 :=
    GridDiagram.unknot_zero.symm.trans (GridDiagram.torusLink_zero_right (p := 0)).symm
  rw [heq]
  exact GridDiagram.even_card_unblockedRectangles_torusLink_X (p := 0) (q := 0)

private theorem unblockedHomologyPieceFinrank_unknot_eq_twoByTwo
    (K : Type*) [CommRing K] [CharP K 2] (g : ℤ × ℤ) :
    isKnot_unknot.unblockedHomologyPieceFinrank K g =
      Module.finrank K (OddComponentGridDiagram.twoByTwo.bigradedUnblockedHomologyPiece K g) := by
  rw [isKnot_unknot.unblockedHomologyPieceFinrank_eq_of_toGridLink_eq K
    isKnot_twoByTwo toGridLink_twoByTwo g,
    isKnot_twoByTwo.bigradedUnblockedHomologyGrading_piece_eq_mk K _ g]

section CommRing

variable (K : Type*) [CommRing K] [CharP K 2]

/-- Over any commutative ring of characteristic two, `GH⁻` of the unknot has piece `finrank` zero
outside the bidegree cone `{(2a, a) | a ≤ 0} ∪ {(2a + 1, a) | a < 0}`. -/
theorem unblockedHomologyPieceFinrank_unknot_eq_zero {g : ℤ × ℤ}
    (hg : ¬ ((g.2 ≤ 0 ∧ g.1 = 2 * g.2) ∨ (g.2 < 0 ∧ g.1 = 2 * g.2 + 1))) :
    isKnot_unknot.unblockedHomologyPieceFinrank K g = 0 := by
  have : Nontrivial K := CharP.nontrivial_of_char_ne_one (v := 2) (by decide)
  rw [unblockedHomologyPieceFinrank_unknot_eq_twoByTwo]
  have hbot : OddComponentGridDiagram.twoByTwo.bigradedUnblockedHomologyPiece K g = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨z, hz, rfl⟩ :=
      (OddComponentGridDiagram.twoByTwo.mem_bigradedUnblockedHomologyPiece_iff K).mp hy
    rw [OddComponentGridDiagram.bigradedChainMinusPiece_twoByTwo_eq_bot K hg,
      Submodule.mem_bot] at hz
    have hz0 : z = 0 := Subtype.ext hz
    rw [hz0, map_zero]
  rw [hbot, finrank_bot]

/-- Over any commutative ring of characteristic two, the `(0, 0)` piece of `GH⁻` of the unknot has
`finrank` `1`. -/
@[simp]
theorem unblockedHomologyPieceFinrank_unknot_zero :
    isKnot_unknot.unblockedHomologyPieceFinrank K (0, 0) = 1 := by
  have : Nontrivial K := CharP.nontrivial_of_char_ne_one (v := 2) (by decide)
  rw [unblockedHomologyPieceFinrank_unknot_eq_twoByTwo]
  have hvmem : GridDiagram.twoByTwo.XMarkingClass K ∈
      OddComponentGridDiagram.twoByTwo.bigradedUnblockedHomologyPiece K (0, 0) := by
    have hm :=
      OddComponentGridDiagram.twoByTwo.XMarkingClass_mem_bigradedUnblockedHomologyPiece K
    rwa [bidegree_twoByTwo_X] at hm
  refine Module.finrank_of_bijective_toSpanSingleton
    (x := ⟨GridDiagram.twoByTwo.XMarkingClass K, hvmem⟩)
    ⟨fun r₁ r₂ hr ↦ ?_, fun w ↦ ?_⟩
  · have hval : (r₁ - r₂) • GridDiagram.twoByTwo.XMarkingClass K = 0 := by
      have hcoe := congrArg Subtype.val hr
      simp only [LinearMap.toSpanSingleton_apply, Submodule.coe_smul] at hcoe
      rwa [sub_smul, sub_eq_zero]
    have hmon : (monomial (0 : Fin 2 →₀ ℕ) (r₁ - r₂) : MvPolynomial (Fin 2) K) •
        GridDiagram.twoByTwo.XMarkingClass K = 0 := by
      rwa [monomial_zero', ← algebraMap_eq, algebraMap_smul]
    exact sub_eq_zero.mp
      (GridDiagram.twoByTwo.eq_zero_of_monomial_smul_XMarkingClass_eq_zero K
        even_card_unblockedRectangles_twoByTwo_X hmon)
  · obtain ⟨z, hz, hzw⟩ :=
      (OddComponentGridDiagram.twoByTwo.mem_bigradedUnblockedHomologyPiece_iff K).mp w.2
    have hzc :=
      OddComponentGridDiagram.eq_smul_single_twoByTwoSwap_of_mem_bigradedChainMinusPiece_zero K hz
    let r0 : K := (z.1 GridState.twoByTwoSwap).coeff 0
    refine ⟨r0, Subtype.ext ?_⟩
    simp only [LinearMap.toSpanSingleton_apply, Submodule.coe_smul]
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
theorem unblockedHomologyPieceFinrank_unknot_neg_two_mul_neg_pos (k : ℕ) :
    0 < isKnot_unknot.unblockedHomologyPieceFinrank K (-2 * (k : ℤ), -(k : ℤ)) := by
  rw [unblockedHomologyPieceFinrank_unknot_eq_twoByTwo]
  have h := OddComponentGridDiagram.twoByTwo.finrank_bigradedUnblockedHomologyPiece_pos K
    even_card_unblockedRectangles_twoByTwo_X (Finsupp.single 0 k)
  have hb : OddComponentGridDiagram.twoByTwo.bidegree GridDiagram.twoByTwo.X -
      (2 * ((Finsupp.single (0 : Fin 2) k).degree : ℤ),
        ((Finsupp.single (0 : Fin 2) k).degree : ℤ)) =
      (-2 * (k : ℤ), -(k : ℤ)) := by
    rw [bidegree_twoByTwo_X, Finsupp.degree_single]
    exact Prod.ext (by simp) (by simp)
  rwa [hb] at h

end Noetherian

end GridLink

end TauCeti
