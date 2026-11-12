/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.HalfTurn
public import TauCeti.KnotTheory.Grid.Stabilization.NorthEast.Grading
public import TauCeti.KnotTheory.Grid.Stabilization.SimplyBlocked.Bigraded

/-!
# North-east stabilization of simply blocked knot-grid homology

The north-east corner `X`-stabilization inserts a column after the split column `s` and a row
after its `X`-marking. The old `O`-marking of column `i` then lies in column
`s.succ.succAbove i`. Blocking that marking gives simply blocked homology in the same absolute
`(O-Maslov, Alexander)` bidegrees as the original knot grid.

This file specifies a coefficient-linear equivalence on every homogeneous piece. A half-turn
identifies the north-east stabilized source with the south-west stabilization of the rotated
grid, including the transported blocked marking. Thus the equivalence retains the grading
normalization and the choice of blocked marking. Over a field of characteristic two, its
bigraded Poincaré series and Alexander-graded Euler characteristic are unchanged.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2.
-/

public section

namespace TauCeti.GridDiagram.IsKnot

open OddComponentGridDiagram

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (s i : Fin n)
  (R : Type*) [CommRing R] [CharP R 2]

local notation "j" => Fin.succAbove (Fin.succ s) i
local notation "hG'" => Iff.mpr
  (GridDiagram.isKnot_stabilizeX G (Fin.succ s) (Fin.succ (GridDiagram.X G s)) s) hG
local notation "hRot" => Iff.mpr (GridDiagram.isKnot_rotate G) hG

/-- North-east `X`-stabilization identifies each homogeneous piece of simply blocked knot-grid
homology with the piece of the same absolute `O`-Maslov and Alexander bidegree. The blocked
marking is the transported old `O`-marking of column `i`. -/
noncomputable def simplyBlockedHomologyStabilizeXSuccPieceEquiv (g : ℤ × ℤ) :
    (hG').toOddComponentGridDiagram.bigradedHatHomologyPiece R j g ≃ₗ[R]
      hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g :=
  (((hG').simplyBlockedHomologyRotatePieceEquiv R j g).trans
    (LinearEquiv.cast (M := fun p : OddComponentGridDiagram (n + 1) × Fin (n + 1) =>
      p.1.bigradedHatHomologyPiece R p.2 g)
      (i := ((Iff.mpr (GridDiagram.isKnot_rotate _) (hG')).toOddComponentGridDiagram, (j).rev))
      («j» := ((hRot).toOddComponentGridDiagram.stabilizeX s.rev,
        s.rev.castSucc.succAbove i.rev)) (by
        apply Prod.ext
        · exact Subtype.ext (G.rotate_stabilizeX_succ s)
        · simp only [Fin.rev_succAbove, Fin.rev_succ]))).trans
    (((hRot).toOddComponentGridDiagram.oneVariableSpecializationStabilizeXHomologyPieceEquiv
      s.rev i.rev R g).trans (hG.simplyBlockedHomologyRotatePieceEquiv R i g).symm)

/-- The north-east comparison is the conjugate of the south-west comparison by half-turns.
The intervening cast identifies the rotated stabilized diagram and its blocked marking. -/
theorem simplyBlockedHomologyStabilizeXSuccPieceEquiv_def (g : ℤ × ℤ) :
    hG.simplyBlockedHomologyStabilizeXSuccPieceEquiv s i R g =
      (((hG').simplyBlockedHomologyRotatePieceEquiv R j g).trans
        (LinearEquiv.cast (M := fun p : OddComponentGridDiagram (n + 1) × Fin (n + 1) =>
          p.1.bigradedHatHomologyPiece R p.2 g)
          (i := ((Iff.mpr (GridDiagram.isKnot_rotate _) (hG')).toOddComponentGridDiagram,
            (j).rev))
          («j» := ((hRot).toOddComponentGridDiagram.stabilizeX s.rev,
            s.rev.castSucc.succAbove i.rev)) (by
            apply Prod.ext
            · exact Subtype.ext (G.rotate_stabilizeX_succ s)
            · simp only [Fin.rev_succAbove, Fin.rev_succ]))).trans
        (((hRot).toOddComponentGridDiagram.oneVariableSpecializationStabilizeXHomologyPieceEquiv
          s.rev i.rev R g).trans (hG.simplyBlockedHomologyRotatePieceEquiv R i g).symm) :=
  (rfl)

/-- North-east `X`-stabilization preserves the coefficient-ring rank in every bidegree of
simply blocked knot-grid homology. -/
theorem finrank_bigradedHatHomologyPiece_stabilizeXSucc (g : ℤ × ℤ) :
    Module.finrank R ((hG').toOddComponentGridDiagram.bigradedHatHomologyPiece R j g) =
      Module.finrank R (hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g) :=
  (hG.simplyBlockedHomologyStabilizeXSuccPieceEquiv s i R g).finrank_eq

section Field

variable (K : Type*) [Field K] [CharP K 2]

/-- North-east corner `X`-stabilization preserves the bigraded Poincaré series of simply
blocked knot-grid homology, blocking the transported old `O`-marking. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_stabilizeXSucc :
    (hG').bigradedSimplyBlockedHomologyPoincareSeries K j =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K i := by
  ext g
  rw [coeff_bigradedSimplyBlockedHomologyPoincareSeries,
    coeff_bigradedSimplyBlockedHomologyPoincareSeries]
  exact hG.finrank_bigradedHatHomologyPiece_stabilizeXSucc s i K g

/-- North-east corner `X`-stabilization preserves the Alexander-graded Euler characteristic of
simply blocked knot-grid homology, blocking the transported old `O`-marking. -/
theorem gradedSimplyBlockedHomologyEulerChar_stabilizeXSucc :
    (hG').gradedSimplyBlockedHomologyEulerChar K j =
      hG.gradedSimplyBlockedHomologyEulerChar K i := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler,
    gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_stabilizeXSucc s i K]

end Field

end TauCeti.GridDiagram.IsKnot
