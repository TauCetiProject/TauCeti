/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Intertwining
public import TauCeti.KnotTheory.Grid.SimplyBlocked.HalfTurn

/-!
# The half-turn on simply blocked grid homology

For a knot grid, rotating the torus by a half-turn (`GridDiagram.rotate`) induces a semilinear
equivalence on `G-hat` (`GridDiagram.IsKnot.simplyBlockedHomologyRotateEquiv`), moving the blocked
column from `i` to `i.rev` and renaming surviving variables along `Fin.revPerm`. It preserves and
reflects the `(O-Maslov, Alexander)` bigrading
(`simplyBlockedHomologyRotateEquiv_mem_bigradedHatHomologyPiece_iff`), restricts to linear
equivalences on homogeneous pieces (`simplyBlockedHomologyRotatePieceEquiv`), and preserves the
bigraded Poincaré series (`bigradedSimplyBlockedHomologyPoincareSeries_rotate`) and Euler
characteristic (`gradedSimplyBlockedHomologyEulerChar_rotate`).

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3, 4.6, and 5.2.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)

local notation "hGᵣ" => Iff.mpr (GridDiagram.isKnot_rotate G) hG
local notation "Base(" R ", " n ", " i ")" =>
  ModuleCat.restrictScalars (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)

private theorem simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece {R : Type*}
    [CommSemiring R] {i : Fin n} (g : ℤ × ℤ) (c : GridChainHat R n i)
    (hc : c ∈ hG.toOddComponentGridDiagram.bigradedChainHatPiece R i g) :
    GridChain.simplyBlockedHalfTurnEquiv R i c ∈
      (hGᵣ).toOddComponentGridDiagram.bigradedChainHatPiece R (Fin.revPerm i) g := by
  rw [← hG.rotate_toOddComponentGridDiagram]
  exact (OddComponentGridDiagram.simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece_iff _).mpr hc

section Ring

variable (R : Type*) [CommRing R] [CharP R 2] (i : Fin n)

/-- **The half-turn on `G-hat`.** Moving grid states by `GridState.halfTurn` and renaming the
surviving variables along `Fin.revPerm` induces an equivalence onto the simply blocked homology of
`G.rotate` blocking column `i.rev`. -/
def simplyBlockedHomologyRotateEquiv :
    hG.simplyBlockedHomology R i ≃ₛₗ[
      ((simplyBlockedRenameEquiv R (Fin.revPerm (n := n)) i).toRingEquiv :
        MvPolynomial {c : Fin n // c ≠ i} R →+*
          MvPolynomial {c : Fin n // c ≠ Fin.revPerm i} R)]
      (hGᵣ).simplyBlockedHomology R (Fin.revPerm i) :=
  hG.simplyBlockedHomologyEquivOfIntertwining R hGᵣ (GridChain.simplyBlockedHalfTurnEquiv R i)
    (G.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv R i)

/-- The half-turn sends the class of a cycle to the class of its half-turned cycle. -/
@[simp]
theorem simplyBlockedHomologyRotateEquiv_oneVariableSpecializationHomologyClass
    (z : hG.simplyBlockedCycles R i) :
    hG.simplyBlockedHomologyRotateEquiv R i (G.oneVariableSpecializationHomologyClass R i z) =
      G.rotate.oneVariableSpecializationHomologyClass R (Fin.revPerm i)
        (hG.simplyBlockedCyclesEquivOfIntertwining R hGᵣ (GridChain.simplyBlockedHalfTurnEquiv R i)
          (G.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv R i) z) :=
  hG.simplyBlockedHomologyEquivOfIntertwining_oneVariableSpecializationHomologyClass R hGᵣ _ _ z

/-- The half-turn preserves and reflects both homology degrees of `G-hat`. -/
@[simp]
theorem simplyBlockedHomologyRotateEquiv_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ} {y : (Base(R, n, i)).obj (hG.simplyBlockedHomology R i)} :
    hG.simplyBlockedHomologyRotateEquiv R i y ∈
        (hGᵣ).toOddComponentGridDiagram.bigradedHatHomologyPiece R (Fin.revPerm i) g ↔
      y ∈ hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g :=
  hG.simplyBlockedHomologyEquivOfIntertwining_mem_bigradedHatHomologyPiece_iff R hGᵣ _ _
    (simplyBlockedRenameEquiv R (Fin.revPerm (n := n)) i).commutes
    (simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece hG)

/-- The half-turn restricted to a homogeneous bidegree piece of `G-hat`. -/
def simplyBlockedHomologyRotatePieceEquiv (g : ℤ × ℤ) :
    hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g ≃ₗ[R]
      (hGᵣ).toOddComponentGridDiagram.bigradedHatHomologyPiece R (Fin.revPerm i) g :=
  hG.simplyBlockedHomologyPieceEquivOfIntertwining R hGᵣ _
    (G.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv R i)
    (simplyBlockedRenameEquiv R (Fin.revPerm (n := n)) i).commutes
    (simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece hG) g

/-- On underlying classes, the homogeneous-piece half-turn is `simplyBlockedHomologyRotateEquiv`. -/
@[simp]
theorem coe_simplyBlockedHomologyRotatePieceEquiv (g : ℤ × ℤ)
    (y : hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g) :
    (hG.simplyBlockedHomologyRotatePieceEquiv R i g y :
      (Base(R, n, Fin.revPerm i)).obj ((hGᵣ).simplyBlockedHomology R (Fin.revPerm i))) =
      hG.simplyBlockedHomologyRotateEquiv R i
        (y : (Base(R, n, i)).obj (hG.simplyBlockedHomology R i)) :=
  hG.coe_simplyBlockedHomologyPieceEquivOfIntertwining R hGᵣ _
    (G.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv R i)
    (simplyBlockedRenameEquiv R (Fin.revPerm (n := n)) i).commutes
    (simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece hG) g y

end Ring

section Field

variable (K : Type*) [Field K] [CharP K 2] (i : Fin n)

/-- The bigraded Poincaré series of `G-hat` is invariant under the half-turn, transporting the
blocked column from `i` to `i.rev`. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_rotate :
    (hGᵣ).bigradedSimplyBlockedHomologyPoincareSeries K (Fin.revPerm i) =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K i :=
  hG.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_intertwining K hGᵣ _
    (G.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv K i)
    (simplyBlockedRenameEquiv K (Fin.revPerm (n := n)) i).commutes
    (simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece hG)

/-- The Alexander-graded Euler characteristic of `G-hat` is invariant under the half-turn. -/
theorem gradedSimplyBlockedHomologyEulerChar_rotate :
    (hGᵣ).gradedSimplyBlockedHomologyEulerChar K (Fin.revPerm i) =
      hG.gradedSimplyBlockedHomologyEulerChar K i :=
  hG.gradedSimplyBlockedHomologyEulerChar_eq_of_intertwining K hGᵣ _
    (G.simplyBlockedDifferential_rotate_simplyBlockedHalfTurnEquiv K i)
    (simplyBlockedRenameEquiv K (Fin.revPerm (n := n)) i).commutes
    (simplyBlockedHalfTurnEquiv_mem_bigradedChainHatPiece hG)

end Field

end TauCeti.GridDiagram.IsKnot
