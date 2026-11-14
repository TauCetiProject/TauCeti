/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.SimplyBlocked.Intertwining
public import TauCeti.KnotTheory.Grid.SimplyBlocked.CyclicPermutation

/-!
# Cyclic permutations preserve bigraded simply blocked grid homology

For a knot grid, cyclically permuting the rows or the columns induces specified equivalences on
simply blocked grid homology `G-hat`, characterized on cycle classes. The row equivalence is
linear over the surviving polynomial variables and keeps the blocked column `i`. The column
equivalence moves the blocked `O`-marking to column `finRotate n i` and is semilinear along the
renaming of the surviving variables by `finRotate n`.

Both equivalences preserve and reflect the `(O-Maslov, Alexander)` bigrading. Consequently the
bigraded Poincaré series and the Alexander-graded Euler characteristic of `G-hat` are unchanged by
both cyclic permutations. Together with the commutation and stabilization comparisons, these are
the cyclic-permutation cases of the invariance of bigraded `G-hat` under grid moves.

## Main definitions

* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyRelabelRowsFinRotateEquiv`: the equivalence
  induced by cyclically permuting the rows.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyRelabelColumnsFinRotateEquiv`: the
  equivalence induced by cyclically permuting the columns.

## Main results

* `TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_relabelRows_finRotate`
  and
  `TauCeti.GridDiagram.IsKnot.bigradedSimplyBlockedHomologyPoincareSeries_relabelColumns_finRotate`:
  the bigraded Poincaré series of `G-hat` is invariant under both cyclic permutations.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.1. The
unblocked counterparts are `TauCeti.GridDiagram.unblockedHomologyRelabelRowsFinRotateEquiv` and
`TauCeti.GridDiagram.unblockedHomologyRelabelColumnsFinRotateEquiv`.
-/

public section

noncomputable section

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)

local notation "hGᵣ" => Iff.mpr (GridDiagram.isKnot_relabelRows _ (finRotate n)) hG
local notation "hGc" => Iff.mpr (GridDiagram.isKnot_relabelColumns _ (finRotate n)) hG

-- The odd-component relabelings are not exposed, so the two presentations of the relabeled
-- odd-component diagram are identified through their underlying grid diagrams.
private theorem relabelRows_toOddComponentGridDiagram :
    hG.toOddComponentGridDiagram.relabelRows (finRotate n) = (hGᵣ).toOddComponentGridDiagram :=
  Subtype.ext (OddComponentGridDiagram.val_relabelRows _ _)

private theorem relabelColumns_toOddComponentGridDiagram :
    hG.toOddComponentGridDiagram.relabelColumns (finRotate n) =
      (hGc).toOddComponentGridDiagram :=
  Subtype.ext (OddComponentGridDiagram.val_relabelColumns _ _)

/-- Cyclic row relabeling preserves the bidegrees of specialized chains of a knot grid. -/
private theorem relabelRowsEquiv_mem_bigradedChainHatPiece {R : Type*} [CommSemiring R]
    {i : Fin n} (g : ℤ × ℤ) (c : GridChainHat R n i)
    (hc : c ∈ hG.toOddComponentGridDiagram.bigradedChainHatPiece R i g) :
    GridChain.relabelRowsEquiv (finRotate n) c ∈
      (hGᵣ).toOddComponentGridDiagram.bigradedChainHatPiece R i g := by
  rw [← relabelRows_toOddComponentGridDiagram hG]
  exact (OddComponentGridDiagram.relabelRowsEquiv_mem_bigradedChainHatPiece_iff _).mpr hc

/-- Cyclic column relabeling preserves the bidegrees of specialized chains of a knot grid. -/
private theorem simplyBlockedRelabelColumnsEquiv_mem_bigradedChainHatPiece {R : Type*}
    [CommSemiring R] {i : Fin n} (g : ℤ × ℤ) (c : GridChainHat R n i)
    (hc : c ∈ hG.toOddComponentGridDiagram.bigradedChainHatPiece R i g) :
    GridChain.simplyBlockedRelabelColumnsEquiv R (finRotate n) i c ∈
      (hGc).toOddComponentGridDiagram.bigradedChainHatPiece R (finRotate n i) g := by
  rw [← relabelColumns_toOddComponentGridDiagram hG]
  exact (OddComponentGridDiagram.simplyBlockedRelabelColumnsEquiv_mem_bigradedChainHatPiece_iff
    _).mpr hc

section Ring

variable (R : Type*) [CommRing R] [CharP R 2] (i : Fin n)

/-! ### Cyclic permutation of the rows -/

/-- **Invariance of `G-hat` under cyclic permutation of the rows.** Relabeling the grid states
along `finRotate n` induces an isomorphism of modules over the surviving polynomial variables,
keeping the blocked column. -/
def simplyBlockedHomologyRelabelRowsFinRotateEquiv :
    hG.simplyBlockedHomology R i ≃ₗ[MvPolynomial {c : Fin n // c ≠ i} R]
      (hGᵣ).simplyBlockedHomology R i :=
  hG.simplyBlockedHomologyEquivOfIntertwining R hGᵣ (GridChain.relabelRowsEquiv (finRotate n))
    (G.simplyBlockedDifferential_relabelRows_finRotate_apply R i)

/-- The row equivalence sends the class of a cycle to the class of its relabeling. -/
@[simp]
theorem simplyBlockedHomologyRelabelRowsFinRotateEquiv_oneVariableSpecializationHomologyClass
    (z : hG.simplyBlockedCycles R i) :
    hG.simplyBlockedHomologyRelabelRowsFinRotateEquiv R i
        (G.oneVariableSpecializationHomologyClass R i z) =
      (G.relabelRows (finRotate n)).oneVariableSpecializationHomologyClass R i
        (hG.simplyBlockedCyclesEquivOfIntertwining R hGᵣ
          (GridChain.relabelRowsEquiv (finRotate n))
          (G.simplyBlockedDifferential_relabelRows_finRotate_apply R i) z) :=
  hG.simplyBlockedHomologyEquivOfIntertwining_oneVariableSpecializationHomologyClass R hGᵣ _ _ z

/-- The row equivalence preserves and reflects both homology degrees. -/
@[simp]
theorem simplyBlockedHomologyRelabelRowsFinRotateEquiv_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ} {y : (ModuleCat.restrictScalars (MvPolynomial.C :
      R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj (hG.simplyBlockedHomology R i)} :
    hG.simplyBlockedHomologyRelabelRowsFinRotateEquiv R i y ∈
        (hGᵣ).toOddComponentGridDiagram.bigradedHatHomologyPiece R i g ↔
      y ∈ hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g :=
  hG.simplyBlockedHomologyEquivOfIntertwining_mem_bigradedHatHomologyPiece_iff R hGᵣ _ _
    (fun _ => rfl) (relabelRowsEquiv_mem_bigradedChainHatPiece hG)

/-! ### Cyclic permutation of the columns -/

/-- **Invariance of `G-hat` under cyclic permutation of the columns.** Relabeling the grid states
along `finRotate n` and renaming the surviving variables along the same permutation induces an
equivalence onto the simply blocked homology blocking column `finRotate n i`, semilinear along the
renaming. -/
def simplyBlockedHomologyRelabelColumnsFinRotateEquiv :
    hG.simplyBlockedHomology R i ≃ₛₗ[((simplyBlockedRenameEquiv R (finRotate n) i).toRingEquiv :
      MvPolynomial {c : Fin n // c ≠ i} R →+*
        MvPolynomial {c : Fin n // c ≠ finRotate n i} R)]
      (hGc).simplyBlockedHomology R (finRotate n i) :=
  hG.simplyBlockedHomologyEquivOfIntertwining R hGc
    (GridChain.simplyBlockedRelabelColumnsEquiv R (finRotate n) i)
    (G.simplyBlockedDifferential_relabelColumns_finRotate_apply R i)

/-- The column equivalence sends the class of a cycle to the class of its relabeling with renamed
coefficients. -/
@[simp]
theorem simplyBlockedHomologyRelabelColumnsFinRotateEquiv_oneVariableSpecializationHomologyClass
    (z : hG.simplyBlockedCycles R i) :
    hG.simplyBlockedHomologyRelabelColumnsFinRotateEquiv R i
        (G.oneVariableSpecializationHomologyClass R i z) =
      (G.relabelColumns (finRotate n)).oneVariableSpecializationHomologyClass R (finRotate n i)
        (hG.simplyBlockedCyclesEquivOfIntertwining R hGc
          (GridChain.simplyBlockedRelabelColumnsEquiv R (finRotate n) i)
          (G.simplyBlockedDifferential_relabelColumns_finRotate_apply R i) z) :=
  hG.simplyBlockedHomologyEquivOfIntertwining_oneVariableSpecializationHomologyClass R hGc _ _ z

/-- The column equivalence preserves and reflects both homology degrees. -/
@[simp]
theorem simplyBlockedHomologyRelabelColumnsFinRotateEquiv_mem_bigradedHatHomologyPiece_iff
    {g : ℤ × ℤ} {y : (ModuleCat.restrictScalars (MvPolynomial.C :
      R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj (hG.simplyBlockedHomology R i)} :
    hG.simplyBlockedHomologyRelabelColumnsFinRotateEquiv R i y ∈
        (hGc).toOddComponentGridDiagram.bigradedHatHomologyPiece R (finRotate n i) g ↔
      y ∈ hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g :=
  hG.simplyBlockedHomologyEquivOfIntertwining_mem_bigradedHatHomologyPiece_iff R hGc _ _
    (simplyBlockedRenameEquiv R (finRotate n) i).commutes
    (simplyBlockedRelabelColumnsEquiv_mem_bigradedChainHatPiece hG)

end Ring

/-! ### Poincaré series and Euler characteristic -/

section Field

variable (K : Type*) [Field K] [CharP K 2] (i : Fin n)

/-- The bigraded Poincaré series of `G-hat` is invariant under cyclic permutation of the rows. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_relabelRows_finRotate :
    (hGᵣ).bigradedSimplyBlockedHomologyPoincareSeries K i =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K i :=
  hG.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_intertwining K hGᵣ _
    (G.simplyBlockedDifferential_relabelRows_finRotate_apply K i) (fun _ => rfl)
    (relabelRowsEquiv_mem_bigradedChainHatPiece hG)

/-- The Alexander-graded Euler characteristic of `G-hat` is invariant under cyclic permutation of
the rows. -/
theorem gradedSimplyBlockedHomologyEulerChar_relabelRows_finRotate :
    (hGᵣ).gradedSimplyBlockedHomologyEulerChar K i =
      hG.gradedSimplyBlockedHomologyEulerChar K i := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler, gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_relabelRows_finRotate K i]

/-- The bigraded Poincaré series of `G-hat` is invariant under cyclic permutation of the columns,
moving the blocked marking to column `finRotate n i`. -/
theorem bigradedSimplyBlockedHomologyPoincareSeries_relabelColumns_finRotate :
    (hGc).bigradedSimplyBlockedHomologyPoincareSeries K (finRotate n i) =
      hG.bigradedSimplyBlockedHomologyPoincareSeries K i :=
  hG.bigradedSimplyBlockedHomologyPoincareSeries_eq_of_intertwining K hGc _
    (G.simplyBlockedDifferential_relabelColumns_finRotate_apply K i)
    (simplyBlockedRenameEquiv K (finRotate n) i).commutes
    (simplyBlockedRelabelColumnsEquiv_mem_bigradedChainHatPiece hG)

/-- The Alexander-graded Euler characteristic of `G-hat` is invariant under cyclic permutation of
the columns. -/
theorem gradedSimplyBlockedHomologyEulerChar_relabelColumns_finRotate :
    (hGc).gradedSimplyBlockedHomologyEulerChar K (finRotate n i) =
      hG.gradedSimplyBlockedHomologyEulerChar K i := by
  rw [gradedSimplyBlockedHomologyEulerChar_eq_euler, gradedSimplyBlockedHomologyEulerChar_eq_euler,
    hG.bigradedSimplyBlockedHomologyPoincareSeries_relabelColumns_finRotate K i]

end Field

end TauCeti.GridDiagram.IsKnot
