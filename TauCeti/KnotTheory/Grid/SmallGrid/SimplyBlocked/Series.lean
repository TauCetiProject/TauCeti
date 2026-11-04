/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Series.SimplyBlocked
public import TauCeti.KnotTheory.Grid.SmallGrid.SimplyBlocked.Bigrading

/-!
# The simply blocked series of the two-by-two unknot

The standard two-by-two toroidal grid has simply blocked homology equal to the coefficient
field in bidegree `(O-Maslov, Alexander) = (0, 0)`. This file computes its Poincaré series and
Alexander-graded Euler characteristic as `1` over any field of characteristic two.

The equivalence `GridDiagram.twoByTwoSimplyBlockedHomologyEquiv` identifies homology with
the coefficient field. It sends the class of the cycle `GridDiagram.twoByTwoSimplyBlockedCycle`
to `1`, and the surviving variable acts by zero. The homogeneous piece at `(0, 0)` is
one-dimensional, and all other pieces vanish.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3--4.6.
-/

public section

noncomputable section

namespace TauCeti.GridDiagram

variable (R : Type*) [Field R] [CharP R 2]

local notation "Poly" => MvPolynomial {c : Fin 2 // c ≠ 0} R
private noncomputable def twoByTwoHomologyCoefficientEquiv :
    (ModuleCat.restrictScalars (MvPolynomial.C : R →+* Poly)).obj
      (twoByTwo.isKnot_of_two.simplyBlockedHomology R 0) ≃ₗ[R] R := by
  letI : Module R (twoByTwo.isKnot_of_two.simplyBlockedHomology R 0) :=
    Module.compHom _ (MvPolynomial.C : R →+* Poly)
  letI : Module Poly R := Module.compHom R (MvPolynomial.constantCoeff : Poly →+* R)
  letI : IsScalarTower R Poly R := IsScalarTower.of_algebraMap_smul fun r x => by
    -- The polynomial action on the target is constant-coefficient multiplication; restriction
    -- along C must agree with the caller's ordinary coefficient-field action.
    change MvPolynomial.constantCoeff (MvPolynomial.C r : Poly) * x = r * x
    rw [MvPolynomial.constantCoeff_C]
  letI : IsScalarTower R Poly (twoByTwo.isKnot_of_two.simplyBlockedHomology R 0) :=
    IsScalarTower.of_compHom R Poly _
  exact (twoByTwoSimplyBlockedHomologyEquiv R).restrictScalars R

/-- The simply blocked Poincaré series of the standard two-by-two unknot is one copy of the
coefficient field in bidegree `(0, 0)`. -/
@[simp]
theorem bigradedSimplyBlockedHomologyPoincareSeries_twoByTwo :
    twoByTwo.isKnot_of_two.bigradedSimplyBlockedHomologyPoincareSeries R 0 = 1 := by
  ext g
  rw [IsKnot.coeff_bigradedSimplyBlockedHomologyPoincareSeries]
  by_cases hg : g = (0, 0)
  · subst g
    rw [twoByTwo_bigradedHatHomologyPiece_zero_eq_top R, finrank_top,
      (twoByTwoHomologyCoefficientEquiv R).finrank_eq]
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single]
    -- The monoid-algebra unit uses the product's zero index; expose that index as the
    -- explicit bidegree so the existing single-coefficient equation applies.
    change Module.finrank R R = Finsupp.single (0, 0) 1 (0, 0)
    simp
  · rw [twoByTwo_bigradedHatHomologyPiece_eq_bot R hg, finrank_bot]
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single]
    exact (Finsupp.single_eq_of_ne hg).symm

/-- The Alexander-graded Euler characteristic of simply blocked homology of the standard
two-by-two unknot is the constant Laurent polynomial one. -/
@[simp]
theorem gradedSimplyBlockedHomologyEulerChar_twoByTwo :
    twoByTwo.isKnot_of_two.gradedSimplyBlockedHomologyEulerChar R 0 = 1 := by
  rw [IsKnot.gradedSimplyBlockedHomologyEulerChar_eq_euler,
    bigradedSimplyBlockedHomologyPoincareSeries_twoByTwo, map_one]

end TauCeti.GridDiagram
