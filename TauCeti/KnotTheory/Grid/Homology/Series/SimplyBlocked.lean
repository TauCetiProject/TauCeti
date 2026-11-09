/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bigraded.Basic
public import TauCeti.KnotTheory.Grid.Homology.HatBigrading
import TauCeti.KnotTheory.Grid.XHomotopy.SimplyBlocked
import TauCeti.LinearAlgebra.Dimension.DirectSum
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The bigraded series of simply blocked knot-grid homology

Over any field of characteristic two, the simply blocked homology `G-hat` of a knot grid is
finite-dimensional over the coefficient field. Its internal `(O-Maslov, Alexander)` grading
therefore gives a finite `TauCeti.Bigraded.Series`: the coefficient at `(m, a)` is the dimension
of that homogeneous piece. The grading is the one on categorical homology, with its actual
`ModuleCat.restrictScalars` coefficient action.

Applying `TauCeti.Bigraded.euler` gives the Alexander-graded Euler characteristic, with a class
of bidegree `(m, a)` contributing `(-1)^m T^a`. These are the integral Alexander degrees of the
knot-grid grading, without the exponent doubling used for grid state sums. No comparison with
the Alexander polynomial or grid determinant is asserted here.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3--4.6.
-/

public section

noncomputable section

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)

section Noetherian

variable (R : Type*) [CommRing R] [CharP R 2] [IsNoetherianRing R] (i : Fin n)

/-- Only finitely many bidegrees of simply blocked knot-grid homology are nonzero. -/
theorem finite_bigradedHatHomologyPiece_ne_bot :
    {g | hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g ≠ ⊥}.Finite := by
  have := hG.finite_restrictScalars_simplyBlockedHomology R i
  simpa only [OddComponentGridDiagram.bigradedHatHomologyGrading_piece] using
    (hG.toOddComponentGridDiagram.bigradedHatHomologyGrading R i).finite_piece_ne_bot

end Noetherian

variable (R : Type*) [Field R] [CharP R 2] (i : Fin n)

private theorem finite_finrank_bigradedHatHomologyPiece_support :
    (Function.support fun g =>
      Module.finrank R (hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g)).Finite :=
  (hG.finite_bigradedHatHomologyPiece_ne_bot R i).subset fun g hg hbot => by
    rw [Function.mem_support, hbot, finrank_bot] at hg
    exact hg rfl

/-- The finite bigraded Poincaré series of simply blocked knot-grid homology over `R`.
Its bidegrees are `(O-Maslov, Alexander)`. -/
noncomputable def bigradedSimplyBlockedHomologyPoincareSeries : Bigraded.Series :=
  AddMonoidAlgebra.ofCoeff <| Finsupp.ofSupportFinite
    (fun g => Module.finrank R
      (hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g))
    (finite_finrank_bigradedHatHomologyPiece_support hG R i)

/-- Each coefficient is the dimension of the corresponding homogeneous homology piece. -/
@[simp]
theorem coeff_bigradedSimplyBlockedHomologyPoincareSeries (g : ℤ × ℤ) :
    (hG.bigradedSimplyBlockedHomologyPoincareSeries R i).coeff g =
      Module.finrank R (hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g) := by
  rw [bigradedSimplyBlockedHomologyPoincareSeries, AddMonoidAlgebra.coeff_ofCoeff,
    Finsupp.ofSupportFinite_coe]

/-- The total dimension of the series is the dimension of categorical `G-hat` after restriction
to the coefficient field. -/
@[simp]
theorem totalDim_bigradedSimplyBlockedHomologyPoincareSeries :
    Bigraded.totalDim (hG.bigradedSimplyBlockedHomologyPoincareSeries R i) =
      Module.finrank R ((ModuleCat.restrictScalars (MvPolynomial.C :
        R →+* MvPolynomial {c : Fin n // c ≠ i} R)).obj
          (hG.simplyBlockedHomology R i)) := by
  classical
  have := hG.finite_restrictScalars_simplyBlockedHomology R i
  rw [Bigraded.totalDim_apply, ← finsum_finrank_eq_finrank_of_isInternal
    (hG.toOddComponentGridDiagram.isInternal_bigradedHatHomologyPiece R i)
    (hG.finite_bigradedHatHomologyPiece_ne_bot R i)]
  rw [finsum_eq_sum_of_support_subset _ (s :=
    (hG.bigradedSimplyBlockedHomologyPoincareSeries R i).coeff.support) (by
      intro g hg
      apply Finsupp.mem_support_iff.mpr
      simpa only [Function.mem_support,
        coeff_bigradedSimplyBlockedHomologyPoincareSeries] using hg)]
  simp only [Finsupp.sum, coeff_bigradedSimplyBlockedHomologyPoincareSeries]

/-- The Alexander-graded Euler characteristic of simply blocked knot-grid homology.
Bidegree `(m, a)` contributes its dimension times `(-1)^m T^a`. -/
noncomputable def gradedSimplyBlockedHomologyEulerChar : LaurentPolynomial ℤ :=
  Bigraded.euler (hG.bigradedSimplyBlockedHomologyPoincareSeries R i)

/-- The simply blocked Euler characteristic is the standard Euler map of its Poincaré series. -/
theorem gradedSimplyBlockedHomologyEulerChar_eq_euler :
    hG.gradedSimplyBlockedHomologyEulerChar R i =
      Bigraded.euler (hG.bigradedSimplyBlockedHomologyPoincareSeries R i) := by
  rfl

/-- The coefficient of the Euler characteristic is the finite alternating sum of the
homogeneous dimensions at the specified Alexander grading. -/
theorem coeff_gradedSimplyBlockedHomologyEulerChar (a : ℤ) :
    (hG.gradedSimplyBlockedHomologyEulerChar R i).coeff a =
      ∑ g ∈ (hG.bigradedSimplyBlockedHomologyPoincareSeries R i).coeff.support,
        if g.2 = a then (g.1.negOnePow : ℤ) *
          (Module.finrank R
            (hG.toOddComponentGridDiagram.bigradedHatHomologyPiece R i g) : ℤ) else 0 := by
  rw [gradedSimplyBlockedHomologyEulerChar, Bigraded.coeff_euler]
  simp only [Finsupp.sum, coeff_bigradedSimplyBlockedHomologyPoincareSeries]

end TauCeti.GridDiagram.IsKnot
