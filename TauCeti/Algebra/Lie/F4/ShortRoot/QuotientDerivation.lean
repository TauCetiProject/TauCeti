/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationStep

/-!
# The representing matrices of type F4 differentiate the multiplication

Modulo two the twenty-six matrices of `TauCeti.F4ShortRoot.quotientMatrix` differentiate the
invariant symmetric multiplication of the twenty-six-dimensional module of type `F₄`. They
represent the twenty-four long root vectors and the first two Cartan generators of the represented
Chevalley algebra, so this is the statement that those elements act by derivations.

Four of the twenty-six are numbered simple root generators outright. The other twenty-two are
reached from those four by commutators with a generator and by divided adjoints of a generator,
alternating between the two because a long root is the sum of a long root and a simple long root,
or of a short root and twice a simple short root; the latter contributes a structure constant two,
and it is the divided power that removes it.

## Main results

* `TauCeti.F4ShortRoot.isDerivation_map_quotientMatrix`: **each of the twenty-six representing
  matrices differentiates the multiplication modulo two.**

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Yale (1967), §§2 and 11.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R] [CharP R 2]

omit [CharP R 2] in
/-- The representing matrix of index 10 is a numbered simple root generator, so it
differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_ten :
    IsDerivation ((quotientMatrix 10).map (Int.cast : ℤ → R)) := by
  have hEq : quotientMatrix 10 = rootMatrix (Sum.inl 0) := by
    ext a b
    rw [quotientMatrix_apply, (isStep_rootMatrix (Sum.inl 0)).apply]
    revert a b
    decide +kernel
  rw [hEq]
  exact (isDerivation_rootMatrix (Sum.inl 0)).map

omit [CharP R 2] in
/-- The representing matrix of index 11 is a numbered simple root generator, so it
differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_eleven :
    IsDerivation ((quotientMatrix 11).map (Int.cast : ℤ → R)) := by
  have hEq : quotientMatrix 11 = rootMatrix (Sum.inl 1) := by
    ext a b
    rw [quotientMatrix_apply, (isStep_rootMatrix (Sum.inl 1)).apply]
    revert a b
    decide +kernel
  rw [hEq]
  exact (isDerivation_rootMatrix (Sum.inl 1)).map

omit [CharP R 2] in
/-- The representing matrix of index 14 is a numbered simple root generator, so it
differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_fourteen :
    IsDerivation ((quotientMatrix 14).map (Int.cast : ℤ → R)) := by
  have hEq : quotientMatrix 14 = rootMatrix (Sum.inr 1) := by
    ext a b
    rw [quotientMatrix_apply, (isStep_rootMatrix (Sum.inr 1)).apply]
    revert a b
    decide +kernel
  rw [hEq]
  exact (isDerivation_rootMatrix (Sum.inr 1)).map

omit [CharP R 2] in
/-- The representing matrix of index 15 is a numbered simple root generator, so it
differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_fifteen :
    IsDerivation ((quotientMatrix 15).map (Int.cast : ℤ → R)) := by
  have hEq : quotientMatrix 15 = rootMatrix (Sum.inr 0) := by
    ext a b
    rw [quotientMatrix_apply, (isStep_rootMatrix (Sum.inr 0)).apply]
    revert a b
    decide +kernel
  rw [hEq]
  exact (isDerivation_rootMatrix (Sum.inr 0)).map

/-- The representing matrix of index 8 is the commutator of a numbered simple root generator
with the representing matrix of index 10, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_eight :
    IsDerivation ((quotientMatrix 8).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := quotientMatrix 10) (M' := quotientMatrix 8)
    (Sum.inl 1) isDerivation_quotientMatrix_ten
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 10),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 1))]
        simp only [quotientMatrix_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 9 is the divided adjoint of a numbered simple root generator
with the representing matrix of index 11, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_nine :
    IsDerivation ((quotientMatrix 9).map (Int.cast : ℤ → R)) :=
  isDerivation_of_conjugation_congr (R := R) (M := quotientMatrix 11) (M' := quotientMatrix 9)
    (Sum.inl 2) isDerivation_quotientMatrix_eleven
      (by
        intro a b
        simp only [Matrix.add_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 11),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 2)),
          Matrix.IsStep.mul_apply (isStep_rootDividedSquareMatrix (Sum.inl 2))]
        simp only [quotientMatrix_apply, rootMatrix_inl, raisingMatrix_apply,
          rootDividedSquareMatrix_inl, raisingDividedSquareMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 12 is the commutator of a numbered simple root generator
with the representing matrix of index 11, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_twelve :
    IsDerivation ((quotientMatrix 12).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := quotientMatrix 11) (M' := quotientMatrix 12)
    (Sum.inr 1) isDerivation_quotientMatrix_eleven
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 11),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 1))]
        simp only [quotientMatrix_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 13 is the commutator of a numbered simple root generator
with the representing matrix of index 10, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_thirteen :
    IsDerivation ((quotientMatrix 13).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := quotientMatrix 10) (M' := quotientMatrix 13)
    (Sum.inr 0) isDerivation_quotientMatrix_ten
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 10),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 0))]
        simp only [quotientMatrix_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 16 is the divided adjoint of a numbered simple root generator
with the representing matrix of index 14, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_sixteen :
    IsDerivation ((quotientMatrix 16).map (Int.cast : ℤ → R)) :=
  isDerivation_of_conjugation_congr (R := R) (M := quotientMatrix 14) (M' := quotientMatrix 16)
    (Sum.inr 2) isDerivation_quotientMatrix_fourteen
      (by
        intro a b
        simp only [Matrix.add_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 14),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 2)),
          Matrix.IsStep.mul_apply (isStep_rootDividedSquareMatrix (Sum.inr 2))]
        simp only [quotientMatrix_apply, rootMatrix_inr, loweringMatrix_apply,
          rootDividedSquareMatrix_inr, loweringDividedSquareMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 17 is the commutator of a numbered simple root generator
with the representing matrix of index 15, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_seventeen :
    IsDerivation ((quotientMatrix 17).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := quotientMatrix 15) (M' := quotientMatrix 17)
    (Sum.inr 1) isDerivation_quotientMatrix_fifteen
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 15),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 1))]
        simp only [quotientMatrix_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 18 is the divided adjoint of a numbered simple root generator
with the representing matrix of index 16, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_eighteen :
    IsDerivation ((quotientMatrix 18).map (Int.cast : ℤ → R)) :=
  isDerivation_of_conjugation_congr (R := R) (M := quotientMatrix 16) (M' := quotientMatrix 18)
    (Sum.inr 3) isDerivation_quotientMatrix_sixteen
      (by
        intro a b
        simp only [Matrix.add_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 16),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 3)),
          Matrix.IsStep.mul_apply (isStep_rootDividedSquareMatrix (Sum.inr 3))]
        simp only [quotientMatrix_apply, rootMatrix_inr, loweringMatrix_apply,
          rootDividedSquareMatrix_inr, loweringDividedSquareMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 19 is the divided adjoint of a numbered simple root generator
with the representing matrix of index 17, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_nineteen :
    IsDerivation ((quotientMatrix 19).map (Int.cast : ℤ → R)) :=
  isDerivation_of_conjugation_congr (R := R) (M := quotientMatrix 17) (M' := quotientMatrix 19)
    (Sum.inr 2) isDerivation_quotientMatrix_seventeen
      (by
        intro a b
        simp only [Matrix.add_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 17),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 2)),
          Matrix.IsStep.mul_apply (isStep_rootDividedSquareMatrix (Sum.inr 2))]
        simp only [quotientMatrix_apply, rootMatrix_inr, loweringMatrix_apply,
          rootDividedSquareMatrix_inr, loweringDividedSquareMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 20 is the divided adjoint of a numbered simple root generator
with the representing matrix of index 19, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_twenty :
    IsDerivation ((quotientMatrix 20).map (Int.cast : ℤ → R)) :=
  isDerivation_of_conjugation_congr (R := R) (M := quotientMatrix 19) (M' := quotientMatrix 20)
    (Sum.inr 3) isDerivation_quotientMatrix_nineteen
      (by
        intro a b
        simp only [Matrix.add_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 19),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 3)),
          Matrix.IsStep.mul_apply (isStep_rootDividedSquareMatrix (Sum.inr 3))]
        simp only [quotientMatrix_apply, rootMatrix_inr, loweringMatrix_apply,
          rootDividedSquareMatrix_inr, loweringDividedSquareMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 21 is the commutator of a numbered simple root generator
with the representing matrix of index 19, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_twentyOne :
    IsDerivation ((quotientMatrix 21).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := quotientMatrix 19) (M' := quotientMatrix 21)
    (Sum.inr 1) isDerivation_quotientMatrix_nineteen
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 19),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 1))]
        simp only [quotientMatrix_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 22 is the divided adjoint of a numbered simple root generator
with the representing matrix of index 21, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_twentyTwo :
    IsDerivation ((quotientMatrix 22).map (Int.cast : ℤ → R)) :=
  isDerivation_of_conjugation_congr (R := R) (M := quotientMatrix 21) (M' := quotientMatrix 22)
    (Sum.inr 3) isDerivation_quotientMatrix_twentyOne
      (by
        intro a b
        simp only [Matrix.add_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 21),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 3)),
          Matrix.IsStep.mul_apply (isStep_rootDividedSquareMatrix (Sum.inr 3))]
        simp only [quotientMatrix_apply, rootMatrix_inr, loweringMatrix_apply,
          rootDividedSquareMatrix_inr, loweringDividedSquareMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 23 is the divided adjoint of a numbered simple root generator
with the representing matrix of index 22, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_twentyThree :
    IsDerivation ((quotientMatrix 23).map (Int.cast : ℤ → R)) :=
  isDerivation_of_conjugation_congr (R := R) (M := quotientMatrix 22) (M' := quotientMatrix 23)
    (Sum.inr 2) isDerivation_quotientMatrix_twentyTwo
      (by
        intro a b
        simp only [Matrix.add_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 22),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 2)),
          Matrix.IsStep.mul_apply (isStep_rootDividedSquareMatrix (Sum.inr 2))]
        simp only [quotientMatrix_apply, rootMatrix_inr, loweringMatrix_apply,
          rootDividedSquareMatrix_inr, loweringDividedSquareMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 24 is the commutator of a numbered simple root generator
with the representing matrix of index 23, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_twentyFour :
    IsDerivation ((quotientMatrix 24).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := quotientMatrix 23) (M' := quotientMatrix 24)
    (Sum.inr 1) isDerivation_quotientMatrix_twentyThree
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 23),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 1))]
        simp only [quotientMatrix_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 25 is the commutator of a numbered simple root generator
with the representing matrix of index 24, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_twentyFive :
    IsDerivation ((quotientMatrix 25).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := quotientMatrix 24) (M' := quotientMatrix 25)
    (Sum.inr 0) isDerivation_quotientMatrix_twentyFour
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 24),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 0))]
        simp only [quotientMatrix_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 6 is the divided adjoint of a numbered simple root generator
with the representing matrix of index 8, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_six :
    IsDerivation ((quotientMatrix 6).map (Int.cast : ℤ → R)) :=
  isDerivation_of_conjugation_congr (R := R) (M := quotientMatrix 8) (M' := quotientMatrix 6)
    (Sum.inl 2) isDerivation_quotientMatrix_eight
      (by
        intro a b
        simp only [Matrix.add_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 8),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 2)),
          Matrix.IsStep.mul_apply (isStep_rootDividedSquareMatrix (Sum.inl 2))]
        simp only [quotientMatrix_apply, rootMatrix_inl, raisingMatrix_apply,
          rootDividedSquareMatrix_inl, raisingDividedSquareMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 7 is the divided adjoint of a numbered simple root generator
with the representing matrix of index 9, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_seven :
    IsDerivation ((quotientMatrix 7).map (Int.cast : ℤ → R)) :=
  isDerivation_of_conjugation_congr (R := R) (M := quotientMatrix 9) (M' := quotientMatrix 7)
    (Sum.inl 3) isDerivation_quotientMatrix_nine
      (by
        intro a b
        simp only [Matrix.add_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 9),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 3)),
          Matrix.IsStep.mul_apply (isStep_rootDividedSquareMatrix (Sum.inl 3))]
        simp only [quotientMatrix_apply, rootMatrix_inl, raisingMatrix_apply,
          rootDividedSquareMatrix_inl, raisingDividedSquareMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 4 is the commutator of a numbered simple root generator
with the representing matrix of index 6, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_four :
    IsDerivation ((quotientMatrix 4).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := quotientMatrix 6) (M' := quotientMatrix 4)
    (Sum.inl 1) isDerivation_quotientMatrix_six
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 6),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 1))]
        simp only [quotientMatrix_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 5 is the divided adjoint of a numbered simple root generator
with the representing matrix of index 6, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_five :
    IsDerivation ((quotientMatrix 5).map (Int.cast : ℤ → R)) :=
  isDerivation_of_conjugation_congr (R := R) (M := quotientMatrix 6) (M' := quotientMatrix 5)
    (Sum.inl 3) isDerivation_quotientMatrix_six
      (by
        intro a b
        simp only [Matrix.add_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 6),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 3)),
          Matrix.IsStep.mul_apply (isStep_rootDividedSquareMatrix (Sum.inl 3))]
        simp only [quotientMatrix_apply, rootMatrix_inl, raisingMatrix_apply,
          rootDividedSquareMatrix_inl, raisingDividedSquareMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 3 is the divided adjoint of a numbered simple root generator
with the representing matrix of index 4, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_three :
    IsDerivation ((quotientMatrix 3).map (Int.cast : ℤ → R)) :=
  isDerivation_of_conjugation_congr (R := R) (M := quotientMatrix 4) (M' := quotientMatrix 3)
    (Sum.inl 3) isDerivation_quotientMatrix_four
      (by
        intro a b
        simp only [Matrix.add_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 4),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 3)),
          Matrix.IsStep.mul_apply (isStep_rootDividedSquareMatrix (Sum.inl 3))]
        simp only [quotientMatrix_apply, rootMatrix_inl, raisingMatrix_apply,
          rootDividedSquareMatrix_inl, raisingDividedSquareMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 2 is the divided adjoint of a numbered simple root generator
with the representing matrix of index 3, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_two :
    IsDerivation ((quotientMatrix 2).map (Int.cast : ℤ → R)) :=
  isDerivation_of_conjugation_congr (R := R) (M := quotientMatrix 3) (M' := quotientMatrix 2)
    (Sum.inl 2) isDerivation_quotientMatrix_three
      (by
        intro a b
        simp only [Matrix.add_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 3),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 2)),
          Matrix.IsStep.mul_apply (isStep_rootDividedSquareMatrix (Sum.inl 2))]
        simp only [quotientMatrix_apply, rootMatrix_inl, raisingMatrix_apply,
          rootDividedSquareMatrix_inl, raisingDividedSquareMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 1 is the commutator of a numbered simple root generator
with the representing matrix of index 2, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_one :
    IsDerivation ((quotientMatrix 1).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := quotientMatrix 2) (M' := quotientMatrix 1)
    (Sum.inl 1) isDerivation_quotientMatrix_two
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 2),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 1))]
        simp only [quotientMatrix_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- The representing matrix of index 0 is the commutator of a numbered simple root generator
with the representing matrix of index 1, so it differentiates the multiplication. -/
private theorem isDerivation_quotientMatrix_zero :
    IsDerivation ((quotientMatrix 0).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := quotientMatrix 1) (M' := quotientMatrix 0)
    (Sum.inl 0) isDerivation_quotientMatrix_one
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsStep.mul_apply (isStep_quotientMatrix 1),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 0))]
        simp only [quotientMatrix_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- **Each of the twenty-six representing matrices differentiates the invariant multiplication
modulo two.** -/
theorem isDerivation_map_quotientMatrix (q : Fin 26) :
    IsDerivation ((quotientMatrix q).map (Int.cast : ℤ → R)) := by
  fin_cases q
  · exact isDerivation_quotientMatrix_zero
  · exact isDerivation_quotientMatrix_one
  · exact isDerivation_quotientMatrix_two
  · exact isDerivation_quotientMatrix_three
  · exact isDerivation_quotientMatrix_four
  · exact isDerivation_quotientMatrix_five
  · exact isDerivation_quotientMatrix_six
  · exact isDerivation_quotientMatrix_seven
  · exact isDerivation_quotientMatrix_eight
  · exact isDerivation_quotientMatrix_nine
  · exact isDerivation_quotientMatrix_ten
  · exact isDerivation_quotientMatrix_eleven
  · exact isDerivation_quotientMatrix_twelve
  · exact isDerivation_quotientMatrix_thirteen
  · exact isDerivation_quotientMatrix_fourteen
  · exact isDerivation_quotientMatrix_fifteen
  · exact isDerivation_quotientMatrix_sixteen
  · exact isDerivation_quotientMatrix_seventeen
  · exact isDerivation_quotientMatrix_eighteen
  · exact isDerivation_quotientMatrix_nineteen
  · exact isDerivation_quotientMatrix_twenty
  · exact isDerivation_quotientMatrix_twentyOne
  · exact isDerivation_quotientMatrix_twentyTwo
  · exact isDerivation_quotientMatrix_twentyThree
  · exact isDerivation_quotientMatrix_twentyFour
  · exact isDerivation_quotientMatrix_twentyFive

end TauCeti.F4ShortRoot
