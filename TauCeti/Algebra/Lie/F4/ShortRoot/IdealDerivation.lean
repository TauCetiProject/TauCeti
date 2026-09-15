/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationStep

/-!
# The multiplication operators of type F4 differentiate the multiplication

Modulo two each of the twenty-six multiplication operators of
`TauCeti.F4ShortRoot.multiplicationOperator` differentiates the invariant symmetric multiplication
of the twenty-six-dimensional module of type `F₄`. They span the short-root ideal of the
represented Chevalley algebra modulo two, so this is the statement that the ideal acts by
derivations; equivalently the multiplication satisfies the identity
`m (m (u, v), w) + m (v, m (u, w)) = m (u, m (v, w))` modulo two.

Four of the twenty-six are congruent modulo two to a numbered simple short root generator, and the
derivation equation of a generator says exactly that its commutator with a multiplication operator
is again a multiplication operator, that of the transformed index; iterating produces the whole
family from those four.

The twenty-six quotient coordinates annihilate every multiplication operator, which is the
statement that the ideal lies in the kernel of the quotient.

## Main results

* `TauCeti.F4ShortRoot.isDerivation_map_multiplicationOperator`: **each multiplication operator
  differentiates the multiplication modulo two.**
* `TauCeti.F4ShortRoot.quotientCoordinate_multiplicationOperator`: the short-root quotient
  coordinates annihilate the multiplication operators.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Yale (1967), §11.
* N. Jacobson, *Exceptional Lie Algebras*, Lecture Notes in Pure and Applied Mathematics **1**,
  Marcel Dekker (1971), §I.4.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R] [CharP R 2]

/-- The multiplication operator of index 10 is congruent modulo two to a numbered simple short
root generator, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_ten :
    IsDerivation ((multiplicationOperator 10).map (Int.cast : ℤ → R)) := by
  have hEq : (multiplicationOperator 10).map (Int.cast : ℤ → R) =
      (rootMatrix (Sum.inl 3)).map (Int.cast : ℤ → R) := by
    refine map_intCast_eq_of_modEq fun a b => ?_
    rw [multiplicationOperator_apply, (isStep_rootMatrix (Sum.inl 3)).apply]
    revert a b
    decide +kernel
  rw [hEq]
  exact (isDerivation_rootMatrix (Sum.inl 3)).map

/-- The multiplication operator of index 11 is congruent modulo two to a numbered simple short
root generator, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_eleven :
    IsDerivation ((multiplicationOperator 11).map (Int.cast : ℤ → R)) := by
  have hEq : (multiplicationOperator 11).map (Int.cast : ℤ → R) =
      (rootMatrix (Sum.inl 2)).map (Int.cast : ℤ → R) := by
    refine map_intCast_eq_of_modEq fun a b => ?_
    rw [multiplicationOperator_apply, (isStep_rootMatrix (Sum.inl 2)).apply]
    revert a b
    decide +kernel
  rw [hEq]
  exact (isDerivation_rootMatrix (Sum.inl 2)).map

/-- The multiplication operator of index 14 is congruent modulo two to a numbered simple short
root generator, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_fourteen :
    IsDerivation ((multiplicationOperator 14).map (Int.cast : ℤ → R)) := by
  have hEq : (multiplicationOperator 14).map (Int.cast : ℤ → R) =
      (rootMatrix (Sum.inr 2)).map (Int.cast : ℤ → R) := by
    refine map_intCast_eq_of_modEq fun a b => ?_
    rw [multiplicationOperator_apply, (isStep_rootMatrix (Sum.inr 2)).apply]
    revert a b
    decide +kernel
  rw [hEq]
  exact (isDerivation_rootMatrix (Sum.inr 2)).map

/-- The multiplication operator of index 15 is congruent modulo two to a numbered simple short
root generator, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_fifteen :
    IsDerivation ((multiplicationOperator 15).map (Int.cast : ℤ → R)) := by
  have hEq : (multiplicationOperator 15).map (Int.cast : ℤ → R) =
      (rootMatrix (Sum.inr 3)).map (Int.cast : ℤ → R) := by
    refine map_intCast_eq_of_modEq fun a b => ?_
    rw [multiplicationOperator_apply, (isStep_rootMatrix (Sum.inr 3)).apply]
    revert a b
    decide +kernel
  rw [hEq]
  exact (isDerivation_rootMatrix (Sum.inr 3)).map

/-- The multiplication operator of index 8 is the commutator of a numbered simple root generator
with the multiplication operator of index 10, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_eight :
    IsDerivation ((multiplicationOperator 8).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 10)
    (M' := multiplicationOperator 8) (Sum.inl 2) isDerivation_multiplicationOperator_ten
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 10),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 2))]
        simp only [multiplicationOperator_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 9 is the commutator of a numbered simple root generator
with the multiplication operator of index 11, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_nine :
    IsDerivation ((multiplicationOperator 9).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 11)
    (M' := multiplicationOperator 9) (Sum.inl 1) isDerivation_multiplicationOperator_eleven
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 11),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 1))]
        simp only [multiplicationOperator_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 12 is the commutator of a numbered simple root generator
with the multiplication operator of index 11, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_twelve :
    IsDerivation ((multiplicationOperator 12).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 11)
    (M' := multiplicationOperator 12) (Sum.inr 2) isDerivation_multiplicationOperator_eleven
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 11),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 2))]
        simp only [multiplicationOperator_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 13 is the commutator of a numbered simple root generator
with the multiplication operator of index 10, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_thirteen :
    IsDerivation ((multiplicationOperator 13).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 10)
    (M' := multiplicationOperator 13) (Sum.inr 3) isDerivation_multiplicationOperator_ten
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 10),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 3))]
        simp only [multiplicationOperator_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 16 is the commutator of a numbered simple root generator
with the multiplication operator of index 14, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_sixteen :
    IsDerivation ((multiplicationOperator 16).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 14)
    (M' := multiplicationOperator 16) (Sum.inr 1) isDerivation_multiplicationOperator_fourteen
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 14),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 1))]
        simp only [multiplicationOperator_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 17 is the commutator of a numbered simple root generator
with the multiplication operator of index 14, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_seventeen :
    IsDerivation ((multiplicationOperator 17).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 14)
    (M' := multiplicationOperator 17) (Sum.inr 3) isDerivation_multiplicationOperator_fourteen
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 14),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 3))]
        simp only [multiplicationOperator_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 18 is the commutator of a numbered simple root generator
with the multiplication operator of index 16, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_eighteen :
    IsDerivation ((multiplicationOperator 18).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 16)
    (M' := multiplicationOperator 18) (Sum.inr 0) isDerivation_multiplicationOperator_sixteen
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 16),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 0))]
        simp only [multiplicationOperator_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 19 is the commutator of a numbered simple root generator
with the multiplication operator of index 16, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_nineteen :
    IsDerivation ((multiplicationOperator 19).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 16)
    (M' := multiplicationOperator 19) (Sum.inr 3) isDerivation_multiplicationOperator_sixteen
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 16),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 3))]
        simp only [multiplicationOperator_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 20 is the commutator of a numbered simple root generator
with the multiplication operator of index 18, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_twenty :
    IsDerivation ((multiplicationOperator 20).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 18)
    (M' := multiplicationOperator 20) (Sum.inr 3) isDerivation_multiplicationOperator_eighteen
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 18),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 3))]
        simp only [multiplicationOperator_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 21 is the commutator of a numbered simple root generator
with the multiplication operator of index 19, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_twentyOne :
    IsDerivation ((multiplicationOperator 21).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 19)
    (M' := multiplicationOperator 21) (Sum.inr 2) isDerivation_multiplicationOperator_nineteen
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 19),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 2))]
        simp only [multiplicationOperator_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 22 is the commutator of a numbered simple root generator
with the multiplication operator of index 20, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_twentyTwo :
    IsDerivation ((multiplicationOperator 22).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 20)
    (M' := multiplicationOperator 22) (Sum.inr 2) isDerivation_multiplicationOperator_twenty
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 20),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 2))]
        simp only [multiplicationOperator_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 23 is the commutator of a numbered simple root generator
with the multiplication operator of index 22, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_twentyThree :
    IsDerivation ((multiplicationOperator 23).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 22)
    (M' := multiplicationOperator 23) (Sum.inr 1) isDerivation_multiplicationOperator_twentyTwo
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 22),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 1))]
        simp only [multiplicationOperator_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 24 is the commutator of a numbered simple root generator
with the multiplication operator of index 23, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_twentyFour :
    IsDerivation ((multiplicationOperator 24).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 23)
    (M' := multiplicationOperator 24) (Sum.inr 2) isDerivation_multiplicationOperator_twentyThree
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 23),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 2))]
        simp only [multiplicationOperator_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 25 is the commutator of a numbered simple root generator
with the multiplication operator of index 24, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_twentyFive :
    IsDerivation ((multiplicationOperator 25).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 24)
    (M' := multiplicationOperator 25) (Sum.inr 3) isDerivation_multiplicationOperator_twentyFour
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 24),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inr 3))]
        simp only [multiplicationOperator_apply, rootMatrix_inr, loweringMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 6 is the commutator of a numbered simple root generator
with the multiplication operator of index 8, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_six :
    IsDerivation ((multiplicationOperator 6).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 8)
    (M' := multiplicationOperator 6) (Sum.inl 1) isDerivation_multiplicationOperator_eight
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 8),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 1))]
        simp only [multiplicationOperator_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 7 is the commutator of a numbered simple root generator
with the multiplication operator of index 9, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_seven :
    IsDerivation ((multiplicationOperator 7).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 9)
    (M' := multiplicationOperator 7) (Sum.inl 0) isDerivation_multiplicationOperator_nine
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 9),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 0))]
        simp only [multiplicationOperator_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 4 is the commutator of a numbered simple root generator
with the multiplication operator of index 6, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_four :
    IsDerivation ((multiplicationOperator 4).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 6)
    (M' := multiplicationOperator 4) (Sum.inl 2) isDerivation_multiplicationOperator_six
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 6),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 2))]
        simp only [multiplicationOperator_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 5 is the commutator of a numbered simple root generator
with the multiplication operator of index 6, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_five :
    IsDerivation ((multiplicationOperator 5).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 6)
    (M' := multiplicationOperator 5) (Sum.inl 0) isDerivation_multiplicationOperator_six
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 6),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 0))]
        simp only [multiplicationOperator_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 3 is the commutator of a numbered simple root generator
with the multiplication operator of index 5, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_three :
    IsDerivation ((multiplicationOperator 3).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 5)
    (M' := multiplicationOperator 3) (Sum.inl 2) isDerivation_multiplicationOperator_five
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 5),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 2))]
        simp only [multiplicationOperator_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 2 is the commutator of a numbered simple root generator
with the multiplication operator of index 3, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_two :
    IsDerivation ((multiplicationOperator 2).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 3)
    (M' := multiplicationOperator 2) (Sum.inl 1) isDerivation_multiplicationOperator_three
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 3),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 1))]
        simp only [multiplicationOperator_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 1 is the commutator of a numbered simple root generator
with the multiplication operator of index 2, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_one :
    IsDerivation ((multiplicationOperator 1).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 2)
    (M' := multiplicationOperator 1) (Sum.inl 2) isDerivation_multiplicationOperator_two
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 2),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 2))]
        simp only [multiplicationOperator_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- The multiplication operator of index 0 is the commutator of a numbered simple root generator
with the multiplication operator of index 1, so it differentiates the multiplication. -/
private theorem isDerivation_multiplicationOperator_zero :
    IsDerivation ((multiplicationOperator 0).map (Int.cast : ℤ → R)) :=
  isDerivation_of_bracket_congr (R := R) (M := multiplicationOperator 1)
    (M' := multiplicationOperator 0) (Sum.inl 3) isDerivation_multiplicationOperator_one
      (by
        intro a b
        simp only [Matrix.sub_apply,
          Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator 1),
          Matrix.IsStep.mul_apply (isStep_rootMatrix (Sum.inl 3))]
        simp only [multiplicationOperator_apply, rootMatrix_inl, raisingMatrix_apply]
        revert a b
        decide +kernel)

/-- **Each multiplication operator differentiates the invariant multiplication modulo two.** -/
theorem isDerivation_map_multiplicationOperator (a : Fin 26) :
    IsDerivation ((multiplicationOperator a).map (Int.cast : ℤ → R)) := by
  fin_cases a
  · exact isDerivation_multiplicationOperator_zero
  · exact isDerivation_multiplicationOperator_one
  · exact isDerivation_multiplicationOperator_two
  · exact isDerivation_multiplicationOperator_three
  · exact isDerivation_multiplicationOperator_four
  · exact isDerivation_multiplicationOperator_five
  · exact isDerivation_multiplicationOperator_six
  · exact isDerivation_multiplicationOperator_seven
  · exact isDerivation_multiplicationOperator_eight
  · exact isDerivation_multiplicationOperator_nine
  · exact isDerivation_multiplicationOperator_ten
  · exact isDerivation_multiplicationOperator_eleven
  · exact isDerivation_multiplicationOperator_twelve
  · exact isDerivation_multiplicationOperator_thirteen
  · exact isDerivation_multiplicationOperator_fourteen
  · exact isDerivation_multiplicationOperator_fifteen
  · exact isDerivation_multiplicationOperator_sixteen
  · exact isDerivation_multiplicationOperator_seventeen
  · exact isDerivation_multiplicationOperator_eighteen
  · exact isDerivation_multiplicationOperator_nineteen
  · exact isDerivation_multiplicationOperator_twenty
  · exact isDerivation_multiplicationOperator_twentyOne
  · exact isDerivation_multiplicationOperator_twentyTwo
  · exact isDerivation_multiplicationOperator_twentyThree
  · exact isDerivation_multiplicationOperator_twentyFour
  · exact isDerivation_multiplicationOperator_twentyFive

/-- **The short-root quotient coordinates annihilate the multiplication operators.** -/
theorem quotientCoordinate_multiplicationOperator (p a : Fin 26) :
    quotientCoordinate p (multiplicationOperator a) ≡ 0 [ZMOD 2] := by
  rw [quotientCoordinate_def]
  simp only [multiplicationOperator_apply]
  revert p a
  decide +kernel

end TauCeti.F4ShortRoot
