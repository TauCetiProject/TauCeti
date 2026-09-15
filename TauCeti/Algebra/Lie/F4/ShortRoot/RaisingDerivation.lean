/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.RootDerivation

/-!
# The numbered simple raising generators of type F4 differentiate the multiplication

The four numbered simple raising generators of the twenty-six-dimensional module of type `F₄`
differentiate its invariant symmetric multiplication, over the integers. Each of the four satisfies
the entrywise criterion `TauCeti.F4ShortRoot.isDerivation_rootMatrix_of_entries`, which is the same
family of relations between the structure constants of the multiplication and the coefficients of
the generator for all eight numbered simple root generators.

## Main results

* `TauCeti.F4ShortRoot.isDerivation_raisingMatrix`: **each numbered simple raising generator is a
  derivation of the invariant multiplication.**

## References

* N. Jacobson, *Exceptional Lie Algebras*, Lecture Notes in Pure and Applied Mathematics **1**,
  Marcel Dekker (1971), §I.4.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

/-- The zeroth numbered simple raising generator differentiates the multiplication. -/
private theorem isDerivation_raisingMatrix_zero : IsDerivation (rootMatrix (Sum.inl 0)) :=
  isDerivation_rootMatrix_of_entries _ (by decide +kernel)

/-- The first numbered simple raising generator differentiates the multiplication. -/
private theorem isDerivation_raisingMatrix_one : IsDerivation (rootMatrix (Sum.inl 1)) :=
  isDerivation_rootMatrix_of_entries _ (by decide +kernel)

/-- The second numbered simple raising generator differentiates the multiplication. -/
private theorem isDerivation_raisingMatrix_two : IsDerivation (rootMatrix (Sum.inl 2)) :=
  isDerivation_rootMatrix_of_entries _ (by decide +kernel)

/-- The third numbered simple raising generator differentiates the multiplication. -/
private theorem isDerivation_raisingMatrix_three : IsDerivation (rootMatrix (Sum.inl 3)) :=
  isDerivation_rootMatrix_of_entries _ (by decide +kernel)

/-- **Every numbered simple raising generator of the twenty-six-dimensional module of type `F₄`
differentiates the invariant symmetric multiplication.** -/
theorem isDerivation_raisingMatrix (i : Fin 4) : IsDerivation (raisingMatrix i) := by
  rw [← rootMatrix_inl]
  fin_cases i
  · exact isDerivation_raisingMatrix_zero
  · exact isDerivation_raisingMatrix_one
  · exact isDerivation_raisingMatrix_two
  · exact isDerivation_raisingMatrix_three

end TauCeti.F4ShortRoot
