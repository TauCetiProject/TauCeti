/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.SepClosed
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic

/-!
# Regular quadratic forms over separably closed fields

Over a separably closed field with two invertible, any two regular quadratic forms of the
same rank are isometric. Thus rank completely determines a `RegularFormClass`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter II, §3.
* `QuadraticForm.equivalent_of_finrank_eq_of_isSepClosed` supplies the classification of regular
  forms by dimension; Mathlib's analogous algebraically closed classification is
  `QuadraticForm.equivalent_of_isAlgClosed`.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [IsSepClosed K] [Invertible (2 : K)]

/-- Rank determines a regular-form class over a separably closed field. -/
theorem RegularFormClass.rank_injective_of_isSepClosed :
    Function.Injective (RegularFormClass.rank (K := K)) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | _ p =>
    induction y using Quotient.inductionOn with
    | _ q =>
      refine RegularFormClass.mk_eq_mk_iff.mpr <|
        (presentedForm p).equivalent_of_finrank_eq_of_isSepClosed (presentedForm q)
          (nondegenerate_presentedForm p) (nondegenerate_presentedForm q) ?_
      simpa using h

end TauCeti
