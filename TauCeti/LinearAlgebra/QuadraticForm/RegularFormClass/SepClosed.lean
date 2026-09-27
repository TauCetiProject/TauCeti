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
* `QuadraticForm.equivalent_weightedSumSquares_of_isSepClosed` supplies the normalization to
  the standard sum of squares; Mathlib's analogous algebraically closed classification is
  `QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed`.
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
      have hp := (presentedForm p).equivalent_weightedSumSquares_of_isSepClosed
        ((QuadraticMap.nondegenerate_associated_iff (Q := presentedForm p)).2
          (nondegenerate_presentedForm p)).1
      have hq := (presentedForm q).equivalent_weightedSumSquares_of_isSepClosed
        ((QuadraticMap.nondegenerate_associated_iff (Q := presentedForm q)).2
          (nondegenerate_presentedForm q)).1
      rcases p with ⟨n, w⟩
      rcases q with ⟨m, v⟩
      have h' : n = m := by simpa only [RegularFormClass.rank_mk] using h
      subst m
      apply RegularFormClass.mk_eq_mk_iff.mpr
      exact hp.trans hq.symm

end TauCeti
