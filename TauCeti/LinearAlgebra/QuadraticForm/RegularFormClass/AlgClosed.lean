/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Complex
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic

/-!
# Regular quadratic forms over algebraically closed fields

Over an algebraically closed field with two invertible, any two regular quadratic forms of the
same rank are isometric. Thus rank completely determines a `RegularFormClass`.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [IsAlgClosed K] [Invertible (2 : K)]

/-- Rank determines a regular-form class over an algebraically closed field. -/
theorem RegularFormClass.rank_injective_of_isAlgClosed :
    Function.Injective (RegularFormClass.rank (K := K)) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | _ p =>
    induction y using Quotient.inductionOn with
    | _ q =>
      have h' : p.1 = q.1 := by simpa only [RegularFormClass.rank_mk] using h
      apply RegularFormClass.mk_eq_mk_iff.mpr
      apply QuadraticForm.equivalent_of_finrank_eq_of_isAlgClosed
        (presentedForm p) (presentedForm q)
        (nondegenerate_presentedForm p) (nondegenerate_presentedForm q)
      simpa only [Module.finrank_fin_fun] using h'

end TauCeti
