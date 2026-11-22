/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Addition

/-!
# Hahn series monomials

Mathlib's `HahnSeries.ofFinsuppLinearMap` views a finitely supported function `Γ →₀ V` as a Hahn
series. This file records that it sends `Finsupp.single a v` to the monomial
`HahnSeries.single a v`, which reduces computations with finitely supported series, such as
polynomial loops, to monomials.

The coefficientwise scalar action also commutes with formation of a monomial.
-/

public section

namespace HahnSeries

/-- Scaling the coefficient of a Hahn monomial scales the whole monomial. -/
theorem single_smul {Γ R V : Type*} [PartialOrder Γ] [Zero V] [SMulZeroClass R V]
    (a : Γ) (r : R) (v : V) : single a (r • v) = r • single a v := by
  ext b
  rcases eq_or_ne b a with rfl | h
  · simp only [coeff_smul, coeff_single_same]
  · simp only [coeff_smul, coeff_single_of_ne h, smul_zero]

variable {Γ R V : Type*} [PartialOrder Γ] [Semiring R] [AddCommMonoid V] [Module R V]

/-- A finitely supported function with a single nonzero value is a monomial. -/
@[simp]
theorem ofFinsuppLinearMap_single (a : Γ) (v : V) :
    ofFinsuppLinearMap R (Finsupp.single a v) = single a v := by
  ext b
  rcases eq_or_ne b a with rfl | h
  · simp
  · simp [h, coeff_single_of_ne]

end HahnSeries
