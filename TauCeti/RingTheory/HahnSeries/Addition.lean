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

/-- Scaling the coefficient of a Hahn monomial scales the whole monomial.
This generalizes the `map_smul'` law of Mathlib's `HahnSeries.single.linearMap`, using
`HahnSeries.map_single` for the zero-preserving coefficient action. -/
theorem TauCeti.hahnSeries_single_smul {Γ R V : Type*} [PartialOrder Γ] [Zero V]
    [SMulZeroClass R V] (a : Γ) (r : R) (v : V) :
    HahnSeries.single a (r • v) = r • HahnSeries.single a v := by
  let f := SMulZeroClass.toZeroHom V r
  calc
    HahnSeries.single a (r • v) = (HahnSeries.single a v).map f :=
      (HahnSeries.map_single (a := a) (r := v) f).symm
    _ = r • HahnSeries.single a v := by
      ext b
      simp only [HahnSeries.map_coeff, HahnSeries.coeff_smul, f,
        SMulZeroClass.toZeroHom_apply]

namespace HahnSeries

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
