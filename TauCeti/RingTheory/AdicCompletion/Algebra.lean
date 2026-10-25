/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Compatibility of the ring-valued projections of an adic completion

The projections to `R ⧸ I ^ n` commute with reduction between powers. This expresses
the compatibility condition of Mathlib's adic completion using its ring-valued projections,
for use when constructing maps of completed algebras from quotient comparisons.
-/

public section

namespace TauCeti.AdicCompletion

/-- Reducing a projection of an adic completion gives the projection at the smaller power. -/
@[simp]
theorem factorPow_evalₐ {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (_root_.AdicCompletion.evalₐ I n x) =
      _root_.AdicCompletion.evalₐ I m x := by
  induction x using _root_.AdicCompletion.induction_on I R with
  | h a =>
    simp only [_root_.AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using (a.property h).symm

end TauCeti.AdicCompletion
