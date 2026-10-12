/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.FiniteHasse
import Mathlib.Algebra.FiniteSupport.Basic
import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic
import TauCeti.NumberTheory.QuadraticForm.Global.HilbertSymbol

/-!
# Finite support of global Hasse signs

The Hasse signs of a regular quadratic form over a number field are nontrivial at only finitely
many finite places. After choosing one diagonalization, the Hasse sign at each finite place is the
pairwise product of local Hilbert symbols of the diagonal coefficients, and each such symbol is
trivial away from the dyadic places and the primes supporting the two coefficients.

## Main result

* `QuadraticForm.hasFiniteMulSupport_finiteHasse`: the finite-place Hasse signs of a regular
  global form have finite multiplicative support.

The good-place calculation follows O'Meara, *Introduction to Quadratic Forms*, 66:6, using the
unramified norm-equation calculation for each pair of coefficients.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- **Almost-all triviality of the finite Hasse sign.** The Hasse sign of a regular quadratic
form over a number field is one at all but finitely many finite places. -/
@[fun_prop]
theorem _root_.QuadraticForm.hasFiniteMulSupport_finiteHasse
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.HasFiniteMulSupport (Q.finiteHasse hQ) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  have hp' : Q.Equivalent
      (QuadraticMap.weightedSumSquares K fun i ↦ (p.2 i : K)) := by
    rwa [← presentedForm_eq_weightedSumSquares_coe]
  rw [funext (Q.finiteHasse_eq_prod_hilbertSymbol hQ hp')]
  fun_prop

end TauCeti
