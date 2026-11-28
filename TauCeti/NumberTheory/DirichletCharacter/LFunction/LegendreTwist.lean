/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.Data.Nat.GCD
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LegendreTwist
import TauCeti.Data.Nat.Prime.Finset
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel

/-!
# The L-function of a Legendre twist

The quadratic twist used in prime selection is the common-level product with a Jacobi
character. Its L-function agrees with that of the Legendre twist at the product level:
raising the level from the least common multiple to the product introduces no new Euler
factors, via `DirichletCharacter.LFunction_changeLevel_eq_of_primeFactors_eq`.
In particular, a zero-free box for the common-level twists can be used in the
one-sided criterion for the signed prime remainder.
-/

public section

namespace DirichletCharacter

/-- The product-level Legendre twist and the common-level product with the Jacobi character
have the same L-function away from the possible principal pole. -/
theorem LFunction_legendreTwist_eq_mul_jacobiChar {q d : ℕ} [NeZero q] [Fact d.Prime]
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : χ.mul (TauCeti.jacobiChar ℂ d) ≠ 1 ∨ s ≠ 1) :
    (χ.legendreTwist d).LFunction s = (χ.mul (TauCeti.jacobiChar ℂ d)).LFunction s := by
  have hprimes : (q * d).primeFactors = (q.lcm d).primeFactors := by
    rw [Nat.primeFactors_mul (NeZero.ne q) (NeZero.ne d),
      Nat.primeFactors_lcm (NeZero.ne q) (NeZero.ne d)]
  rw [← χ.changeLevel_mul_jacobiChar_eq_legendreTwist d]
  exact LFunction_changeLevel_eq_of_primeFactors_eq _ _ hprimes hs

end DirichletCharacter
