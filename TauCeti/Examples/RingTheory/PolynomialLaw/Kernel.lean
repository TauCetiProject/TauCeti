/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.PolynomialLaw.Kernel
import Mathlib.Algebra.Field.Rat

/-!
# Examples: the kernel of a polynomial law

* The identity law is faithful: `b ⊗ x + m = m` for all `S`, `b`, `m` forces `x = 0`.
* The zero law has kernel everything, so it is not faithful on a nonzero module.
* The law of the first projection `ℚ × ℚ → ℚ` has kernel the second factor, and the law it
  induces on the quotient is faithful.
-/

open PolynomialLaw

-- The identity law on `ℚ²` is faithful.
example : (PolynomialLaw.id : (ℚ × ℚ) →ₚₗ[ℚ] (ℚ × ℚ)).IsFaithful :=
  isFaithful_id

-- The zero law has kernel everything ...
example : (0 : (ℚ × ℚ) →ₚₗ[ℚ] ℚ).ker = ⊤ :=
  ker_zero

-- ... so it is not faithful on a nonzero module.
example : ¬ (0 : ℚ →ₚₗ[ℚ] ℚ).IsFaithful := by
  rw [isFaithful_iff, ker_zero]
  exact top_ne_bot

-- The law of the first projection `ℚ × ℚ → ℚ` has kernel the second factor `0 × ℚ`.
example : (LinearMap.fst ℚ ℚ ℚ).toPolynomialLaw.ker = LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) :=
  LinearMap.ker_toPolynomialLaw _

example : ((0 : ℚ), (1 : ℚ)) ∈ (LinearMap.fst ℚ ℚ ℚ).toPolynomialLaw.ker := by
  simp

-- The first projection factors through `(ℚ × ℚ) ⧸ Ker`, and the induced law is faithful.
example : (LinearMap.fst ℚ ℚ ℚ).toPolynomialLaw =
    ((LinearMap.fst ℚ ℚ ℚ).toPolynomialLaw.liftQ _ le_rfl).comp
      (LinearMap.fst ℚ ℚ ℚ).toPolynomialLaw.ker.mkQ.toPolynomialLaw :=
  (liftQ_comp_mkQ le_rfl).symm

example : ((LinearMap.fst ℚ ℚ ℚ).toPolynomialLaw.liftQ _ le_rfl).IsFaithful :=
  isFaithful_liftQ_ker
