/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Chain

/-!
# Root strings through orthogonal roots

In a finite reduced crystallographic root pairing, orthogonal roots whose sum is a root
have the three-term string `β - α, β, β + α`. In particular both string coefficients are one.
This distinguishes such pairs from orthogonal simple roots, whose sum is not a root, and
supplies the coefficient of absolute value two in the Chevalley commutator formula.

The argument uses the root-string pairing equation and the bound of three on the sum of
the string coefficients. See Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4–6,
Chapter VI, §1.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced] {α β : ι}

/-- The string through orthogonal roots with a root as their sum has precisely one step
in each direction. -/
theorem chainBotCoeff_eq_one_and_chainTopCoeff_eq_one_of_pairingIn_eq_zero
    (h : P.root α + P.root β ∈ Set.range P.root) (horth : P.pairingIn ℤ β α = 0) :
    P.chainBotCoeff α β = 1 ∧ P.chainTopCoeff α β = 1 := by
  have hli := P.linearIndependent_of_add_mem_range_root' h
  have hdiff := P.chainBotCoeff_sub_chainTopCoeff hli
  have hbound := P.chainBotCoeff_add_chainTopCoeff_le_three (i := α) (j := β)
  have hpos := P.one_le_chainTopCoeff_of_root_add_mem h
  rw [horth] at hdiff
  omega

end RootPairing
