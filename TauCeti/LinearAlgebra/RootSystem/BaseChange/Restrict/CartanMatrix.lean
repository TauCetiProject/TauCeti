/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Base

/-!
# Cartan matrices under scalar restriction

This file shows that the Cartan matrix of a restricted base `b.restrictScalars' K` agrees with
the Cartan matrix of `b` along `RootPairing.Base.supportRestrictScalars'Equiv`.

## Main results

* `RootPairing.Base.cartanMatrixIn_restrictScalars'_apply` and
  `RootPairing.Base.cartanMatrix_restrictScalars'_apply`: equality of the `T`-valued and integral
  Cartan matrices under scalar restriction.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§1, 6.
-/

public section

namespace RootPairing

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  {P : RootPairing ι L M N} (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced] [P.IsValuedIn K] (b : P.Base)

/-- The `T`-valued Cartan matrix of `b.restrictScalars' K` agrees with that of `b` along
`Base.supportRestrictScalars'Equiv`. -/
@[simp]
theorem Base.cartanMatrixIn_restrictScalars'_apply (T : Type*) [CommRing T] [Algebra T K]
    [Algebra T L] [IsScalarTower T K L] [P.IsValuedIn T]
    (i j : (b.restrictScalars' K).support) :
    (b.restrictScalars' K).cartanMatrixIn T i j =
      b.cartanMatrixIn T (b.supportRestrictScalars'Equiv K i)
        (b.supportRestrictScalars'Equiv K j) := by
  simp only [Base.cartanMatrixIn, Matrix.of_apply, Base.coe_supportRestrictScalars'Equiv,
    P.restrictScalars'_pairingIn]

-- Not `@[simp]`: `cartanMatrix` is an `abbrev` for `cartanMatrixIn ℤ`, which
-- `Base.cartanMatrixIn_restrictScalars'_apply` already simplifies (`simpNF`).
/-- The Cartan matrix of `b.restrictScalars' K` agrees with that of `b` along
`Base.supportRestrictScalars'Equiv`. -/
theorem Base.cartanMatrix_restrictScalars'_apply [P.IsCrystallographic]
    (i j : (b.restrictScalars' K).support) :
    (b.restrictScalars' K).cartanMatrix i j =
      b.cartanMatrix (b.supportRestrictScalars'Equiv K i)
        (b.supportRestrictScalars'Equiv K j) :=
  b.cartanMatrixIn_restrictScalars'_apply K ℤ i j

end RootPairing
