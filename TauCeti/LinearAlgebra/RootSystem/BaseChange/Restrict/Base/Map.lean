/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Base.Basic
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Hom

/-!
# Equivalence transport of restricted bases under scalar restriction

This file proves that restricting a base `b` of a balanced root pairing to a subfield `K`
(`RootPairing.Base.restrictScalars'`) commutes with transporting `b` along an equivalence of root
pairings (`RootPairing.Base.map` and `RootPairing.Equiv.restrictScalars'`).

## Main results

* `RootPairing.Base.restrictScalars'_map`: `Base.restrictScalars'` commutes with `Base.map`.

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

/-- `Base.restrictScalars'` commutes with transporting a base along an equivalence. -/
@[simp]
theorem Base.restrictScalars'_map {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [AddCommGroup N₂]
    [Module L M₂] [Module L N₂] {Q : RootPairing ι₂ L M₂ N₂} [Module K M₂] [Module K N₂]
    [IsScalarTower K L M₂] [IsScalarTower K L N₂] [Q.IsBalanced] [Q.IsValuedIn K]
    (e : P.Equiv Q) :
    (b.map e).restrictScalars' K = (b.restrictScalars' K).map (e.restrictScalars' K) := by
  classical
  apply Base.ext
  rw [support_restrictScalars', support_map_eq, support_map_eq, support_restrictScalars',
    Equiv.indexEquiv_restrictScalars']

end RootPairing
