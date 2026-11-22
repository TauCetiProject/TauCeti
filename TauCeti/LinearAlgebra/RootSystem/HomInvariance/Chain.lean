/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Chain
public import TauCeti.LinearAlgebra.RootSystem.HomInvariance

import TauCeti.LinearAlgebra.RootSystem.PairingInvariance

/-!
# Invariance of root-string coefficients under homomorphisms of root pairings

In a finite crystallographic root pairing in characteristic zero, a homomorphism `f : P.Hom P₂`
preserves the root-string coefficients `RootPairing.chainTopCoeff` and
`RootPairing.chainBotCoeff`.

These invariance facts show that an automorphism of a root system permutes the matrices of Geck's
construction, as developed in `TauCeti.LinearAlgebra.RootSystem.GeckConstruction.Symmetry`.

## Main results

* `RootPairing.Hom.chainTopCoeff_indexEquiv` and `RootPairing.Hom.chainBotCoeff_indexEquiv`:
  a homomorphism of finite crystallographic root pairings preserves the two root-string
  coefficients.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

namespace RootPairing.Hom

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂}
  (f : P.Hom P₂) [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic]

/-- The index bijection of a homomorphism of finite crystallographic root pairings preserves the
number of times one may add `P.root i` to `P.root j` and stay among the roots. -/
@[simp]
theorem chainTopCoeff_indexEquiv (i j : ι) :
    letI := Finite.of_equiv ι f.indexEquiv
    letI := f.isValuedIn ℤ
    P₂.chainTopCoeff (f.indexEquiv i) (f.indexEquiv j) = P.chainTopCoeff i j := by
  let := f.isValuedIn ℤ
  exact chainTopCoeff_eq_of_pairingIn f.indexEquiv (f.pairingIn_indexEquiv ℤ) i j

/-- The index bijection of a homomorphism of finite crystallographic root pairings preserves the
number of times one may subtract `P.root i` from `P.root j` and stay among the roots. -/
@[simp]
theorem chainBotCoeff_indexEquiv (i j : ι) :
    letI := Finite.of_equiv ι f.indexEquiv
    letI := f.isValuedIn ℤ
    P₂.chainBotCoeff (f.indexEquiv i) (f.indexEquiv j) = P.chainBotCoeff i j := by
  let := f.isValuedIn ℤ
  exact chainBotCoeff_eq_of_pairingIn f.indexEquiv (f.pairingIn_indexEquiv ℤ) i j

end RootPairing.Hom
