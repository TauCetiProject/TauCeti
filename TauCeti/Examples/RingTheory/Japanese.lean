/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.NumberField.Basic
import TauCeti.RingTheory.Japanese

/-!
# Examples of N-1 and Japanese domains

Fields are Japanese, with no separability hypothesis on the extension. `ℤ`, the polynomial ring
`ℚ[X]` and the ring of integers of a number field are Noetherian integrally closed domains of
characteristic zero, hence Japanese and N-1. For `ℤ` the defining property applies to the fraction
field `ℚ` rather than `FractionRing ℤ`: the integral closure of `ℤ` in any number field, in any
universe, is a finite `ℤ`-module.
-/

open TauCeti.Ring NumberField

-- Fields are Japanese, inseparable extensions included, and hence N-1.
example (k : Type*) [Field k] : IsJapanese k := inferInstance
example (k : Type*) [Field k] : IsN1 k := inferInstance

-- Noetherian integrally closed domains of characteristic zero are Japanese.
example : IsJapanese ℤ := inferInstance
example : IsJapanese (Polynomial ℚ) := inferInstance
example (K : Type*) [Field K] [NumberField K] : IsJapanese (𝓞 K) := inferInstance

-- The integral closure of `ℤ` in a number field is finite over `ℤ`, read off from the fraction
-- field `ℚ` of `ℤ`.
example (L : Type*) [Field L] [NumberField L] : Module.Finite ℤ (integralClosure ℤ L) :=
  IsJapanese.finite_integralClosure ℚ L

-- An integrally closed domain is N-1, with no Noetherian or characteristic hypothesis.
example (R : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] : IsN1 R := inferInstance

-- For a Noetherian domain of characteristic zero, being Japanese and being N-1 agree.
example (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero (FractionRing R)] :
    IsJapanese R ↔ IsN1 R :=
  isJapanese_iff_isN1

-- Localizations of N-1 and Japanese domains are N-1 and Japanese; at a prime this is found by
-- instance search.
example (p : Ideal ℤ) [p.IsPrime] : IsJapanese (Localization.AtPrime p) := inferInstance

example (R : Type*) [CommRing R] [IsDomain R] [IsN1 R] (p : Ideal R) [p.IsPrime] :
    IsN1 (Localization.AtPrime p) :=
  inferInstance
