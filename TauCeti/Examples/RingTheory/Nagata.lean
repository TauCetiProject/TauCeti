/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import TauCeti.FieldTheory.AlgebraicClosure
import TauCeti.RingTheory.Nagata

/-!
# Examples of Nagata rings

Fields, the zero ring and Artinian rings such as `ZMod n` for `n ≠ 0` are Nagata, being Noetherian
of Krull dimension zero. `ℤ`, `ℚ[X]` and Dedekind domains with perfect fraction field are
Noetherian Japanese domains of dimension at most one, hence Nagata, and so are their quotients and
their finite algebras, such as rings of integers of number fields. A discrete valuation ring is
Nagata exactly when it is Japanese. Over a Nagata ring, such as a field, integral closures in
reduced algebras of finite type are finite.
-/

open TauCeti.Ring NumberField

-- Fields are Nagata, and their prime quotients are Japanese.
example (k : Type*) [Field k] : IsNagata k := inferInstance

-- The zero ring is Nagata: it is Noetherian and has no prime ideals.
example : IsNagata (ZMod 1) := .of_krullDimLE_zero

-- Artinian rings are Nagata.
example (n : ℕ) [NeZero n] : IsNagata (ZMod n) := .of_krullDimLE_zero

-- `ℤ`, `ℚ[X]` and Dedekind domains with perfect fraction field are Nagata.
example : IsNagata ℤ := .of_isJapanese
example : IsNagata (Polynomial ℚ) := .of_isJapanese
example (R : Type*) [CommRing R] [IsDedekindDomain R] [PerfectField (FractionRing R)] :
    IsNagata R :=
  .of_isJapanese

-- Quotients of Nagata rings are Nagata.
example (I : Ideal ℤ) : IsNagata (ℤ ⧸ I) :=
  have : IsNagata ℤ := .of_isJapanese
  inferInstance

-- A finite algebra over `ℤ`, such as the ring of integers of a number field, is Nagata.
example (K : Type*) [Field K] [NumberField K] : IsNagata (𝓞 K) :=
  have : IsNagata ℤ := .of_isJapanese
  .of_finite ℤ (𝓞 K)

-- A Nagata domain is Japanese.
example (R : Type*) [CommRing R] [IsDomain R] [IsNagata R] : IsJapanese R := inferInstance

-- A discrete valuation ring is Nagata if and only if it is Japanese.
example (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsNagata R ↔ IsJapanese R :=
  isNagata_iff_isJapanese

-- The integral closure of a field `k` in a reduced algebra of finite type over `k` is
-- finite-dimensional over `k`.
example (k S : Type*) [Field k] [CommRing S] [IsReduced S] [Algebra k S]
    [Algebra.FiniteType k S] : Module.Finite k (integralClosure k S) :=
  IsNagata.finite_integralClosure S

-- The algebraic part of the finitely generated, transcendental field extension `ℚ(X, Y)` of `ℚ`
-- is finite over `ℚ`.
example : FiniteDimensional ℚ (algebraicClosure ℚ (FractionRing (MvPolynomial (Fin 2) ℚ))) :=
  have : Algebra.EssFiniteType ℚ (FractionRing (MvPolynomial (Fin 2) ℚ)) :=
    .comp ℚ (MvPolynomial (Fin 2) ℚ) _
  inferInstance
