/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Countable
public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.RingTheory.DedekindDomain.Countable
import Mathlib.Data.Rat.Encodable

/-!
# Number fields and their rings of integers are countable

A number field is a finite-dimensional vector space over the countable field `ℚ`, and its ring of
integers is a finitely generated `ℤ`-module, so both are countable. Through
`IsDedekindDomain.HeightOneSpectrum.countable`, imported here, the second instance also gives a
number field countably many finite places.
-/

public section

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- A number field is countable. -/
instance instCountable : Countable K :=
  Countable.of_moduleFinite (R := ℚ)

/-- The ring of integers of a number field is countable. -/
instance RingOfIntegers.instCountable : Countable (𝓞 K) :=
  Countable.of_moduleFinite (R := ℤ)

end NumberField
