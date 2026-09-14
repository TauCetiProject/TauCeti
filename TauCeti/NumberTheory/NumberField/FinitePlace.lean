/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Finite places of number fields

This file records general facts about the finite places of a number field.

The main content is that a number field always *has* a finite place: the finite places are the
height one primes of its ring of integers, and that ring is a Dedekind domain which is not a
field, so it has a maximal ideal. Recording this as a `Nonempty` instance lets local-global
arguments pick a finite place with `Classical.arbitrary` whenever a hypothesis quantified over
all finite places has to be used at some place — for instance to read off an invariant, such as
the dimension of the underlying space, that is the same at every place. Without the instance
each such argument has to rebuild the existence proof inline.
-/

public section
noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti

variable {K : Type*} [Field K]

/-- A number field has a finite place: its ring of integers is not a field. -/
instance [NumberField K] : Nonempty (HeightOneSpectrum (𝓞 K)) :=
  ⟨(HeightOneSpectrum.equivMaximalSpectrum (RingOfIntegers.not_isField K)).symm
    (Classical.choice (inferInstance : Nonempty (MaximalSpectrum (𝓞 K))))⟩

end TauCeti
