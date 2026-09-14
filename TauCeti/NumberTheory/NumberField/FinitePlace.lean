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
