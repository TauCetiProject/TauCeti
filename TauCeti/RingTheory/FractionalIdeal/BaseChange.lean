/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.IsTensorProduct

import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.Algebra.Module.Lattice

/-!
# A nonzero fractional ideal is a lattice in the fraction field

A nonzero fractional ideal `I` of a domain `R` spans its fraction field `K`, so the inclusion
`I → K` identifies `K ⊗[R] I` with `K`. Composing with a further scalar extension, this computes
the scalar extension of `I` along any ring homomorphism out of `K`, for instance the complex
fibres of a fractional ideal of a number field at its complex embeddings.
-/

public section

open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- The inclusion of a nonzero fractional ideal into the fraction field is a scalar extension to
the fraction field: `K ⊗[R] I ≅ K`. -/
theorem isBaseChange_subtype {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    IsBaseChange K (I : Submodule R K).subtype := by
  refine (isLocalizedModule_iff_isBaseChange R⁰ K _).mp
    (Submodule.IsLattice.isLocalizedModule_subtype K _ ?_)
  obtain ⟨x, hxI, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (coeToSubmodule_ne_bot.mpr hI)
  refine eq_top_iff.mpr fun y _ ↦ ?_
  rw [show y = (y / x) • x by rw [smul_eq_mul, div_mul_cancel₀ y hx]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hxI)

end FractionalIdeal
