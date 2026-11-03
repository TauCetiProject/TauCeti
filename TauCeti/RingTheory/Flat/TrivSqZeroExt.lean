/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.RingTheory.TrivSqZeroExt
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Pure

/-!
# Non-flatness of trivial square-zero extensions by the residue field

Over a Noetherian local ring `R` which is not a field, `TrivSqZeroExt R (R ⧸ 𝔪)` is not flat:
its direct summand `R ⧸ 𝔪` would be flat, making `𝔪` idempotent and hence zero by Krull's
intersection theorem.

## Main results

* `TrivSqZeroExt.not_flat`: over a Noetherian local ring that is not a field,
  `TrivSqZeroExt R (R ⧸ 𝔪)` is not flat.
-/

public section

open IsLocalRing

namespace TrivSqZeroExt

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Over a Noetherian local ring which is not a field, `TrivSqZeroExt R (R ⧸ 𝔪)` is not flat. -/
theorem not_flat [IsNoetherianRing R] (h : ¬ IsField R) :
    ¬ Module.Flat R (TrivSqZeroExt R (R ⧸ maximalIdeal R)) := fun _ ↦ by
  -- The direct summand `R ⧸ 𝔪` would be flat, making `𝔪` idempotent and hence zero.
  have : (maximalIdeal R).Pure := .of_retract (inrHom R _) (sndHom R _) (by ext; simp)
  rcases (Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing _).1
    (maximalIdeal R).isIdempotentElem_of_pure with h' | h'
  · exact h (isField_iff_maximalIdeal_eq.2 h')
  · exact (maximalIdeal.isMaximal R).ne_top h'

end TrivSqZeroExt
