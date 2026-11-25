/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-!
# Complex embeddings of rings of integers

A number field `K` has a complex embedding `K →+* ℂ`, and `𝓞 K → K` is injective, so the ring of
integers `𝓞 K` embeds into `ℂ`. This lets identities in `𝓞 K` be checked after mapping to `ℂ`.

## Main results

* `NumberField.RingOfIntegers.exists_injective_ringHom_complex`: there is an injective ring
  homomorphism `𝓞 K →+* ℂ`.
-/

public section

open scoped NumberField

namespace NumberField.RingOfIntegers

variable (K : Type*) [Field K] [NumberField K]

/-- The ring of integers of a number field embeds into `ℂ`. -/
theorem exists_injective_ringHom_complex : ∃ f : 𝓞 K →+* ℂ, Function.Injective f :=
  ⟨(Classical.arbitrary (K →+* ℂ)).comp (algebraMap (𝓞 K) K),
    (Classical.arbitrary (K →+* ℂ)).injective.comp (FaithfulSMul.algebraMap_injective _ _)⟩

end NumberField.RingOfIntegers
