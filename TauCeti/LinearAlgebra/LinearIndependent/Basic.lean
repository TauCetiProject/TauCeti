/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Linear independence on the image of an injective reindexing

A family `v` is linearly independent on the image `f '' s` of a set under a map injective on `s`
exactly when `v ∘ f` is linearly independent on `s`. This is the linear counterpart of Mathlib's
`affineIndepOn_image_iff`, combining `LinearIndepOn.comp_of_image` and
`LinearIndepOn.image_of_comp`.

## Main results

* `TauCeti.linearIndepOn_image_iff`: linear independence on `f '' s` versus of `v ∘ f` on `s`.
-/

public section

namespace TauCeti

variable {ι ι' R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A family `v` is linearly independent on `f '' s` exactly when `v ∘ f` is linearly independent
on `s`, for `f` injective on `s`. -/
theorem linearIndepOn_image_iff {s : Set ι} {f : ι → ι'} (v : ι' → M) (hf : Set.InjOn f s) :
    LinearIndepOn R v (f '' s) ↔ LinearIndepOn R (v ∘ f) s :=
  ⟨fun h ↦ h.comp_of_image hf, fun h ↦ h.image_of_comp f v⟩

end TauCeti
