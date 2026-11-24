/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Function

/-!
# The inverse of a strictly monotone function on a set

A function strictly monotone on a set `s` of a linear order is injective there, so
`Function.invFunOn f s` inverts it on `s`; this inverse is strictly monotone on the image `f '' s`
(`StrictMonoOn.invFunOn`).
-/

public section

open Function Set

/-- The inverse `invFunOn f s` of a function strictly monotone on `s` is strictly monotone on the
image `f '' s`. -/
theorem StrictMonoOn.invFunOn {α β : Type*} [LinearOrder α] [Preorder β] [Nonempty α]
    {f : α → β} {s : Set α} (hf : StrictMonoOn f s) : StrictMonoOn (invFunOn f s) (f '' s) := by
  rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ h
  rw [hf.injOn.leftInvOn_invFunOn hx₁, hf.injOn.leftInvOn_invFunOn hx₂]
  exact (hf.lt_iff_lt hx₁ hx₂).1 h
