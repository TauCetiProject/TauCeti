/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Small.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Logic.Small.Basic

/-!
# Basic properties of adic completions

This file records foundational properties of `AdicCompletion I M` that require no Noetherian or
injectivity hypotheses.

## Main declarations

* `TauCeti.AdicCompletion.instSmall`: `AdicCompletion I M` is `Small.{v}` whenever `M` is
  `Small.{v}`.
-/

public section

universe v

namespace TauCeti.AdicCompletion

/-- The adic completion of a `Small.{v}` module is `Small.{v}`, as a subtype of a countable
product of quotients of `M`. In particular `[Small.{v} R]` supplies
`[Small.{v} (AdicCompletion I R)]` for module injectivity over the completion. -/
instance instSmall {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M]
    [Module R M] [Small.{v} M] : Small.{v} (_root_.AdicCompletion I M) := by
  have (n : ℕ) : Small.{v} (M ⧸ (I ^ n • ⊤ : Submodule R M)) :=
    small_of_surjective (Submodule.Quotient.mk_surjective _)
  exact small_of_injective (f := Subtype.val) Subtype.val_injective

end TauCeti.AdicCompletion
