/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Universe smallness of adic completions

The `I`-adic completion `AdicCompletion I M` is a subtype of `∀ n : ℕ, M ⧸ (I ^ n • ⊤)`, so
whenever `M` is `v`-small, its quotients, their countable product, and hence `AdicCompletion I M`
are `v`-small as well (`AdicCompletion.small`).

## Main declarations

* `AdicCompletion.small`: the `I`-adic completion of a `v`-small module is `v`-small.
-/

public section

namespace AdicCompletion

universe v

variable {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

/-- The `I`-adic completion of a `v`-small module is `v`-small. -/
instance small [Small.{v} M] : Small.{v} (AdicCompletion I M) :=
  small_of_injective Subtype.val_injective

end AdicCompletion
