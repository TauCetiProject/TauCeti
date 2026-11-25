/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Pullback

/-!
# Membership in the pullback of rings

Mathlib defines the pullback `RingHom.pullback f g` of `f : R →+* T` and `g : S →+* T` as the
equaliser of `f ∘ fst` and `g ∘ snd` in `R × S`. This file states membership in it as the equation
`f x.1 = g x.2`, so that proofs need not unfold the equaliser.

## Main results

* `RingHom.mem_pullback`: `x ∈ f.pullback g ↔ f x.1 = g x.2`.
-/

public section

namespace RingHom

variable {R S T : Type*} [Ring R] [Ring S] [Semiring T] {f : R →+* T} {g : S →+* T}

/-- A pair `x : R × S` lies in the pullback of `f : R →+* T` and `g : S →+* T` exactly when
`f x.1 = g x.2`. -/
theorem mem_pullback {x : R × S} : x ∈ f.pullback g ↔ f x.1 = g x.2 :=
  Iff.rfl

end RingHom
