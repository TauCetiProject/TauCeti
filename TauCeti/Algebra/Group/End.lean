/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.AddChar

/-!
# Powers of an additively indexed family of endomorphisms

A family `f : ℕ → M →* M` of endomorphisms of a monoid indexed additively, so that `f 0` is the
identity and `f (a + b)` is the composite of `f a` and `f b`, is an additive character
`AddChar ℕ (Monoid.End M)`, and so turns multiplication of indices into powers in the
endomorphism monoid: the `m`-th power of `f k` is `f (k * m)`.

This is the shape of the iteration laws of an iterated Frobenius, `Frob_0 = id` and
`Frob_(a + b) = Frob_a ∘ Frob_b`, and the lemma packages Mathlib's `AddChar.map_nsmul_eq_pow`
for that shape once, so that each Chevalley carrier only supplies its two iteration laws.

## Main results

* `TauCeti.Monoid.End.pow_eq_of_add_eq_comp`: `f k ^ m = f (k * m)` in `Monoid.End M`.
-/

public section

namespace TauCeti

variable {M : Type*} [Monoid M]

/-- **Indices multiply under taking powers** in the endomorphism monoid: if `f 0` is the identity
and `f (a + b) = f a ∘ f b`, then the `m`-th power of `f k` is `f (k * m)`. -/
-- `Monoid.End` is definitionally a bundled `MonoidHom`; the `show` picks its composition monoid
-- structure before the power is elaborated.
theorem Monoid.End.pow_eq_of_add_eq_comp (f : ℕ → M →* M) (h0 : f 0 = MonoidHom.id M)
    (hadd : ∀ a b, f (a + b) = (f a).comp (f b)) (k m : ℕ) :
    (show Monoid.End M from f k) ^ m = f (k * m) := by
  let ψ : AddChar ℕ (Monoid.End M) :=
    { toFun := fun j => f j
      map_zero_eq_one' := h0
      map_add_eq_mul' := hadd }
  have hpow := AddChar.map_nsmul_eq_pow ψ m k
  -- Expose the function supplied to `AddChar.mk` and the natural-number scalar action.
  change f (m * k) = (show Monoid.End M from f k) ^ m at hpow
  rw [Nat.mul_comm] at hpow
  exact hpow.symm

end TauCeti
