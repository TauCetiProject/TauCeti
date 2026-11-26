/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientRing

/-!
# `ℤ` modulo a power of `(p)` is `ZMod (p ^ n)`

Mathlib's `Int.quotientSpanNatEquivZMod n` identifies `ℤ ⧸ (n)` with `ZMod n`. This file gives
the version for the powers `(p) ^ n` of a principal ideal, the residue rings of the `(p)`-adic
filtration of `ℤ`.

## Main definitions

* `Int.quotientSpanNatPowEquivZMod p n`: `ℤ ⧸ (p) ^ n ≃+* ZMod (p ^ n)`.

## Main results

* `Int.quotientSpanNatPowEquivZMod_mk`: it sends the class of `k` to `(k : ZMod (p ^ n))`.
-/

public section

namespace Int

/-- The residue rings of the `(p)`-adic filtration of `ℤ`: `ℤ ⧸ (p) ^ n ≃+* ZMod (p ^ n)`. -/
noncomputable def quotientSpanNatPowEquivZMod (p n : ℕ) :
    ℤ ⧸ Ideal.span {(p : ℤ)} ^ n ≃+* ZMod (p ^ n) :=
  (Ideal.quotEquivOfEq (by rw [Ideal.span_singleton_pow, Nat.cast_pow])).trans
    (Int.quotientSpanNatEquivZMod (p ^ n))

/-- `Int.quotientSpanNatPowEquivZMod p n` sends the class of `k` to `(k : ZMod (p ^ n))`. Not a
simp lemma: `simp` already rewrites the class to a cast (`eq_intCast`) and pushes the ring
equivalence through it (`map_intCast`). -/
theorem quotientSpanNatPowEquivZMod_mk (p n : ℕ) (k : ℤ) :
    quotientSpanNatPowEquivZMod p n (Ideal.Quotient.mk _ k) = (k : ZMod (p ^ n)) := by
  simp

/-- The inverse of `Int.quotientSpanNatPowEquivZMod p n` sends `(k : ZMod (p ^ n))` to the class
of `k`. Not a simp lemma, for the same reason as `Int.quotientSpanNatPowEquivZMod_mk`. -/
theorem quotientSpanNatPowEquivZMod_symm_intCast (p n : ℕ) (k : ℤ) :
    (quotientSpanNatPowEquivZMod p n).symm (k : ZMod (p ^ n)) = Ideal.Quotient.mk _ k := by
  rw [RingEquiv.symm_apply_eq, quotientSpanNatPowEquivZMod_mk]

end Int
