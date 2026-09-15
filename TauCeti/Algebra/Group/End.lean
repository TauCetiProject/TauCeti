/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Families of endomorphisms indexed by the natural numbers

A family of endomorphisms `F : ℕ → M →* M` whose zeroth member is the identity and which turns
addition of indices into composition is a homomorphism from `(ℕ, +)` into the endomorphism monoid
of `M`. Its exponents therefore multiply: the `m`-th power of `F k` is `F (k * m)`. This file
proves that once, so that no such family needs its own induction.

The two hypotheses are the iteration laws of an iterated endomorphism, so every `p ^ k`-power
Frobenius on a group of points of a group scheme satisfies them, whatever carrier it is built on.

## Main results

* `TauCeti.monoidEnd_pow_eq_of_zero_of_add`: the exponents of such a family multiply under taking
  powers in `Monoid.End M`.
-/

public section

namespace TauCeti

/-- **A family of endomorphisms indexed by the natural numbers, whose zeroth member is the
identity and which carries addition to composition, has multiplicative exponents**: the `m`-th
power of `F k` in the endomorphism monoid of `M` is `F (k * m)`. -/
-- Multiplication in `Monoid.End M` is composition and a bundled endomorphism is definitionally
-- an element of it, so the `show` picks that monoid structure before the power is elaborated.
-- Associativity of the multiplication of `M` is never used: composition of endomorphisms is
-- associative whatever `M` is.
theorem monoidEnd_pow_eq_of_zero_of_add {M : Type*} [MulOne M] (F : ℕ → M →* M)
    (hzero : F 0 = MonoidHom.id M) (hadd : ∀ a b, F (a + b) = (F a).comp (F b)) (k m : ℕ) :
    (show Monoid.End M from F k) ^ m = F (k * m) := by
  induction m with
  | zero => rw [pow_zero, Nat.mul_zero, hzero]; rfl
  | succ m ih => rw [pow_succ, ih, Nat.mul_succ, hadd]; rfl

end TauCeti
