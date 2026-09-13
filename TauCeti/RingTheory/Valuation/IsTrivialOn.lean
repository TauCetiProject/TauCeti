/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Restricting a valuation along an algebra map preserves triviality on the base

A valuation trivial on a base ring stays trivial on that base when restricted along a map of
algebras over it. The restriction changes where the valuation is evaluated but not what it does to
constants, because an algebra map fixes them.

## Main results

* `Valuation.IsTrivialOn.comap`: **restriction preserves triviality on the base**, for a valuation
  on any algebra restricted along any algebra map over that base.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], for valuations, their restriction along a ring map,
  and triviality on a base ring.
-/

public section

namespace Valuation

variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]

/-- **Restricting a valuation along an algebra map preserves triviality on the base.** An algebra
map fixes the base, so the restricted valuation takes the same values on constants. -/
instance IsTrivialOn.comap {A B C : Type*} [CommSemiring A] [Ring B] [Ring C] [Algebra A B]
    [Algebra A C] (v : Valuation C Γ₀) (f : B →ₐ[A] C) [v.IsTrivialOn A] :
    (v.comap f.toRingHom).IsTrivialOn A where
  eq_one a ha := by simpa using Valuation.IsTrivialOn.eq_one (v := v) a ha

end Valuation

end
