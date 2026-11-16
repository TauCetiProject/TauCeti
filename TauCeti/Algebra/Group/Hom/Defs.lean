/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Multiplicative maps applied entrywise and endomorphism multiplication

A multiplicative map applied entrywise to a scalar multiple `c • v` of a family gives
`f c • (f ∘ v)`. This is the scalar companion of Mathlib's `map_comp_mul` and `map_comp_pow`.
Multiplication in `Monoid.End M` and `AddMonoid.End M` acts on elements by composition.

## Main results

* `TauCeti.map_comp_smul`: `f ∘ (c • v) = f c • (f ∘ v)`.
* `Monoid.End.mul_apply`, `AddMonoid.End.mul_apply`: `(f * g) x = f (g x)`.
-/

public section

namespace Monoid.End

-- `@[simp]` is omitted to avoid colliding with `Monoid.End.coe_mul`.
/-- Multiplication in `Monoid.End M` acts on elements by function composition. -/
@[to_additive mul_apply
/-- Multiplication in `AddMonoid.End M` acts on elements by function composition. -/]
theorem mul_apply {M : Type*} [MulOne M] (f g : Monoid.End M) (x : M) :
    (f * g) x = f (g x) :=
  (rfl)

end Monoid.End

namespace TauCeti

/-- A multiplicative map applied entrywise to `c • v` gives `f c • (f ∘ v)`. -/
@[simp]
theorem map_comp_smul {F M N ι : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    (f : F) (c : M) (v : ι → M) : f ∘ (c • v) = f c • (f ∘ v) :=
  funext fun _ ↦ map_mul f _ _

end TauCeti
