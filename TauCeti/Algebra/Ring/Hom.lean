/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Data.Set.Operations
import Mathlib.Data.Nat.Cast.Basic

/-!
# Multiplicative maps into rings

The element `-1` squares to `1`. A multiplicative map into a ring without zero divisors
therefore sends it to `1` or `-1`. This applies to ordinary ring-valued maps as well as to
unit-valued characters after composing with the coercion homomorphism.

A ring homomorphism fixes natural number casts, so it preserves membership statements of the form
`n * x ∈ A`: if it maps `A` into `B`, then `n * x ∈ A` implies `n * f x ∈ B`. This controls
denominators under ring endomorphisms that preserve a subring, as in integrality arguments for
Hazewinkel's functional equation.

## Main results

* `MonoidHom.map_neg_one_eq_one_or_eq_neg_one`: the image of `-1` is `1` or `-1`.
* `Set.MapsTo.natCast_mul_apply_mem`: if a ring homomorphism `f` maps `A` into `B`, then
  `n * x ∈ A` implies `n * f x ∈ B`.
-/

public section

namespace MonoidHom

/-- A multiplicative map into a ring without zero divisors sends `-1` to `1` or `-1`.
Only distributive negation and a multiplicative identity are required in the source; the target
ring need not be associative. -/
theorem map_neg_one_eq_one_or_eq_neg_one {M R : Type*} [MulOneClass M] [HasDistribNeg M]
    [NonAssocRing R] [NoZeroDivisors R] (f : M →* R) :
    f (-1) = 1 ∨ f (-1) = -1 :=
  mul_self_eq_one_iff.mp (by rw [← map_mul]; simp)

end MonoidHom

namespace Set.MapsTo

/-- If a ring homomorphism `f` maps `A` into `B`, then `n * x ∈ A` implies `n * f x ∈ B` for every
natural number `n`, since `f` fixes `n`. No closure properties of `A` or `B` are needed. -/
theorem natCast_mul_apply_mem {R S F : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    [FunLike F R S] [RingHomClass F R S] {f : F} {A : Set R} {B : Set S} (hf : MapsTo f A B)
    {n : ℕ} {x : R} (hx : (n : R) * x ∈ A) : (n : S) * f x ∈ B := by
  simpa only [map_mul, map_natCast] using hf hx

end Set.MapsTo
