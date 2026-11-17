/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Data.Set.Operations
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Set.Function

/-!
# Multiplicative maps into rings

The element `-1` squares to `1`. A multiplicative map into a ring without zero divisors
therefore sends it to `1` or `-1`. This applies to ordinary ring-valued maps as well as to
unit-valued characters after composing with the coercion homomorphism.

Any multiplicative map `f` from a unital magma into a (possibly non-associative) ring sends `1` to
an idempotent `f 1`, and the complementary idempotent `1 - f 1` annihilates every image `f a` on
both sides (`TauCeti.one_sub_map_one_mul_apply` and `TauCeti.apply_mul_one_sub_map_one`).

A ring homomorphism fixes natural number casts, so it preserves membership statements of the form
`n ^ k * x ∈ A`: if it maps `A` into `B`, then `n ^ k * x ∈ A` implies `n ^ k * f x ∈ B`. This
controls denominators under ring endomorphisms that preserve a subring, as in integrality arguments
for Hazewinkel's functional equation.

## Main results

* `TauCeti.map_neg_one_eq_one_or_eq_neg_one`: the image of `-1` is `1` or `-1`.
* `TauCeti.one_sub_map_one_mul_apply` and `TauCeti.apply_mul_one_sub_map_one`: `1 - f 1`
  annihilates `f a` on the left and right for any multiplicative map `f`.
* `Set.MapsTo.natCast_pow_mul_apply_mem`: if a ring homomorphism `f` maps `A` into `B`, then
  `n ^ k * x ∈ A` implies `n ^ k * f x ∈ B`.
* `Set.MapsTo.ringHom_pow`: if a ring endomorphism `f` maps `A` into itself, so does `f ^ n`.
-/

public section

namespace TauCeti

/-- A multiplicative map into a ring without zero divisors sends `-1` to `1` or `-1`.
Only distributive negation and a multiplicative identity are required in the source; the target
ring need not be associative. -/
theorem map_neg_one_eq_one_or_eq_neg_one {F M R : Type*} [MulOneClass M] [HasDistribNeg M]
    [NonAssocRing R] [NoZeroDivisors R] [FunLike F M R] [MonoidHomClass F M R] (f : F) :
    f (-1) = 1 ∨ f (-1) = -1 :=
  mul_self_eq_one_iff.mp (by rw [← map_mul]; simp)

/-- For any multiplicative map `f` from a unital magma into a (possibly non-associative) ring,
the complementary idempotent `1 - f 1` annihilates `f a` on the left. -/
@[simp]
theorem one_sub_map_one_mul_apply {F M R : Type*} [MulOneClass M] [NonAssocRing R]
    [FunLike F M R] [MulHomClass F M R] (f : F) (a : M) :
    (1 - f 1) * f a = 0 := by
  rw [sub_mul, one_mul, ← map_mul, one_mul, sub_self]

/-- For any multiplicative map `f` from a unital magma into a (possibly non-associative) ring,
the complementary idempotent `1 - f 1` annihilates `f a` on the right. -/
@[simp]
theorem apply_mul_one_sub_map_one {F M R : Type*} [MulOneClass M] [NonAssocRing R]
    [FunLike F M R] [MulHomClass F M R] (f : F) (a : M) :
    f a * (1 - f 1) = 0 := by
  rw [mul_sub, mul_one, ← map_mul, mul_one, sub_self]

end TauCeti

namespace Set.MapsTo

/-- If a ring endomorphism `f` maps `A` into itself, then so does its power `f ^ n`, which is the
`n`-th iterate of `f`. -/
theorem ringHom_pow {R : Type*} [NonAssocSemiring R] {f : R →+* R} {A : Set R}
    (hf : MapsTo f A A) (n : ℕ) : MapsTo (f ^ n) A A := by
  rw [RingHom.coe_pow]
  exact hf.iterate n

/-- If a ring homomorphism `f` maps `A` into `B`, then `n ^ k * x ∈ A` implies `n ^ k * f x ∈ B`
for all natural numbers `n` and `k`, since `f` fixes `n ^ k`. No closure properties of `A` or `B`
are needed. -/
theorem natCast_pow_mul_apply_mem {R S F : Type*} [Semiring R] [Semiring S]
    [FunLike F R S] [RingHomClass F R S] {f : F} {A : Set R} {B : Set S} (hf : MapsTo f A B)
    {n k : ℕ} {x : R} (hx : (n : R) ^ k * x ∈ A) : (n : S) ^ k * f x ∈ B := by
  simpa only [map_mul, map_pow, map_natCast] using hf hx

end Set.MapsTo
