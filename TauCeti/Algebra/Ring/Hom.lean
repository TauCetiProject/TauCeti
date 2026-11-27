/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Tactic.Abel
import TauCeti.Algebra.Ring.Parity

/-!
# Multiplicative maps, ring homomorphisms, and ring equivalences

The element `-1` squares to `1`. A multiplicative map into a ring without zero divisors
therefore sends it to `1` or `-1`. This applies to ordinary ring-valued maps as well as to
unit-valued characters after composing with the coercion homomorphism.
Similarly, a ring homomorphism sends a square root of an integer `D` to a square root of `D`, and
a square root of `-1` to a square root of `-1`.

Any multiplicative map `f` from a unital magma into a (possibly non-associative) ring sends `1` to
an idempotent `f 1`, and the complementary idempotent `1 - f 1` annihilates every image `f a` on
both sides (`TauCeti.one_sub_map_one_mul_apply` and `TauCeti.apply_mul_one_sub_map_one`).
In a monoid-to-ring map, `a ↦ f a + (1 - f 1)` is a monoid homomorphism (`MulHom.unitize`): it
acts as `f` on the range of `f 1` and as the identity on the range of `1 - f 1`. This is how a
nonunital representation of a unital algebra still lets its invertible elements act by invertible
operators.

A ring homomorphism fixes natural number casts, so it preserves membership statements of the form
`n ^ k * x ∈ A`: if it maps `A` into `B`, then `n ^ k * x ∈ A` implies `n ^ k * f x ∈ B`. This
controls denominators under ring endomorphisms that preserve a subring, as in integrality arguments
for Hazewinkel's functional equation.

A ring equivalence `e : R ≃+* S` transports polynomial equations in both directions by applying
`e` and `e.symm`. In particular, it preserves solvability of the binary quadratic norm equation
`b = x² - a y²`, which transports Hilbert symbols and local and global quadratic norm equations
along field and completion isomorphisms.

## Main results

* `TauCeti.map_neg_one_eq_one_or_eq_neg_one`: the image of `-1` is `1` or `-1`.
* `TauCeti.sq_map_of_sq_eq_intCast`: the image of a square root of an integer `D` is a square
  root of `D`.
* `TauCeti.mul_self_map_of_mul_self_eq_neg_one`: the image of a square root of `-1` is a square
  root of `-1`.
* `TauCeti.one_sub_map_one_mul_apply` and `TauCeti.apply_mul_one_sub_map_one`: `1 - f 1`
  annihilates `f a` on the left and right for any multiplicative map `f`.
* `TauCeti.exists_add_neg_one_pow_mul_apply_eq`: showing from a trace-one element for
  `t ↦ t + σ t` that every element `s` with `σ s = (-1) ^ k * s` has a preimage under
  `t ↦ t + (-1) ^ k * σ t`.
* `TauCeti.exists_ne_zero_add_neg_one_pow_mul_apply_eq_zero`: producing a nonzero kernel element
  of `t ↦ t + (-1) ^ k * σ t` from a nonzero kernel element of `d ↦ d + σ d` when `k` is even
  (and unconditionally via `1` when `k` is odd).
* `MulHom.unitize`: the unitization `a ↦ f a + (1 - f 1)` of a multiplicative map from a monoid
  to a ring, which is a monoid homomorphism.
* `Set.MapsTo.natCast_pow_mul_apply_mem`: if a ring homomorphism `f` maps `A` into `B`, then
  `n ^ k * x ∈ A` implies `n ^ k * f x ∈ B`.
* `Set.MapsTo.ringHom_pow`: if a ring endomorphism `f` maps `A` into itself, so does `f ^ n`.
* `RingEquiv.exists_eq_sq_sub_mul_sq_map_iff`: a ring equivalence preserves solvability of
  `b = x² - a y²`.
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

/-- A ring homomorphism sends a square root of an integer `D` to a square root of `D`. -/
theorem sq_map_of_sq_eq_intCast {R S F : Type*} [Ring R] [Ring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) {D : ℤ} {δ : R} (hδ : δ ^ 2 = (D : R)) : f δ ^ 2 = (D : S) := by
  rw [← map_pow, hδ, map_intCast]

/-- A ring homomorphism sends a square root of `-1` to a square root of `-1`. -/
theorem mul_self_map_of_mul_self_eq_neg_one {R S F : Type*} [NonAssocRing R] [NonAssocRing S]
    [FunLike F R S] [RingHomClass F R S] (f : F) {i : R} (hi : i * i = -1) : f i * f i = -1 := by
  rw [← map_mul, hi, map_neg, map_one]

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

/-- Existence of a trace-one element `b + σ b = 1` implies that every element `s` with
`σ s = (-1) ^ k * s` has a preimage under the signed trace `t ↦ t + (-1) ^ k * σ t` for every
`k : ℕ` (for an arbitrary ring endomorphism `σ`, the map need not land in
`{s | σ s = (-1) ^ k * s}`).

Adapted from `TauCeti.FiniteField.exists_add_neg_one_pow_mul_pow_eq` in
`TauCeti.FieldTheory.Finite.PowAddSelf` to an arbitrary ring endomorphism. -/
theorem exists_add_neg_one_pow_mul_apply_eq {R : Type*} [Ring R] {σ : R →+* R}
    (hb : ∃ b : R, b + σ b = 1) (k : ℕ) {s : R}
    (hs : σ s = (-1 : R) ^ k * s) : ∃ t : R, t + (-1 : R) ^ k * σ t = s := by
  obtain ⟨b, hb⟩ := hb
  refine ⟨s * b, ?_⟩
  rw [map_mul, hs, ← mul_assoc ((-1 : R) ^ k), neg_one_pow_mul_neg_one_pow_mul,
    ← mul_add, hb, mul_one]

/-- Existence of a nonzero `d` with `d + σ d = 0` when `k` is even yields a nonzero solution of
`d + (-1) ^ k * σ d = 0` for every `k : ℕ` (for odd `k`, `d = 1` works unconditionally).

Adapted from `TauCeti.FiniteField.exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero` in
`TauCeti.FieldTheory.Finite.PowAddSelf` to an arbitrary nontrivial ring. -/
theorem exists_ne_zero_add_neg_one_pow_mul_apply_eq_zero {R : Type*} [Ring R] [Nontrivial R]
    {σ : R →+* R} {k : ℕ} (hadm : Even k → ∃ d ≠ (0 : R), d + σ d = 0) :
    ∃ d ≠ (0 : R), d + (-1 : R) ^ k * σ d = 0 := by
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨d, hd0, hd⟩ := hadm hk
    exact ⟨d, hd0, by rw [hk.neg_one_pow, one_mul, hd]⟩
  · exact ⟨1, one_ne_zero, by rw [hk.neg_one_pow, map_one, neg_one_mul, add_neg_cancel]⟩

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

namespace MulHom

variable {M R : Type*} [MulOneClass M] [NonAssocRing R]

/-- The **unitization** `a ↦ f a + (1 - f 1)` of a multiplicative map `f` from a monoid to a
ring: it agrees with `f` on the range of the idempotent `f 1` and is the identity on the range of
`1 - f 1`, so it is multiplicative and unital even when `f` does not preserve `1`. -/
def unitize (f : M →ₙ* R) : M →* R where
  toFun a := f a + (1 - f 1)
  map_one' := add_sub_cancel _ _
  map_mul' a b := by
    have h₁ : f a * f 1 = f a := by rw [← map_mul, mul_one]
    have h₂ : f 1 * f b = f b := by rw [← map_mul, one_mul]
    have h₃ : f 1 * f 1 = f 1 := by rw [← map_mul, mul_one]
    simp only [map_mul, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, h₁, h₂, h₃]
    abel

/-- The unitization of `f` sends `a` to `f a + (1 - f 1)`. -/
@[simp]
theorem unitize_apply (f : M →ₙ* R) (a : M) : f.unitize a = f a + (1 - f 1) :=
  (rfl)

end MulHom

namespace RingEquiv

-- Not `@[simp]`: the left-hand side is headed by `Exists`, which would index under a wildcard key.
/-- A ring isomorphism preserves solvability of the binary quadratic norm equation
`b = x² - a y²`. -/
theorem exists_eq_sq_sub_mul_sq_map_iff {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S)
    (a b : R) :
    (∃ x y : S, e b = x ^ 2 - e a * y ^ 2) ↔ ∃ x y : R, b = x ^ 2 - a * y ^ 2 := by
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨e.symm x, e.symm y, e.injective (by simpa using h)⟩
  · rintro ⟨x, y, h⟩
    exact ⟨e x, e y, by simp [h]⟩

end RingEquiv
