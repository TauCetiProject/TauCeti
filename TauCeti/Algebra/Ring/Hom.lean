/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Tactic.Abel

/-!
# Multiplicative maps, ring homomorphisms, and ring equivalences

The element `-1` squares to `1`. A multiplicative map into a ring without zero divisors
therefore sends it to `1` or `-1`. This applies to ordinary ring-valued maps as well as to
unit-valued characters after composing with the coercion homomorphism.

A multiplicative map `f` from a monoid to a ring need not send `1` to `1`, but `f 1` is then an
idempotent, and `a ↦ f a + (1 - f 1)` is a monoid homomorphism: it acts as `f` on the range of
`f 1` and as the identity on the range of `1 - f 1`. This is how a nonunital representation of a
unital algebra still lets its invertible elements act by invertible operators.

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
