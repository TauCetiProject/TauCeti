/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Nat.Cast.Basic
import TauCeti.Algebra.Polynomial.Roots

/-!
# Multiplicative maps, ring homomorphisms, and ring equivalences

The element `-1` squares to `1`. A multiplicative map into a ring without zero divisors
therefore sends it to `1` or `-1`. This applies to ordinary ring-valued maps as well as to
unit-valued characters after composing with the coercion homomorphism.

A ring homomorphism fixes natural number casts, so it preserves membership statements of the form
`n ^ k * x ∈ A`: if it maps `A` into `B`, then `n ^ k * x ∈ A` implies `n ^ k * f x ∈ B`. This
controls denominators under ring endomorphisms that preserve a subring, as in integrality arguments
for Hazewinkel's functional equation.

A ring equivalence `e : R ≃+* S` transports polynomial equations in both directions by applying
`e` and `e.symm`. In particular, it preserves solvability of the binary quadratic norm equation
`b = x² - a y²`, which transports Hilbert symbols and local and global quadratic norm equations
along field and completion isomorphisms.

On an infinite commutative ring `R`, no two ring homomorphisms `g, g' : R →+* S` into a nontrivial
commutative ring can satisfy a nontrivial identity `g x ^ d * g' x ^ n = 1` on all nonzero elements
(`RingHom.not_forall_map_pow_mul_map_pow_eq_one`).

## Main results

* `TauCeti.map_neg_one_eq_one_or_eq_neg_one`: the image of `-1` is `1` or `-1`.
* `Set.MapsTo.natCast_pow_mul_apply_mem`: if a ring homomorphism `f` maps `A` into `B`, then
  `n ^ k * x ∈ A` implies `n ^ k * f x ∈ B`.
* `Set.MapsTo.ringHom_pow`: if a ring endomorphism `f` maps `A` into itself, so does `f ^ n`.
* `RingEquiv.exists_eq_sq_sub_mul_sq_map_iff`: a ring equivalence preserves solvability of
  `b = x² - a y²`.
* `RingHom.not_forall_map_pow_mul_map_pow_eq_one`: no two ring homomorphisms out of an infinite
  commutative ring satisfy `g x ^ d * g' x ^ n = 1` on all nonzero elements with `d ≠ 0 ∨ n ≠ 0`.
* `RingHom.not_forall_map_mul_map_eq_one` and `RingHom.not_forall_map_pow_mul_pow_eq_one`: the
  pointwise-inverse and endomorphism specializations.
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

namespace RingHom

open Polynomial in
private theorem not_forall_map_pow_mul_map_pow_eq_one_of_ne_zero {R S : Type*} [CommRing R]
    [Infinite R] [CommRing S] [Nontrivial S] (g g' : R →+* S) {d n : ℕ} (hd : d ≠ 0) :
    ¬ ∀ x : R, x ≠ 0 → g x ^ d * g' x ^ n = 1 := fun h => by
  have : Nontrivial R := Infinite.instNontrivial R
  have hginj : Function.Injective g := (injective_iff_map_eq_zero g).mpr fun x hx => by_contra
    fun hx0 => (zero_ne_one (α := S)) (by simpa [hx, zero_pow hd] using h x hx0)
  have : NoZeroDivisors R := ⟨fun {a b} hab => by_contra fun hne => by
    rw [not_or] at hne
    have h1 : (g a ^ d * g' a ^ n) * (g b ^ d * g' b ^ n) = 1 := by
      rw [h a hne.1, h b hne.2, mul_one]
    rw [mul_mul_mul_comm, ← mul_pow, ← map_mul, hab, map_zero, zero_pow hd, zero_mul] at h1
    exact zero_ne_one h1⟩
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  rcases eq_or_ne n 0 with rfl | hn
  · exact TauCeti.not_forall_pow_eq_one hd fun x hx => hginj (by simpa [map_pow] using h x hx)
  let Q : R[X] := (X ^ n + 1) ^ d * (X ^ d + 1) ^ n - X ^ (d * n)
  let P : R[X] := X * (X ^ n + 1) * Q
  refine mul_ne_zero (mul_ne_zero X_ne_zero fun h1 => by simpa [hn] using congrArg (eval 0) h1)
    (fun h2 => by simpa [Q, hd, hn, Nat.mul_ne_zero hd hn] using congrArg (eval 0) h2)
    (Polynomial.zero_of_eval_zero P fun c => ?_)
  simp only [P, Q, eval_mul, eval_sub, eval_pow, eval_add, eval_X, eval_one]
  by_cases hc0 : c = 0; · simp [hc0]
  by_cases hcn1 : c ^ n + 1 = 0; · simp [hcn1]
  have hlink : g c ^ d * g' (c ^ n + 1) = g (c ^ d + 1) := by
    rw [map_add, map_pow, map_one, mul_add, mul_one, h c hc0, map_add, map_pow, map_one, add_comm]
  have hgeq : g ((c ^ n + 1) ^ d * (c ^ d + 1) ^ n) = g (c ^ (d * n)) := by
    rw [map_mul, map_pow, map_pow, ← hlink, mul_pow]
    calc g (c ^ n + 1) ^ d * ((g c ^ d) ^ n * g' (c ^ n + 1) ^ n)
      _ = (g c ^ d) ^ n * (g (c ^ n + 1) ^ d * g' (c ^ n + 1) ^ n) := by ring
      _ = g (c ^ (d * n)) := by rw [h _ hcn1, mul_one, ← pow_mul, map_pow]
  rw [sub_eq_zero.mpr (hginj hgeq), mul_zero]

/-- **No two ring homomorphisms out of an infinite commutative ring satisfy a nontrivial
negative-exponent power law on nonzero elements.** -/
theorem not_forall_map_pow_mul_map_pow_eq_one {R S : Type*} [CommRing R] [Infinite R]
    [CommRing S] [Nontrivial S] (g g' : R →+* S) {d n : ℕ} (hdn : d ≠ 0 ∨ n ≠ 0) :
    ¬ ∀ x : R, x ≠ 0 → g x ^ d * g' x ^ n = 1 :=
  hdn.elim (not_forall_map_pow_mul_map_pow_eq_one_of_ne_zero g g') fun hn h =>
    not_forall_map_pow_mul_map_pow_eq_one_of_ne_zero g' g hn fun x hx => by
      rw [mul_comm]; exact h x hx

/-- **No two ring homomorphisms out of an infinite commutative ring are pointwisely inverse on
nonzero elements.** -/
theorem not_forall_map_mul_map_eq_one {R S : Type*} [CommRing R] [Infinite R]
    [CommRing S] [Nontrivial S] (g g' : R →+* S) : ¬ ∀ x : R, x ≠ 0 → g x * g' x = 1 := by
  simpa only [pow_one] using
    not_forall_map_pow_mul_map_pow_eq_one g g' (d := 1) (n := 1) (.inl one_ne_zero)

/-- **No ring endomorphism of an infinite commutative ring satisfies a nontrivial negative-exponent
power law on nonzero elements.** -/
theorem not_forall_map_pow_mul_pow_eq_one {R : Type*} [CommRing R] [Infinite R] (g : R →+* R)
    {d n : ℕ} (hdn : d ≠ 0 ∨ n ≠ 0) : ¬ ∀ x : R, x ≠ 0 → g x ^ d * x ^ n = 1 :=
  have : Nontrivial R := Infinite.instNontrivial R
  not_forall_map_pow_mul_map_pow_eq_one g (RingHom.id R) hdn

end RingHom
