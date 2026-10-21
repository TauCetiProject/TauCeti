/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span

/-!
# Frobenius between quotient rings

Let `p` be a prime and `I, J` ideals of a commutative ring `A` with `p ∈ J` and `x ^ p ∈ J` for
every `x ∈ I`. Then `x ↦ x ^ p` descends to a ring homomorphism `A ⧸ I →+* A ⧸ J`: it is
multiplicative, and additive because `(x + y) ^ p - x ^ p - y ^ p` is a multiple of `p`. Unlike
Mathlib's `frobenius`, the source and target are different rings, and the source need not have
characteristic `p` (only the target, where `p = 0`, does).

The case of interest is `I = (ϖ)` and `J = (ϖ ^ p)` for an element `ϖ` with `ϖ ^ p ∣ p`: the map
`A ⧸ ϖ →+* A ⧸ ϖ ^ p` whose bijectivity on the ring of power-bounded elements is the defining
condition of a perfectoid Tate ring. Its surjectivity says that every element is a `p`-th power
modulo `ϖ ^ p`, and its injectivity that `ϖ ^ p ∣ y ^ p` forces `ϖ ∣ y`.

## Main definitions

* `Ideal.frobeniusQuot`: the ring homomorphism `A ⧸ I →+* A ⧸ J`, `[x] ↦ [x ^ p]`.
* `TauCeti.frobeniusModPow`: the case `A ⧸ ϖ →+* A ⧸ ϖ ^ p`, for `ϖ ^ p ∣ p`.

## Main results

* `TauCeti.surjective_frobeniusModPow_iff`: surjectivity says every element is a `p`-th power
  modulo `ϖ ^ p`.
* `TauCeti.injective_frobeniusModPow_iff`: injectivity says `ϖ ^ p ∣ y ^ p` implies `ϖ ∣ y`.

## References

* P. Scholze, *Étale cohomology of diamonds*, Definition 3.1.
* P. Scholze, J. Weinstein, *Berkeley lectures on p-adic geometry*, Definition 6.1.1.
-/

public section

namespace Ideal

variable {A : Type*} [CommRing A]

/-- **Frobenius between quotients.** For a prime `p` and ideals `I, J` with `p ∈ J` and
`x ^ p ∈ J` for all `x ∈ I`, the ring homomorphism `A ⧸ I →+* A ⧸ J`, `[x] ↦ [x ^ p]`. -/
noncomputable def frobeniusQuot (I J : Ideal A) (p : ℕ) [hp : Fact p.Prime] (hpJ : (p : A) ∈ J)
    (hIJ : ∀ x ∈ I, x ^ p ∈ J) : A ⧸ I →+* A ⧸ J :=
  Quotient.lift I
    { toFun x := Quotient.mk J (x ^ p)
      map_one' := by rw [one_pow, map_one]
      map_mul' x y := by rw [mul_pow, map_mul]
      map_zero' := by rw [zero_pow hp.out.ne_zero, map_zero]
      map_add' x y := by
        obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out x y
        have hmem : (p : A) * x * y * r ∈ J :=
          J.mul_mem_right _ (J.mul_mem_right _ (J.mul_mem_right _ hpJ))
        rw [hr, map_add, Quotient.eq_zero_iff_mem.mpr hmem, add_zero, map_add] }
    fun x hx ↦ Quotient.eq_zero_iff_mem.mpr (hIJ x hx)

@[simp]
theorem frobeniusQuot_mk (I J : Ideal A) (p : ℕ) [Fact p.Prime] (hpJ : (p : A) ∈ J)
    (hIJ : ∀ x ∈ I, x ^ p ∈ J) (x : A) :
    frobeniusQuot I J p hpJ hIJ (Quotient.mk I x) = Quotient.mk J (x ^ p) := (rfl)

end Ideal

namespace TauCeti

open Ideal

variable {A : Type*} [CommRing A]

/-- **Frobenius modulo `ϖ`.** For a prime `p` and `ϖ` with `ϖ ^ p ∣ p`, the ring homomorphism
`A ⧸ ϖ →+* A ⧸ ϖ ^ p`, `[x] ↦ [x ^ p]`; this is `Ideal.frobeniusQuot` for `I = (ϖ)` and
`J = (ϖ ^ p)`. -/
noncomputable def frobeniusModPow (ϖ : A) (p : ℕ) [Fact p.Prime] (h : ϖ ^ p ∣ (p : A)) :
    A ⧸ span {ϖ} →+* A ⧸ span {ϖ ^ p} :=
  frobeniusQuot _ _ p (mem_span_singleton.mpr h) fun _ hx ↦
    span_singleton_pow ϖ p ▸ pow_mem_pow hx p

variable (ϖ : A) (p : ℕ) [Fact p.Prime] (h : ϖ ^ p ∣ (p : A))

@[simp]
theorem frobeniusModPow_mk (x : A) :
    frobeniusModPow ϖ p h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (x ^ p) := (rfl)

/-- **Frobenius modulo `ϖ` is surjective** exactly when every element is a `p`-th power modulo
`ϖ ^ p`. -/
theorem surjective_frobeniusModPow_iff :
    Function.Surjective (frobeniusModPow ϖ p h) ↔ ∀ x : A, ∃ y : A, ϖ ^ p ∣ x - y ^ p := by
  refine ⟨fun hs x ↦ ?_, fun hs ↦ ?_⟩
  · obtain ⟨y, hy⟩ := hs (Ideal.Quotient.mk _ x)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [frobeniusModPow_mk, Ideal.Quotient.eq, mem_span_singleton] at hy
    exact ⟨y, by rw [← neg_sub, dvd_neg]; exact hy⟩
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, hy⟩ := hs x
    refine ⟨Ideal.Quotient.mk _ y, ?_⟩
    rw [frobeniusModPow_mk, Ideal.Quotient.eq, mem_span_singleton, ← neg_sub, dvd_neg]
    exact hy

/-- **Frobenius modulo `ϖ` is injective** exactly when `ϖ ^ p ∣ y ^ p` forces `ϖ ∣ y`. -/
theorem injective_frobeniusModPow_iff :
    Function.Injective (frobeniusModPow ϖ p h) ↔ ∀ y : A, ϖ ^ p ∣ y ^ p → ϖ ∣ y := by
  rw [injective_iff_map_eq_zero]
  refine ⟨fun hi y hy ↦ ?_, fun hi y hy ↦ ?_⟩
  · have := hi (Ideal.Quotient.mk _ y) (by
      rw [frobeniusModPow_mk, Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton]
      exact hy)
    rwa [Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton] at this
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [frobeniusModPow_mk, Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton] at hy
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton]
    exact hi y hy

end TauCeti
