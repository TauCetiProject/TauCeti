/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Positive integers as non-zero-divisors

In a semiring `S` without additive torsion, multiplication by a positive integer `n` is `n • ·`,
which is injective. Hence `n` is regular (`TauCeti.isRegular_natCast_of_ne_zero`), so a
non-zero-divisor of `S` (`TauCeti.natCast_mem_nonZeroDivisors`). This combines Mathlib's
`isRegular_natCast` with `IsRegular.mem_nonZeroDivisors`. In any semiring, if the image of `b` is
regular then so is the image of every divisor of `b` (`TauCeti.isRegular_natCast_of_dvd`); for
instance `i!` is regular when `r!` is, for `i ≤ r`.

In any semiring, multiplication by a positive integer `n` is injective if and only if
multiplication by each prime factor of `n` is
(`TauCeti.isSMulRegular_natCast_iff_forall_mem_primeFactors`). So torsion-freeness at finitely many
primes gives torsion-freeness at every integer built from them.

On a module over a semiring `R`, multiplication by the image `(n : R)` of a natural number is
multiplication by `n`, so the two are injective together (`TauCeti.isSMulRegular_natCast_iff`).
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

/-- Positive integers are regular in a semiring without additive torsion. -/
theorem isRegular_natCast_of_ne_zero {S : Type*} [Semiring S] [IsAddTorsionFree S] {n : ℕ}
    (hn : n ≠ 0) : IsRegular (n : S) :=
  isRegular_natCast.mpr fun a b h ↦ eq_of_nsmul_eq_nsmul_of_addCommute hn (AddCommute.all a b) h

/-- Positive integers are non-zero-divisors of a semiring without additive torsion. -/
theorem natCast_mem_nonZeroDivisors {S : Type*} [Semiring S] [IsAddTorsionFree S] {n : ℕ}
    (hn : n ≠ 0) : (n : S) ∈ S⁰ :=
  (isRegular_natCast_of_ne_zero hn).mem_nonZeroDivisors

/-- If the image of a natural number `b` in a semiring is regular, so is the image of every
divisor `a` of `b`. -/
theorem isRegular_natCast_of_dvd {S : Type*} [Semiring S] {a b : ℕ} (hab : a ∣ b)
    (hb : IsRegular (b : S)) : IsRegular (a : S) := by
  obtain ⟨c, rfl⟩ := hab
  rw [Nat.cast_mul] at hb
  exact (isRegular_mul_and_mul_iff.1 ⟨hb, by rwa [Nat.cast_comm]⟩).1

/-- Multiplication by a positive integer `n` is injective on a semiring if and only if
multiplication by each prime factor of `n` is. -/
theorem isSMulRegular_natCast_iff_forall_mem_primeFactors {R : Type*} [Semiring R] {n : ℕ}
    (hn : n ≠ 0) : IsSMulRegular R (n : R) ↔ ∀ p ∈ n.primeFactors, IsSMulRegular R (p : R) := by
  refine ⟨fun h p hp ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mem_primeFactors hp
    rw [hk, mul_comm, Nat.cast_mul] at h
    exact h.of_mul
  · rw [Nat.prod_primeFactors_pow_factorization hn]
    refine Finset.prod_induction _ (fun m : ℕ ↦ IsSMulRegular R (m : R))
      (fun _ _ ha hb ↦ by rw [Nat.cast_mul]; exact ha.mul hb) (by simp [IsSMulRegular.one])
      fun p hp ↦ ?_
    rw [Nat.cast_pow]
    exact (h p hp).pow _

/-- On an `R`-module, multiplication by `(n : R)` is injective if and only if multiplication by the
natural number `n` is. -/
theorem isSMulRegular_natCast_iff {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {n : ℕ} : IsSMulRegular M (n : R) ↔ IsSMulRegular M n :=
  (Equiv.refl M).isSMulRegular_congr fun m ↦ Nat.cast_smul_eq_nsmul R n m

end TauCeti
