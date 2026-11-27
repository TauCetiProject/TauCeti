/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.Data.ZMod.QuotientRing

/-!
# Frobenius congruences in localizations at unramified primes

The arithmetic Frobenius and its iterates satisfy congruences modulo the maximal ideal of a
localization at a prime. When the prime is unramified over a rational prime `p`, these are
congruences modulo the principal ideal `(p)`, and hence hold after mapping into any target ring.
-/

public section

namespace AlgHom.IsArithFrobAt

open IsLocalRing

variable {S : Type*} [CommRing S] {Q : Ideal S} [Q.IsPrime]

/-- The local lift of an iterated arithmetic Frobenius agrees with the iterated global
endomorphism on elements of the original ring. -/
@[simp] theorem localize_pow_algebraMap {A : Type*} [CommRing A] [Algebra A S]
    {φ : S →ₐ[A] S} (hφ : φ.IsArithFrobAt Q) (n : ℕ) (x : S) :
    (hφ.localize ^ n) (algebraMap S (Localization.AtPrime Q) x) =
      algebraMap S (Localization.AtPrime Q) ((φ ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih,
      hφ.localize_algebraMap]

/-- At an unramified prime above `p`, an iterate of the localized arithmetic Frobenius acts
by the corresponding power modulo `p`, also after mapping to a target ring. -/
theorem natCast_dvd_localize_pow_sub_pow [Algebra.EssFiniteType ℤ S]
    [Algebra.IsUnramifiedAt ℤ Q] {p : ℕ} [Q.LiesOver (Ideal.span {(p : ℤ)})]
    {φ : S →ₐ[ℤ] S} (hφ : φ.IsArithFrobAt Q) {R : Type*} [CommRing R]
    (f : Localization.AtPrime Q →+* R) (n : ℕ) (x : Localization.AtPrime Q) :
    (p : R) ∣ f ((hφ.localize ^ n) x) - f x ^ p ^ n := by
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hP : P = Q.under ℤ := Q.over_def P
  have : P.IsPrime := hP ▸ Ideal.IsPrime.under ℤ Q
  let := Localization.AtPrime.algebraOfLiesOver P Q
  have : IsScalarTower ℤ (Localization.AtPrime P) (Localization.AtPrime Q) := inferInstance
  let M := maximalIdeal (Localization.AtPrime Q)
  have hmax : M = Ideal.span {(p : Localization.AtPrime Q)} := by
    have h := Algebra.IsUnramifiedAt.map_eq ℤ P Q
    simpa [M, P, Ideal.map_span] using h.symm
  have hcard : Nat.card (ℤ ⧸ M.under ℤ) = p := by
    rw [← Ideal.under_under (B := S), Localization.AtPrime.under_maximalIdeal, ← hP]
    exact (Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv).trans (Nat.card_zmod p)
  have hpow (k : ℕ) : Ideal.Quotient.mk M ((hφ.localize ^ k) x) =
      (Ideal.Quotient.mk M x) ^ p ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgHom.mul_apply, hφ.isArithFrobAt_localize.mk_apply, hcard, ih,
        ← pow_mul, pow_succ]
  have hmem := Ideal.Quotient.eq.mp (by rw [map_pow]; exact hpow n :
    Ideal.Quotient.mk M ((hφ.localize ^ n) x) = Ideal.Quotient.mk M (x ^ p ^ n))
  have hdiv : (p : Localization.AtPrime Q) ∣ (hφ.localize ^ n) x - x ^ p ^ n := by
    rwa [hmax, Ideal.mem_span_singleton] at hmem
  simpa only [map_natCast, map_sub, map_pow] using map_dvd f hdiv

end AlgHom.IsArithFrobAt
