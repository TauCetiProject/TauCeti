/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Order.Filter.Cofinite
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Dirichlet characters agreeing at almost all primes

A Dirichlet character of nonzero level is determined by its values at all but finitely many
primes. At a fixed level this is Dirichlet's theorem on primes in arithmetic progressions: every
unit residue class contains primes larger than any given bound. Across two levels, both characters
are lifted to a common multiple level, where they agree at all primes not dividing that level and
outside the exceptional set; the lifts are then equal, so the two characters have the same
conductor and the same primitive character. In particular, two primitive Dirichlet characters
agreeing at almost all primes have the same level and are equal.

Agreement at almost all primes is written `∀ᶠ p in Filter.cofinite, p.Prime → χ p = ψ p`. A
hypothesis of the form "`χ p = ψ p` for every prime `p ∉ S`" with `S` finite is turned into this
one by `Set.Finite.eventually_cofinite_notMem`.

## Main results

* `DirichletCharacter.eq_of_eventually_apply_prime_eq`: two characters of the same nonzero level
  agreeing at almost all primes are equal.
* `DirichletCharacter.changeLevel_eq_changeLevel_of_eventually_apply_prime_eq`: two characters
  agreeing at almost all primes have the same lift to every common multiple of their levels.
* `DirichletCharacter.conductor_eq_of_eventually_apply_prime_eq` and
  `DirichletCharacter.primitiveCharacter_apply_eq_of_eventually_apply_prime_eq`: such characters
  have the same conductor and the same primitive character.
* `DirichletCharacter.IsPrimitive.level_eq_of_eventually_apply_prime_eq` and
  `DirichletCharacter.IsPrimitive.apply_eq_of_eventually_apply_prime_eq`: two primitive characters
  agreeing at almost all primes have equal levels and agree at every integer.

## References

* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), §6, Lemma 6.2 (ii), whose uniqueness assertion is the
  statement for primitive characters.
-/

public section

open Filter

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {N M : ℕ}

/-- Two Dirichlet characters of the same nonzero level that agree at all but finitely many primes
are equal. -/
theorem eq_of_eventually_apply_prime_eq [NeZero N] {χ ψ : DirichletCharacter R N}
    (h : ∀ᶠ p : ℕ in cofinite, p.Prime → χ p = ψ p) : χ = ψ := by
  rw [Nat.cofinite_eq_atTop] at h
  obtain ⟨B, hB⟩ := eventually_atTop.mp h
  refine MulChar.ext fun a ↦ ?_
  obtain ⟨p, hpB, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod a.isUnit B
  rw [← hpa]
  exact hB p hpB.le hp

/-- Two Dirichlet characters of nonzero levels that agree at all but finitely many primes have the
same lift to every common multiple of their levels. -/
theorem changeLevel_eq_changeLevel_of_eventually_apply_prime_eq {L : ℕ} [NeZero L]
    {χ : DirichletCharacter R N} {ψ : DirichletCharacter R M} (hN : N ∣ L) (hM : M ∣ L)
    (h : ∀ᶠ p : ℕ in cofinite, p.Prime → χ p = ψ p) :
    changeLevel hN χ = changeLevel hM ψ := by
  apply eq_of_eventually_apply_prime_eq
  rw [Nat.cofinite_eq_atTop] at h ⊢
  filter_upwards [h, eventually_gt_atTop L] with p hp hpL hprime
  -- A prime larger than `L` does not divide `L`, so lifting does not change the values at it.
  have hcop : IsCoprime (p : ℤ) (L : ℤ) := Nat.isCoprime_iff_coprime.mpr <|
    (Nat.Prime.coprime_iff_not_dvd hprime).mpr fun hdvd ↦
      (Nat.le_of_dvd (NeZero.pos L) hdvd).not_gt hpL
  have hχ := changeLevel_eq_cast_of_dvd' χ hN hcop
  have hψ := changeLevel_eq_cast_of_dvd' ψ hM hcop
  simp only [Int.cast_natCast] at hχ hψ
  rw [hχ, hψ, hp hprime]

/-- Two Dirichlet characters of nonzero levels that agree at all but finitely many primes have the
same conductor. -/
theorem conductor_eq_of_eventually_apply_prime_eq [NeZero N] [NeZero M]
    {χ : DirichletCharacter R N} {ψ : DirichletCharacter R M}
    (h : ∀ᶠ p : ℕ in cofinite, p.Prime → χ p = ψ p) : χ.conductor = ψ.conductor := by
  rw [← conductor_changeLevel χ (dvd_mul_right N M), ← conductor_changeLevel ψ (dvd_mul_left M N),
    changeLevel_eq_changeLevel_of_eventually_apply_prime_eq _ _ h]

/-- Two Dirichlet characters of nonzero levels that agree at all but finitely many primes have the
same primitive character: its values agree at every integer. -/
theorem primitiveCharacter_apply_eq_of_eventually_apply_prime_eq [Nontrivial R] [NeZero N]
    [NeZero M] {χ : DirichletCharacter R N} {ψ : DirichletCharacter R M}
    (h : ∀ᶠ p : ℕ in cofinite, p.Prime → χ p = ψ p) (a : ℤ) :
    χ.primitiveCharacter a = ψ.primitiveCharacter a := by
  rw [← primitiveCharacter_changeLevel_apply (dvd_mul_right N M),
    ← primitiveCharacter_changeLevel_apply (dvd_mul_left M N),
    changeLevel_eq_changeLevel_of_eventually_apply_prime_eq _ _ h]

namespace IsPrimitive

/-- Two primitive Dirichlet characters of nonzero levels that agree at all but finitely many
primes have the same level. -/
theorem level_eq_of_eventually_apply_prime_eq [NeZero N] [NeZero M]
    {χ : DirichletCharacter R N} {ψ : DirichletCharacter R M} (hχ : χ.IsPrimitive)
    (hψ : ψ.IsPrimitive) (h : ∀ᶠ p : ℕ in cofinite, p.Prime → χ p = ψ p) : N = M := by
  rw [← (isPrimitive_def χ).mp hχ, ← (isPrimitive_def ψ).mp hψ]
  exact conductor_eq_of_eventually_apply_prime_eq h

/-- Two primitive Dirichlet characters of nonzero levels that agree at all but finitely many
primes agree at every integer. Their levels are equal by
`DirichletCharacter.IsPrimitive.level_eq_of_eventually_apply_prime_eq`. -/
theorem apply_eq_of_eventually_apply_prime_eq [NeZero N] [NeZero M]
    {χ : DirichletCharacter R N} {ψ : DirichletCharacter R M} (hχ : χ.IsPrimitive)
    (hψ : ψ.IsPrimitive) (h : ∀ᶠ p : ℕ in cofinite, p.Prime → χ p = ψ p) (a : ℤ) :
    χ a = ψ a := by
  obtain rfl := hχ.level_eq_of_eventually_apply_prime_eq hψ h
  rw [eq_of_eventually_apply_prime_eq h]

end IsPrimitive

end DirichletCharacter
