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

* `DirichletCharacter.eq_iff_eventually_apply_prime_eq`: two characters of the same nonzero level
  are equal if and only if they agree at almost all primes.
* `DirichletCharacter.changeLevel_eq_changeLevel_iff_eventually_apply_prime_eq`: two characters
  have the same lift to a common nonzero multiple of their levels if and only if they agree at
  almost all primes.
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

/-- Two Dirichlet characters of the same nonzero level are equal if and only if they agree at all
but finitely many primes. -/
theorem eq_iff_eventually_apply_prime_eq [NeZero N] {χ ψ : DirichletCharacter R N} :
    χ = ψ ↔ ∀ᶠ p : ℕ in cofinite, p.Prime → χ p = ψ p := by
  refine ⟨fun h ↦ .of_forall fun _ _ ↦ h ▸ rfl, fun h ↦ MulChar.ext fun a ↦ ?_⟩
  -- By Dirichlet's theorem, some prime outside the exceptional set reduces to `a`.
  obtain ⟨p, ⟨hp, hpa⟩, hχψ⟩ :=
    ((Nat.infinite_setOfPred_prime_and_eq_mod a.isUnit).frequently_cofinite.and_eventually h).exists
  rw [← hpa]
  exact hχψ hp

/-- Two Dirichlet characters of nonzero levels have the same lift to a common nonzero multiple of
their levels if and only if they agree at all but finitely many primes. -/
theorem changeLevel_eq_changeLevel_iff_eventually_apply_prime_eq {L : ℕ} [NeZero L]
    {χ : DirichletCharacter R N} {ψ : DirichletCharacter R M} (hN : N ∣ L) (hM : M ∣ L) :
    changeLevel hN χ = changeLevel hM ψ ↔ ∀ᶠ p : ℕ in cofinite, p.Prime → χ p = ψ p := by
  -- A prime larger than `L` does not divide `L`, so lifting does not change the values at it.
  have hlift : ∀ᶠ p : ℕ in cofinite, p.Prime →
      changeLevel hN χ p = χ p ∧ changeLevel hM ψ p = ψ p := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_gt_atTop L] with p hpL hp
    have hcop : IsCoprime (p : ℤ) L := Nat.isCoprime_iff_coprime.mpr <|
      hp.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt (NeZero.pos L) hpL
    exact ⟨mod_cast changeLevel_eq_cast_of_dvd' χ hN hcop,
      mod_cast changeLevel_eq_cast_of_dvd' ψ hM hcop⟩
  rw [eq_iff_eventually_apply_prime_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> filter_upwards [hlift, h] with p hp hχψ hprime
  · rw [← (hp hprime).1, ← (hp hprime).2, hχψ hprime]
  · rw [(hp hprime).1, (hp hprime).2, hχψ hprime]

/-- Two Dirichlet characters of nonzero levels that agree at all but finitely many primes have the
same conductor. -/
theorem conductor_eq_of_eventually_apply_prime_eq [NeZero N] [NeZero M]
    {χ : DirichletCharacter R N} {ψ : DirichletCharacter R M}
    (h : ∀ᶠ p : ℕ in cofinite, p.Prime → χ p = ψ p) : χ.conductor = ψ.conductor := by
  rw [← conductor_changeLevel χ (dvd_mul_right N M), ← conductor_changeLevel ψ (dvd_mul_left M N),
    (changeLevel_eq_changeLevel_iff_eventually_apply_prime_eq _ _).mpr h]

/-- Two Dirichlet characters of nonzero levels that agree at all but finitely many primes have the
same primitive character: its values agree at every integer. -/
theorem primitiveCharacter_apply_eq_of_eventually_apply_prime_eq [Nontrivial R] [NeZero N]
    [NeZero M] {χ : DirichletCharacter R N} {ψ : DirichletCharacter R M}
    (h : ∀ᶠ p : ℕ in cofinite, p.Prime → χ p = ψ p) (a : ℤ) :
    χ.primitiveCharacter a = ψ.primitiveCharacter a := by
  rw [← primitiveCharacter_changeLevel_apply (dvd_mul_right N M),
    ← primitiveCharacter_changeLevel_apply (dvd_mul_left M N),
    (changeLevel_eq_changeLevel_iff_eventually_apply_prime_eq _ _).mpr h]

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
  rw [eq_iff_eventually_apply_prime_eq.mpr h]

end IsPrimitive

end DirichletCharacter
