/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Data.Nat.Squarefree
import TauCeti.Data.ZMod.PrincipalUnits
import TauCeti.NumberTheory.DirichletCharacter.Basic

/-!
# The odd part of a primitive quadratic conductor is squarefree

If an odd prime `p` divides `N` at least twice, then every unit modulo `N` that is `1` modulo
`N / p` is a square. Write `p ^ k` for the exact power of `p` in `N`, so `k ≥ 2`. Such a unit
is `1` modulo the prime-to-`p` part of `N`, and modulo `p ^ k` it is `1` modulo `p ^ (k - 1)`,
hence modulo `p`, so it is a square modulo `p ^ k` (`ZMod.isSquare_of_unitsMap_eq_one`). The
Chinese remainder theorem glues the two square roots (`ZMod.isSquare_of_unitsMap_div_eq_one`).

A character whose square is trivial is therefore trivial on the kernel of reduction to `N / p`,
so it factors through `N / p`. For a primitive such character, no odd prime divides the level
twice: the odd part `N / 2 ^ v₂(N)` of a nonzero level is squarefree. With the dyadic bound
`DirichletCharacter.IsPrimitive.factorization_two_eq_zero_or_two_or_three_of_sq_eq_one`, this
gives the shape of a primitive quadratic conductor.

The results are proved for characters of order dividing two with values in any commutative
monoid with zero, and specialised to quadratic characters with values in a commutative ring.

## Main results

* `DirichletCharacter.factorsThrough_div_of_sq_eq_one`: a character of order dividing two at a
  level divisible by `p ^ 2`, for an odd prime `p`, factors through `N / p`.
* `DirichletCharacter.IsPrimitive.factorization_le_one_of_sq_eq_one`: an odd prime divides the
  level of a primitive character of order dividing two at most once.
* `DirichletCharacter.IsPrimitive.squarefree_ordCompl_two_of_sq_eq_one`,
  `DirichletCharacter.IsPrimitive.squarefree_ordCompl_two`: the odd part of the nonzero level of
  a primitive character of order dividing two, in particular of a primitive quadratic character,
  is squarefree.

## References

M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short
character sums*, Annals of Mathematics 191 (2020), §6, proof of Proposition 6.1, p. 372, uses
this shape of a primitive quadratic conductor.
-/

public section

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {N : ℕ}

/-- A character of order dividing two at a nonzero level divisible by `p ^ 2`, for an odd prime
`p`, factors through `N / p`. -/
theorem factorsThrough_div_of_sq_eq_one [NeZero N] (χ : DirichletCharacter R N)
    (hχ : χ ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : p ^ 2 ∣ N) :
    χ.FactorsThrough (N / p) := by
  have hd : N / p ∣ N := Nat.div_dvd_of_dvd ((dvd_pow_self p two_ne_zero).trans hN)
  refine (factorsThrough_iff_ker_unitsMap hd).mpr fun u hu ↦ ?_
  obtain ⟨y, rfl⟩ := ZMod.isSquare_of_unitsMap_div_eq_one hp hp2 hN hu
  apply Units.ext
  rw [MulChar.coe_toUnitHom, Units.val_one, Units.val_mul, map_mul, ← sq]
  simpa only [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply y.isUnit] using
    congrArg (fun ψ : DirichletCharacter R N ↦ ψ y) hχ

/-- **An odd prime divides the level of a primitive character of order dividing two at most
once.** At level zero this uses the zero convention for `Nat.factorization`. -/
theorem IsPrimitive.factorization_le_one_of_sq_eq_one {χ : DirichletCharacter R N}
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    N.factorization p ≤ 1 := by
  by_cases hN : N = 0
  · simp [hN]
  let : NeZero N := ⟨hN⟩
  by_contra h
  have hp2N : p ^ 2 ∣ N := (hp.pow_dvd_iff_le_factorization hN).mpr (by omega)
  have hlt := (factorsThrough_div_iff_factorization_conductor_lt hp
    ((dvd_pow_self p two_ne_zero).trans hp2N) χ).mp
    (χ.factorsThrough_div_of_sq_eq_one hsq hp hp2 hp2N)
  rw [(isPrimitive_def χ).mp hχ] at hlt
  exact lt_irrefl _ hlt

/-- **The odd part of a primitive conductor of order dividing two is squarefree.** For a
primitive character of order dividing two at a nonzero level `N`, the odd part
`N / 2 ^ v₂(N)` of `N` is squarefree. -/
theorem IsPrimitive.squarefree_ordCompl_two_of_sq_eq_one [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) :
    Squarefree (ordCompl[2] N) := by
  rw [Nat.squarefree_iff_factorization_le_one (Nat.ordCompl_pos 2 (NeZero.ne N)).ne',
    Nat.factorization_ordCompl]
  intro p
  by_cases hp2 : p = 2
  · simp [hp2]
  rw [Finsupp.erase_ne hp2]
  by_cases hp : p.Prime
  · exact hχ.factorization_le_one_of_sq_eq_one hsq hp hp2
  · simp [Nat.factorization_eq_zero_of_not_prime N hp]

/-- **The odd part of a primitive quadratic conductor is squarefree.** For a primitive quadratic
character `χ` of nonzero level `N` with values in a commutative ring, the odd part
`N / 2 ^ v₂(N)` of `N` is squarefree. -/
theorem IsPrimitive.squarefree_ordCompl_two {S : Type*} [CommRing S] [NeZero N]
    {χ : DirichletCharacter S N} (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic) :
    Squarefree (ordCompl[2] N) :=
  hχ.squarefree_ordCompl_two_of_sq_eq_one hquad.sq_eq_one

end DirichletCharacter
