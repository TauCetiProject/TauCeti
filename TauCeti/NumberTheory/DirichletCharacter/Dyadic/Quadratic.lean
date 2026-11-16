/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Basic
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.MulChar.Basic
import TauCeti.Data.ZMod.UnitSquare

/-!
# The dyadic part of a quadratic conductor

A character whose square is trivial descends from a level divisible by sixteen to half
that level: every unit in the reduction kernel is a square. Thus a primitive quadratic
character has dyadic conductor exponent at most three. Together with the exclusion of
exponent one, its dyadic exponent is zero, two or three.

Likewise such a character at level `2 ^ k` with `k ≥ 3` factors through `8`
(`DirichletCharacter.factorsThrough_eight_of_sq_eq_one`), since every unit congruent to `1`
modulo `8` is a square.

The descent and upper bound are proved for characters of order dividing two with values
in any commutative monoid with zero. In particular they apply to quadratic characters
with values in a commutative ring, without assumptions on its characteristic.

## References

M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short
character sums*, Annals of Mathematics 191 (2020), §7, Lemma 7.3 and its proof, p. 375,
uses this restriction in the shape of a primitive quadratic conductor.
-/

public section

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {N : ℕ}

/-- A character of order dividing two at a nonzero level divisible by sixteen factors
through half its level. -/
theorem factorsThrough_half_of_sq_eq_one [NeZero N] (χ : DirichletCharacter R N)
    (hχ : χ ^ 2 = 1) (hN : 16 ∣ N) : χ.FactorsThrough (N / 2) := by
  have hd : N / 2 ∣ N := Nat.div_dvd_of_dvd ((by decide : 2 ∣ 16).trans hN)
  refine (factorsThrough_iff_ker_unitsMap hd).mpr fun u hu ↦ ?_
  have hcast : ((u : ZMod N).cast : ZMod (N / 2)) = 1 := by
    simpa only [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, Units.val_one] using hu
  obtain ⟨y, hy⟩ := (ZMod.isSquare_of_cast_half_eq_one (u : ZMod N) hN hcast).exists_sq
  have hyunit : IsUnit y := (isUnit_pow_iff two_ne_zero).mp (hy ▸ u.isUnit)
  apply Units.ext
  rw [MulChar.coe_toUnitHom, Units.val_one, hy]
  exact MulChar.apply_sq_eq_one_of_sq_eq_one hχ hyunit

/-- A character of order dividing two at level `2 ^ k`, `k ≥ 3`, factors through `8`: every
unit congruent to `1` modulo `8` is a square. -/
theorem factorsThrough_eight_of_sq_eq_one {k : ℕ} (hk : 3 ≤ k) (χ : DirichletCharacter R (2 ^ k))
    (hχ : χ ^ 2 = 1) : χ.FactorsThrough 8 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h8 : 8 ∣ 2 ^ (k + 1) := pow_dvd_pow 2 hk
  refine (factorsThrough_iff_ker_unitsMap h8).mpr fun u hu ↦ ?_
  have hcast : ((u : ZMod (2 ^ (k + 1))).cast : ZMod 8) = 1 := by
    simpa only [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, Units.val_one] using hu
  -- The representative of `u` is `1 + 8 a`, the square of a unit.
  set x := (u : ZMod (2 ^ (k + 1))).val with hx
  have hmod : x % 8 = 1 := by
    have h : (x : ZMod 8) = ((1 : ℕ) : ZMod 8) := by
      rw [hx, ← ZMod.cast_eq_val, hcast, Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff' x 1 8).mp h
  obtain ⟨q, hq⟩ : ∃ q, x = 8 * q + 1 := ⟨x / 8, by omega⟩
  obtain ⟨y, hy⟩ := ZMod.exists_unit_sq_eq_one_add_eight_mul (q : ZMod (2 ^ (k + 1)))
  have hu' : (u : ZMod (2 ^ (k + 1))) = (y : ZMod (2 ^ (k + 1))) ^ 2 := by
    rw [hy, ← ZMod.natCast_zmod_val (u : ZMod (2 ^ (k + 1))), ← hx, hq]
    push_cast
    ring
  apply Units.ext
  rw [MulChar.coe_toUnitHom, Units.val_one, hu']
  exact MulChar.apply_sq_eq_one_of_sq_eq_one hχ y.isUnit

/-- The dyadic exponent of a primitive character of order dividing two is at most three.
At level zero this uses the zero convention for `Nat.factorization`. -/
theorem IsPrimitive.factorization_two_le_three_of_sq_eq_one {χ : DirichletCharacter R N}
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) : N.factorization 2 ≤ 3 := by
  by_cases hN : N = 0
  · simp [hN]
  let : NeZero N := ⟨hN⟩
  by_contra h
  have h16 : 16 ∣ N := by
    exact (Nat.prime_two.pow_dvd_iff_le_factorization (k := 4) hN).mpr (by omega)
  have hlt := (factorsThrough_div_iff_factorization_conductor_lt Nat.prime_two
    ((by decide : 2 ∣ 16).trans h16) χ).mp (χ.factorsThrough_half_of_sq_eq_one hsq h16)
  rw [(isPrimitive_def χ).mp hχ] at hlt
  exact (lt_irrefl _ hlt)

/-- The only dyadic exponents of a primitive character of order dividing two are zero,
two and three. At level zero this uses the zero convention for `Nat.factorization`. -/
theorem IsPrimitive.factorization_two_eq_zero_or_two_or_three_of_sq_eq_one
    {χ : DirichletCharacter R N} (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) :
    N.factorization 2 = 0 ∨ N.factorization 2 = 2 ∨ N.factorization 2 = 3 := by
  have := hχ.factorization_two_le_three_of_sq_eq_one hsq
  have := hχ.factorization_two_ne_one
  omega

/-- A primitive quadratic character has dyadic exponent at most three. -/
theorem IsPrimitive.factorization_two_le_three {S : Type*} [CommRing S]
    {χ : DirichletCharacter S N} (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic) :
    N.factorization 2 ≤ 3 :=
  hχ.factorization_two_le_three_of_sq_eq_one hquad.sq_eq_one

/-- The only dyadic exponents of a primitive quadratic character are zero, two and three. -/
theorem IsPrimitive.factorization_two_eq_zero_or_two_or_three {S : Type*} [CommRing S]
    {χ : DirichletCharacter S N} (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic) :
    N.factorization 2 = 0 ∨ N.factorization 2 = 2 ∨ N.factorization 2 = 3 :=
  hχ.factorization_two_eq_zero_or_two_or_three_of_sq_eq_one hquad.sq_eq_one

end DirichletCharacter
