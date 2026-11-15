/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Data.Nat.Totient

/-!
# The missing dyadic conductor exponent

Every Dirichlet character modulo twice an odd number factors through that odd number.
Consequently a primitive character's level cannot have 2-adic valuation one. This is the
first restriction on the dyadic part of a quadratic conductor, but does not require the
character to be quadratic or its values to lie in a ring.

The factorization statement is `DirichletCharacter.factorsThrough_of_odd_half`;
`DirichletCharacter.IsPrimitive.factorization_two_ne_one` gives the valuation restriction.
Here valuation means `Nat.factorization`, whose value at the zero level is zero.

## References

M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short
character sums*, Annals of Mathematics 191 (2020), §7, proof of Lemma 7.3, p. 375,
uses this restriction in the classification of quadratic conductors.
-/

public section

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R]

/-- A character modulo twice an odd number is induced from the odd modulus. -/
theorem factorsThrough_of_odd_half {m : ℕ} (χ : DirichletCharacter R (2 * m))
    (hm : _root_.Odd m) :
    χ.FactorsThrough m := by
  have hm0 : m ≠ 0 := by have := Nat.odd_iff.mp hm; omega
  let : NeZero m := ⟨hm0⟩
  let : NeZero (2 * m) := ⟨mul_ne_zero (by decide) hm0⟩
  -- Reduction is surjective, and doubling an odd modulus does not change its totient.
  have hinj : Function.Injective (ZMod.unitsMap (Nat.dvd_mul_left m 2)) :=
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨ZMod.unitsMap_surjective _, by
        simpa only [ZMod.card_units_eq_totient] using Nat.totient_two_mul_of_odd hm⟩).injective
  refine (factorsThrough_iff_ker_unitsMap (Nat.dvd_mul_left m 2)).mpr ?_
  intro u hu
  have hu1 : u = 1 := hinj (by simpa using MonoidHom.mem_ker.mp hu)
  simp [hu1]

/-- There is no primitive Dirichlet character modulo twice an odd number. -/
@[simp]
theorem not_isPrimitive_two_mul {m : ℕ} (χ : DirichletCharacter R (2 * m))
    (hm : _root_.Odd m) : ¬χ.IsPrimitive := by
  have hm0 : m ≠ 0 := by have := Nat.odd_iff.mp hm; omega
  let : NeZero (2 * m) := ⟨mul_ne_zero (by decide) hm0⟩
  intro hχ
  have hd : χ.conductor ∣ m :=
    conductor_dvd_of_mem_conductorSet χ (factorsThrough_of_odd_half χ hm)
  rw [hχ] at hd
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd
  omega

/-- The 2-adic valuation of the level of a primitive Dirichlet character is not one.
This also holds at level zero, with `Nat.factorization`'s zero convention. -/
theorem IsPrimitive.factorization_two_ne_one {N : ℕ} {χ : DirichletCharacter R N}
    (hχ : χ.IsPrimitive) : N.factorization 2 ≠ 1 := by
  intro h
  have hN : N ≠ 0 := by rintro rfl; simp at h
  have hodd : _root_.Odd (N / 2) := by
    have hnot := Nat.not_dvd_ordCompl Nat.prime_two hN
    rw [h, pow_one] at hnot
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hnot)
  have hlevel : 2 * (N / 2) = N := by
    simpa only [h, pow_one] using Nat.ordProj_mul_ordCompl_eq_self N 2
  generalize hm : N / 2 = m at hodd hlevel
  subst N
  exact not_isPrimitive_two_mul χ hodd hχ

-- The small excluded levels include 2 itself; no nontriviality of the value monoid is needed.
example (χ : DirichletCharacter R 2) : ¬χ.IsPrimitive :=
  not_isPrimitive_two_mul (m := 1) χ (by decide)

example (χ : DirichletCharacter R 6) : ¬χ.IsPrimitive :=
  not_isPrimitive_two_mul (m := 3) χ (by decide)

example (χ : DirichletCharacter R 10) : ¬χ.IsPrimitive :=
  not_isPrimitive_two_mul (m := 5) χ (by decide)

example (χ : DirichletCharacter R 14) : ¬χ.IsPrimitive :=
  not_isPrimitive_two_mul (m := 7) χ (by decide)

end DirichletCharacter
