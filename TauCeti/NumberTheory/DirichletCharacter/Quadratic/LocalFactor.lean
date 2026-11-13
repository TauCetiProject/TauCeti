/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LocalFactor
public import TauCeti.NumberTheory.DirichletCharacter.OddPrimePower.Quadratic
public import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Classification
public import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Quadratic
public import TauCeti.NumberTheory.DirichletCharacter.Quadratic.OddPart

/-!
# Local conductors of a quadratic Dirichlet character

A Dirichlet character `χ` of level `N ≠ 0` is the product of the lifts of its local factors
(`DirichletCharacter.prod_changeLevel_localFactor`), its conductor is the product of the
conductors of the local factors (`DirichletCharacter.conductor_eq_prod_conductor_localFactor`),
and `χ` is quadratic exactly when its local factors are
(`DirichletCharacter.isQuadratic_iff_forall_isQuadratic_localFactor`). This file adds what the
quadratic case contributes: each local conductor is `1` or `p` at an odd prime `p`, by the odd
prime-power classification, and `1`, `4` or `8` at `p = 2`, by the dyadic classification.

Equivalently, the conductor of `χ`, which is the level of its primitive character `χ*`, has
squarefree odd part and `2`-adic exponent `0`, `2` or `3`. These are the shape results for
primitive levels, `DirichletCharacter.IsPrimitive.squarefree_ordCompl_two` and
`DirichletCharacter.IsPrimitive.factorization_two_eq_zero_or_two_or_three`, applied to `χ*`,
which is quadratic when `χ` is.

The results are proved for characters of order dividing two with values in any commutative
monoid with zero, and specialised to quadratic characters with values in a commutative ring.

## Main results

* `DirichletCharacter.primitiveCharacter_sq_eq_one`, `MulChar.IsQuadratic.primitiveCharacter`:
  the primitive character of a character of order dividing two, or of a quadratic character, is
  again one.
* `DirichletCharacter.conductor_localFactor_eq_one_or_eq_prime_of_sq_eq_one`,
  `MulChar.IsQuadratic.conductor_localFactor_eq_one_or_eq_prime`: at an odd prime `p`, the
  local conductor is `1` or `p`.
* `DirichletCharacter.conductor_localFactor_two_eq_one_or_four_or_eight_of_sq_eq_one`,
  `MulChar.IsQuadratic.conductor_localFactor_two_eq_one_or_four_or_eight`: at `2`, the local
  conductor is `1`, `4` or `8`.
* `MulChar.IsQuadratic.factorization_conductor_le_one`,
  `MulChar.IsQuadratic.squarefree_ordCompl_two_conductor`,
  `MulChar.IsQuadratic.factorization_two_conductor_eq_zero_or_two_or_three`: the shape of the
  conductor.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*,
  Cambridge Studies in Advanced Mathematics 97 (2006), Lemma 9.3 and §9.3, pp. 283 and
  295–296.
-/

public section

namespace DirichletCharacter

section SqEqOne

variable {R : Type*} [CommMonoidWithZero R] {N : ℕ} {χ : DirichletCharacter R N}

/-- The primitive character of a character of order dividing two at a nonzero level has order
dividing two. -/
theorem primitiveCharacter_sq_eq_one [NeZero N] (hχ : χ ^ 2 = 1) :
    χ.primitiveCharacter ^ 2 = 1 := by
  apply changeLevel_injective χ.conductor_dvd_level
  rw [map_pow, changeLevel_primitiveCharacter, map_one, hχ]

/-- The local factors of a character of order dividing two have order dividing two. -/
theorem localFactor_sq_eq_one (hχ : χ ^ 2 = 1) (p : ℕ) : localFactor p χ ^ 2 = 1 := by
  rw [← map_pow, hχ, map_one]

/-- **The local conductor at an odd prime.** For an odd prime `p`, the local factor at `p` of a
character of order dividing two has conductor `1` or `p`. -/
theorem conductor_localFactor_eq_one_or_eq_prime_of_sq_eq_one (hχ : χ ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    (localFactor p χ).conductor = 1 ∨ (localFactor p χ).conductor = p :=
  conductor_eq_one_or_eq_prime_of_sq_eq_one hp hp2 _ (localFactor_sq_eq_one hχ p)

/-- **The local conductor at `2`.** The local factor at `2` of a character of order dividing two
has conductor `1`, `4` or `8`. -/
theorem conductor_localFactor_two_eq_one_or_four_or_eight_of_sq_eq_one (hχ : χ ^ 2 = 1) :
    (localFactor 2 χ).conductor = 1 ∨ (localFactor 2 χ).conductor = 4 ∨
      (localFactor 2 χ).conductor = 8 :=
  conductor_eq_one_or_four_or_eight_of_sq_eq_one (localFactor_sq_eq_one hχ 2)

/-- An odd prime divides the conductor of a character of order dividing two at most once. -/
theorem factorization_conductor_le_one_of_sq_eq_one (hχ : χ ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : χ.conductor.factorization p ≤ 1 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [conductor_eq_zero_iff_level_eq_zero.mpr rfl]
  have : NeZero N := ⟨hN⟩
  exact χ.primitiveCharacter_isPrimitive.factorization_le_one_of_sq_eq_one
    (primitiveCharacter_sq_eq_one hχ) hp hp2

/-- The odd part of the conductor of a character of order dividing two at a nonzero level is
squarefree. -/
theorem squarefree_ordCompl_two_conductor_of_sq_eq_one [NeZero N] (hχ : χ ^ 2 = 1) :
    Squarefree (ordCompl[2] χ.conductor) :=
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  χ.primitiveCharacter_isPrimitive.squarefree_ordCompl_two_of_sq_eq_one
    (primitiveCharacter_sq_eq_one hχ)

/-- The `2`-adic exponent of the conductor of a character of order dividing two is `0`, `2` or
`3`. -/
theorem factorization_two_conductor_eq_zero_or_two_or_three_of_sq_eq_one (hχ : χ ^ 2 = 1) :
    χ.conductor.factorization 2 = 0 ∨ χ.conductor.factorization 2 = 2 ∨
      χ.conductor.factorization 2 = 3 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [conductor_eq_zero_iff_level_eq_zero.mpr rfl]
  have : NeZero N := ⟨hN⟩
  exact χ.primitiveCharacter_isPrimitive.factorization_two_eq_zero_or_two_or_three_of_sq_eq_one
    (primitiveCharacter_sq_eq_one hχ)

end SqEqOne

end DirichletCharacter

namespace MulChar.IsQuadratic

open DirichletCharacter

variable {R : Type*} [CommRing R] {N : ℕ} {χ : DirichletCharacter R N}

/-- The primitive character of a quadratic Dirichlet character at a nonzero level is quadratic:
its values at units are values of `χ` at units lifting them. -/
theorem primitiveCharacter [NeZero N] (hχ : χ.IsQuadratic) :
    χ.primitiveCharacter.IsQuadratic := by
  rw [← isQuadratic_changeLevel_iff χ.conductor_dvd_level, changeLevel_primitiveCharacter]
  exact hχ

/-- **The local conductor of a quadratic character at an odd prime** is `1` or `p`. -/
theorem conductor_localFactor_eq_one_or_eq_prime (hχ : χ.IsQuadratic) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    (DirichletCharacter.localFactor p χ).conductor = 1 ∨
      (DirichletCharacter.localFactor p χ).conductor = p :=
  conductor_localFactor_eq_one_or_eq_prime_of_sq_eq_one hχ.sq_eq_one hp hp2

/-- **The local conductor of a quadratic character at `2`** is `1`, `4` or `8`. -/
theorem conductor_localFactor_two_eq_one_or_four_or_eight (hχ : χ.IsQuadratic) :
    (DirichletCharacter.localFactor 2 χ).conductor = 1 ∨
      (DirichletCharacter.localFactor 2 χ).conductor = 4 ∨
      (DirichletCharacter.localFactor 2 χ).conductor = 8 :=
  conductor_localFactor_two_eq_one_or_four_or_eight_of_sq_eq_one hχ.sq_eq_one

/-- An odd prime divides the conductor of a quadratic character at most once. -/
theorem factorization_conductor_le_one (hχ : χ.IsQuadratic) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : χ.conductor.factorization p ≤ 1 :=
  factorization_conductor_le_one_of_sq_eq_one hχ.sq_eq_one hp hp2

/-- The odd part of the conductor of a quadratic character at a nonzero level is squarefree. -/
theorem squarefree_ordCompl_two_conductor [NeZero N] (hχ : χ.IsQuadratic) :
    Squarefree (ordCompl[2] χ.conductor) :=
  squarefree_ordCompl_two_conductor_of_sq_eq_one hχ.sq_eq_one

/-- The `2`-adic exponent of the conductor of a quadratic character is `0`, `2` or `3`. -/
theorem factorization_two_conductor_eq_zero_or_two_or_three (hχ : χ.IsQuadratic) :
    χ.conductor.factorization 2 = 0 ∨ χ.conductor.factorization 2 = 2 ∨
      χ.conductor.factorization 2 = 3 :=
  factorization_two_conductor_eq_zero_or_two_or_three_of_sq_eq_one hχ.sq_eq_one

end MulChar.IsQuadratic

/-! ## Examples

The principal character of level `6` has principal local factors and conductor `1`. It vanishes
at `2` and `3`, while its primitive character, of level `1`, is `1` there. -/

open DirichletCharacter

example : localFactor 2 (1 : DirichletCharacter ℂ 6) = 1 := map_one _

example : localFactor 3 (1 : DirichletCharacter ℂ 6) = 1 := map_one _

example : (1 : DirichletCharacter ℂ 6).conductor = 1 := conductor_one

example : (1 : DirichletCharacter ℂ 6) 2 = 0 := MulChar.map_nonunit _ (by decide)

example : (1 : DirichletCharacter ℂ 6).primitiveCharacter 2 = 1 := by
  have : Subsingleton (ZMod (1 : DirichletCharacter ℂ 6).conductor) := by
    rw [conductor_one]
    infer_instance
  rw [Subsingleton.elim (2 : ZMod _) 1, map_one]

/-! At level `12`, `χ₄ · (Legendre mod 3)` has local conductors `4` and `3` and conductor `12`.
The character `χ₄` lifted to level `12` has local conductors `4` and `1` and conductor `4`. -/

example :
    let χ : DirichletCharacter ℂ 12 :=
      changeLevel (by norm_num : 4 ∣ 12) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) *
        changeLevel (by norm_num : 3 ∣ 12)
          ((quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ))
    χ.conductor = 12 ∧ (localFactor 2 χ).conductor = 4 ∧ (localFactor 3 χ).conductor = 3 := by
  intro χ
  have hR : ringChar ℂ ≠ 2 := by simp [ringChar.eq_zero]
  have h : χ.conductor = 12 := by
    rw [conductor_mul_of_coprime] <;>
      simp only [conductor_changeLevel, conductor_χ₄_ringHomComp,
        conductor_changeLevel_quadraticChar hR (by norm_num : 3 ≠ 2)]
    norm_num
  refine ⟨h, ?_, ?_⟩ <;>
    rw [conductor_localFactor, h, show (12 : ℕ) = 2 ^ 2 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.prime_two.factorization_pow] <;>
    simp [Nat.prime_three.factorization]

example :
    let χ : DirichletCharacter ℂ 12 :=
      changeLevel (by norm_num : 4 ∣ 12) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
    χ.conductor = 4 ∧ (localFactor 2 χ).conductor = 4 ∧ (localFactor 3 χ).conductor = 1 := by
  intro χ
  have h : χ.conductor = 4 := by simp [χ, conductor_changeLevel, conductor_χ₄_ringHomComp]
  refine ⟨h, ?_, ?_⟩ <;>
    rw [conductor_localFactor, h, show (4 : ℕ) = 2 ^ 2 by norm_num,
      Nat.prime_two.factorization_pow] <;> simp

/-! At level `45 = 9 · 5`, the product of the quadratic characters modulo `9` and modulo `5`
has conductor `15`, not `45`: its local factor at `3` is quadratic, so its conductor is `1` or
`3` by `MulChar.IsQuadratic.conductor_localFactor_eq_one_or_eq_prime`, and it is `3`. -/

example :
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let χ : DirichletCharacter ℂ 45 :=
      changeLevel (by norm_num : 9 ∣ 45) (changeLevel (by norm_num : 3 ∣ 9)
          ((quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ))) *
        changeLevel (by norm_num : 5 ∣ 45)
          ((quadraticChar (ZMod 5)).ringHomComp (Int.castRingHom ℂ))
    χ.conductor = 15 ∧ (localFactor 3 χ).conductor = 3 ∧ (localFactor 5 χ).conductor = 5 := by
  intro _ χ
  have hR : ringChar ℂ ≠ 2 := by simp [ringChar.eq_zero]
  have h : χ.conductor = 15 := by
    rw [conductor_mul_of_coprime] <;>
      simp only [conductor_changeLevel,
        conductor_changeLevel_quadraticChar hR (by norm_num : 3 ≠ 2),
        conductor_changeLevel_quadraticChar hR (by norm_num : 5 ≠ 2)]
    norm_num
  refine ⟨h, ?_, ?_⟩ <;>
    rw [conductor_localFactor, h, show (15 : ℕ) = 3 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)] <;>
    simp [Nat.prime_three.factorization, Nat.prime_five.factorization]
