/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Character
public import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic

/-!
# Primitive Dirichlet characters of prime discriminants

A prime discriminant `P` determines a real quadratic Dirichlet character of level `|P|`, the
Kronecker character `TauCeti.kroneckerChar` of `P`. This file names it `primeDiscriminantChar P hP`,
identifies its values with the function `primeDiscriminantCharFun P`, and proves that its conductor
is exactly `|P|`.

For the three even prime discriminants this is Mathlib's `ZMod.χ₄`, `ZMod.χ₈`, or `ZMod.χ₈'`.
For an odd prime discriminant `p*`, it is the quadratic character of `ZMod p`, equivalently the
Legendre symbol `(· / p)`. Primitivity at an odd prime level follows from nontriviality. At levels
`4` and `8`, the values at `1` and respectively `3` or `5` show that the character cannot descend
to a proper divisor of its level.

These primitive characters are the character-theoretic input for the conductor-minimality part of
the quadratic Kronecker--Weber theorem: Mathlib's cyclotomic Galois correspondence detects a
subfield by the conductors of its associated Dirichlet characters.

The description is classical; see K. Ireland and M. Rosen, *A Classical Introduction to Modern
Number Theory*, Chapter 6.

## Main definitions and results

* `TauCeti.Multiquadratic.primeDiscriminantChar`: the Dirichlet character of level `|P|`
  attached to the prime discriminant `P`.
* `TauCeti.Multiquadratic.primeDiscriminantChar_apply_int`: its value on an integer is
  `primeDiscriminantCharFun P`.
* `TauCeti.Multiquadratic.isQuadratic_primeDiscriminantChar`: it takes only the values
  `0`, `1`, `-1`.
* `TauCeti.Multiquadratic.isPrimitive_primeDiscriminantChar`: its conductor is `|P|`.
-/

public section

namespace TauCeti.Multiquadratic

/-- **The real quadratic Dirichlet character attached to a prime discriminant.** It is the
Kronecker character `(P / ·)` of level `|P|`. At `-4`, `8`, and `-8` this is respectively
`ZMod.χ₄`, `ZMod.χ₈`, and `ZMod.χ₈'`; at an odd prime discriminant `p*` it is the quadratic
character modulo `p`. -/
def primeDiscriminantChar (P : ℤ) (hP : IsPrimeDiscriminant P) : DirichletCharacter ℤ P.natAbs :=
  kroneckerChar ℤ P (hP.isFundamentalDiscr.emod_four_eq_zero_or_one.imp id id) hP.ne_zero

/-- The bundled character evaluates to the unbundled prime-discriminant character on integers. -/
@[simp] theorem primeDiscriminantChar_apply_int (P : ℤ) (hP : IsPrimeDiscriminant P) (n : ℤ) :
    primeDiscriminantChar P hP n = primeDiscriminantCharFun P n :=
  (kroneckerChar_intCast _ _ n).trans (primeDiscriminantCharFun_eq_kroneckerSym hP n).symm

/-- The character attached to a prime discriminant is nontrivial. -/
theorem primeDiscriminantChar_ne_one (P : ℤ) (hP : IsPrimeDiscriminant P) :
    primeDiscriminantChar P hP ≠ 1 := by
  obtain ⟨a, ha⟩ := exists_primeDiscriminantCharFun_eq_neg_one hP
  have haunit : IsUnit ((a : ℤ) : ZMod P.natAbs) := by
    by_contra ha'
    have hz : primeDiscriminantChar P hP ((a : ℤ) : ZMod P.natAbs) = 0 :=
      MulChar.map_nonunit (primeDiscriminantChar P hP) ha'
    rw [primeDiscriminantChar_apply_int, ha] at hz
    norm_num at hz
  refine MulChar.ne_one_iff.mpr ⟨haunit.unit, ?_⟩
  rw [IsUnit.unit_spec, primeDiscriminantChar_apply_int, ha]
  norm_num

/-- The Dirichlet character attached to a prime discriminant is quadratic. -/
theorem isQuadratic_primeDiscriminantChar (P : ℤ) (hP : IsPrimeDiscriminant P) :
    (primeDiscriminantChar P hP).IsQuadratic :=
  kroneckerChar_isQuadratic _ _

/-- **The Dirichlet character of a prime discriminant is primitive.** Its conductor is exactly
the absolute value of the prime discriminant. -/
theorem isPrimitive_primeDiscriminantChar (P : ℤ) (hP : IsPrimeDiscriminant P) :
    DirichletCharacter.IsPrimitive (primeDiscriminantChar P hP) := by
  let _ : NeZero P.natAbs := ⟨Int.natAbs_ne_zero.mpr hP.ne_zero⟩
  rw [DirichletCharacter.isPrimitive_def]
  have hne_one : (primeDiscriminantChar P hP).conductor ≠ 1 := by
    intro h
    exact primeDiscriminantChar_ne_one P hP
      ((DirichletCharacter.eq_one_iff_conductor_eq_one).2 h)
  rcases isPrimeDiscriminant_iff.mp hP with hP | ⟨p, hp, _, hP⟩
  · -- At an even prime discriminant the character is `χ₄`, `χ₈` or `χ₈'`, whose values at `1`
    -- and at `3`, respectively `5`, are `1` and `-1`.
    rcases hP with rfl | rfl | rfl
    · refine DirichletCharacter.conductor_eq_four_of_apply_one_ne_apply_three _ ?_
      rw [primeDiscriminantChar_apply_int, primeDiscriminantChar_apply_int,
        primeDiscriminantCharFun_one, primeDiscriminantCharFun_neg_four,
        ZMod.χ₄_int_eq_if_mod_four]
      norm_num
    · refine DirichletCharacter.conductor_eq_eight_of_apply_one_ne_apply_five _ ?_
      rw [primeDiscriminantChar_apply_int, primeDiscriminantChar_apply_int,
        primeDiscriminantCharFun_one, primeDiscriminantCharFun_eight,
        ZMod.χ₈_int_eq_if_mod_eight]
      norm_num
    · refine DirichletCharacter.conductor_eq_eight_of_apply_one_ne_apply_five _ ?_
      rw [primeDiscriminantChar_apply_int, primeDiscriminantChar_apply_int,
        primeDiscriminantCharFun_one, primeDiscriminantCharFun_neg_eight,
        ZMod.χ₈'_int_eq_if_mod_eight]
      norm_num
  · subst P
    have hdiv : (primeDiscriminantChar (oddPrimeDiscriminant p) hP).conductor ∣ p := by
      simpa only [oddPrimeDiscriminant_natAbs] using DirichletCharacter.conductor_dvd_level
        (primeDiscriminantChar (oddPrimeDiscriminant p) hP)
    have hcond : (primeDiscriminantChar (oddPrimeDiscriminant p) hP).conductor = p :=
      ((Nat.dvd_prime hp).mp hdiv).resolve_left hne_one
    simpa only [oddPrimeDiscriminant_natAbs] using hcond

end TauCeti.Multiquadratic
