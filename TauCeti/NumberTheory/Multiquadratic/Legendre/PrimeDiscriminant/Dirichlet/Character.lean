/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Character
public import TauCeti.NumberTheory.DirichletCharacter.Basic

/-!
# Primitive Dirichlet characters of prime discriminants

A prime discriminant `P` determines a real quadratic Dirichlet character of level `|P|`. This
file bundles the previously unbundled function `primeDiscriminantCharFun P` as
`primeDiscriminantChar P hP` and proves that its conductor is exactly `|P|`.

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
* `TauCeti.Multiquadratic.isPrimitive_primeDiscriminantChar`: its conductor is `|P|`.
-/

public section

namespace TauCeti.Multiquadratic

/-- **The real quadratic Dirichlet character attached to a prime discriminant.** At `-4`, `8`,
and `-8` this is respectively `ZMod.χ₄`, `ZMod.χ₈`, and `ZMod.χ₈'`; at an odd prime
discriminant `p*` it is the quadratic character modulo `p`. -/
noncomputable def primeDiscriminantChar (P : ℤ) (hP : IsPrimeDiscriminant P) :
    DirichletCharacter ℤ P.natAbs := by
  letI : NeZero P.natAbs := ⟨Int.natAbs_ne_zero.mpr hP.ne_zero⟩
  exact
    { toFun := fun a => primeDiscriminantCharFun P a.val
      map_one' := by
        rw [← primeDiscriminantCharFun_one P]
        apply primeDiscriminantCharFun_mod_right'
        apply (ZMod.intCast_eq_intCast_iff' _ _ _).mp
        exact_mod_cast ZMod.natCast_zmod_val (1 : ZMod P.natAbs)
      map_mul' := fun a b => by
        rw [← primeDiscriminantCharFun_mul_right]
        apply primeDiscriminantCharFun_mod_right'
        apply (ZMod.intCast_eq_intCast_iff' _ _ _).mp
        calc
          ((((a * b).val : ℕ) : ℤ) : ZMod P.natAbs) =
              ((a * b).val : ℕ) := by norm_cast
          _ = a * b := ZMod.natCast_zmod_val _
          _ = (a.val : ZMod P.natAbs) * (b.val : ZMod P.natAbs) := by
            rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
          _ = ((a.val : ℤ) : ZMod P.natAbs) * ((b.val : ℤ) : ZMod P.natAbs) := by
            norm_cast
          _ = (((a.val : ℤ) * (b.val : ℤ) : ℤ) : ZMod P.natAbs) := by
            rw [Int.cast_mul]
      map_nonunit' := fun a ha => by
        rw [primeDiscriminantCharFun_eq_zero_iff hP]
        intro hcop
        apply ha
        have hcopNat : Nat.Coprime a.val P.natAbs := by
          simpa only [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast] using hcop
        have hunit : IsUnit (a.val : ZMod P.natAbs) :=
          (ZMod.isUnit_iff_coprime _ _).2 hcopNat
        rwa [ZMod.natCast_zmod_val] at hunit }

/-- The bundled character evaluates to the unbundled prime-discriminant character on integers. -/
@[simp] theorem primeDiscriminantChar_apply_int (P : ℤ) (hP : IsPrimeDiscriminant P) (n : ℤ) :
    primeDiscriminantChar P hP n = primeDiscriminantCharFun P n := by
  let _ : NeZero P.natAbs := ⟨Int.natAbs_ne_zero.mpr hP.ne_zero⟩
  apply primeDiscriminantCharFun_mod_right'
  apply (ZMod.intCast_eq_intCast_iff' _ _ _).mp
  exact_mod_cast ZMod.natCast_zmod_val (n : ZMod P.natAbs)

/-- The character attached to a prime discriminant is nontrivial. -/
theorem primeDiscriminantChar_ne_one (P : ℤ) (hP : IsPrimeDiscriminant P) :
    primeDiscriminantChar P hP ≠ 1 := by
  obtain ⟨a, ha⟩ := exists_primeDiscriminantCharFun_eq_neg_one hP
  intro h
  have happ : primeDiscriminantChar P hP (a : ℤ) =
      (1 : DirichletCharacter ℤ P.natAbs) (a : ℤ) := by
    exact DFunLike.congr_fun h ((a : ℤ) : ZMod P.natAbs)
  have haunit : IsUnit ((a : ℤ) : ZMod P.natAbs) := by
    by_contra ha'
    have hz := MulChar.map_nonunit (primeDiscriminantChar P hP) ha'
    have hz' : primeDiscriminantChar P hP (a : ℤ) = 0 := hz
    rw [primeDiscriminantChar_apply_int, ha] at hz'
    norm_num at hz'
  rw [primeDiscriminantChar_apply_int, ha, MulChar.one_apply haunit] at happ
  omega

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
  rcases isPrimeDiscriminant_iff.mp hP with hP | ⟨p, hp, hodd, hP⟩
  · rcases hP with rfl | rfl | rfl
    · exact DirichletCharacter.conductor_eq_four_of_apply_one_ne_apply_three _
        (by simp [primeDiscriminantChar])
    · exact DirichletCharacter.conductor_eq_eight_of_apply_one_ne_apply_five _
        (by simp [primeDiscriminantChar])
    · exact DirichletCharacter.conductor_eq_eight_of_apply_one_ne_apply_five _
        (by simp [primeDiscriminantChar])
  · subst P
    have hdiv : (primeDiscriminantChar (oddPrimeDiscriminant p) hP).conductor ∣ p := by
      simpa only [oddPrimeDiscriminant_natAbs] using DirichletCharacter.conductor_dvd_level
        (primeDiscriminantChar (oddPrimeDiscriminant p) hP)
    have hcond : (primeDiscriminantChar (oddPrimeDiscriminant p) hP).conductor = p :=
      ((Nat.dvd_prime hp).mp hdiv).resolve_left hne_one
    simpa only [oddPrimeDiscriminant_natAbs] using hcond

end TauCeti.Multiquadratic
