/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Character
public import TauCeti.NumberTheory.NumberField.Frobenius
import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminants

/-!
# Frobenius on the square root of a prime discriminant

Let `P` be a prime discriminant and `x` a square root of its radicand in a number field. At every
rational prime `q` not dividing `P`, an arithmetic Frobenius fixes `x` exactly when the character
`primeDiscriminantCharFun P` attached to `P` takes the value `1` at `q`. This is the form in which
the genus characters of a quadratic field meet the Galois action on its genus field.

The statement makes no parity assumption on `q`. At an odd prime it is the Legendre-symbol action
`NumberField.isArithFrobAt_apply_sqrt_eq_self_iff` together with the identification
`primeDiscriminantCharFun_eq_legendreSym`. At `q = 2` the discriminant `P` is odd, hence congruent
to `1` modulo `4` and equal to its own radicand, and the dyadic action
`TauCeti.isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight` combines with the supplementary law
`primeDiscriminantCharFun_two`.

See D. A. Cox, *Primes of the Form x² + ny²*, §5.A and §6.A.

## Main results

* `TauCeti.Multiquadratic.isArithFrobAt_apply_sqrt_primeDiscriminantRadicand_eq_self_iff`: a
  Frobenius at a prime `q ∤ P` fixes `√P` exactly when the character of `P` is `1` at `q`.
-/

public section

open NumberField Ideal

namespace TauCeti.Multiquadratic

/-- **Frobenius acts on `√P` by the character of the prime discriminant `P`.** Let `K` be a number
field, `P` a prime discriminant, and `x ∈ K` a square root of the radicand of `P`. For a rational
prime `q` not dividing `P` (including `q = 2` when `P` is odd), an arithmetic Frobenius `σ` at an
ideal of `𝓞 K` above `q` fixes `x` exactly when `primeDiscriminantCharFun P q = 1`. -/
theorem isArithFrobAt_apply_sqrt_primeDiscriminantRadicand_eq_self_iff
    {K : Type*} [Field K] [NumberField K] {P : ℤ} (hP : IsPrimeDiscriminant P)
    {q : ℕ} [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ P)
    {x : K} (hx : x ^ 2 = algebraMap ℤ K (primeDiscriminantRadicand P))
    (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(q : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ x = x ↔ primeDiscriminantCharFun P q = 1 := by
  rcases eq_or_ne q 2 with rfl | hodd
  · -- `P` is odd, so it is its own radicand and is congruent to `1` modulo `4`.
    obtain ⟨p, hpp, hp, rfl⟩ := (isPrimeDiscriminant_iff.mp hP).resolve_left (by
      rintro (rfl | rfl | rfl) <;> norm_num at hq)
    have hmod := oddPrimeDiscriminant_mod_four_eq_one hp
    rw [primeDiscriminantRadicand_oddPrimeDiscriminant hp] at hx
    have : Q.LiesOver (span {(2 : ℤ)}) := by simpa using ‹Q.LiesOver (span {((2 : ℕ) : ℤ)})›
    rw [isArithFrobAt_apply_sqrt_eq_self_iff_mod_eight hx hmod Q hσ, Nat.cast_ofNat,
      primeDiscriminantCharFun_two (isPrimeDiscriminant_oddPrimeDiscriminant hpp hp),
      ZMod.χ₈_int_eq_if_mod_eight]
    split_ifs <;> simp only [iff_true, iff_false, zero_ne_one] <;> omega
  · have hqrad : ¬ (q : ℤ) ∣ primeDiscriminantRadicand P :=
      (dvd_primeDiscriminant_iff_dvd_radicand P hodd).not.mp hq
    rw [NumberField.isArithFrobAt_apply_sqrt_eq_self_iff hodd hqrad hx Q hσ,
      primeDiscriminantCharFun_eq_legendreSym hP hodd,
      legendreSym_eq_legendreSym_primeDiscriminantRadicand P hodd]

end TauCeti.Multiquadratic
