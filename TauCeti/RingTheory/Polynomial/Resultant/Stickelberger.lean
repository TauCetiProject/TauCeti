/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.FormDiscriminant
public import TauCeti.RingTheory.MvPolynomial.StronglyDvd

import TauCeti.RingTheory.MvPolynomial.SquareModFour
import TauCeti.RingTheory.Polynomial.Resultant.FreeMonic
import TauCeti.RingTheory.Polynomial.Resultant.Normalization

/-!
# Stickelberger's congruence for binary forms

The universal discriminant of a binary form is a square modulo four. Consequently the
discriminant of every integral binary form is zero or one modulo four, including forms with
roots at infinity. Its residue modulo four is constant on each coefficient class modulo two,
so divisibility by four at one representative is strong divisibility throughout the class.
In particular, no integral binary-form discriminant has valuation exactly one at two.

The monic case uses Mathlib's `MvPolynomial.esymmAlgEquiv` to descend the even and odd
parts argument from the roots, adapting the number-field proof in
`TauCeti.NumberTheory.NumberField.Discriminant.Stickelberger`. The identity
`Polynomial.discr_integralNormalization` then reduces the universal binary-form case to
cancelling an even power of the leading variable.

## References

* M. Bhargava, A. Shankar, and X. Wang, *Squarefree values of polynomial discriminants II*,
  Forum Math. Pi 13 (2025), e17, §1 and Appendix A.
-/

public section

open MvPolynomial

namespace TauCeti

open Polynomial

/-- The universal binary-form discriminant is a square modulo four in the coefficient ring. -/
theorem exists_universalDiscr_eq_sq_sub_four_mul (n : ℕ) :
    ∃ s t : MvPolynomial (Fin (n + 1)) ℤ, universalDiscr n = s ^ 2 - 4 * t := by
  have hnz : universalPoly n ≠ 0 := leadingCoeff_ne_zero.mp <| by simp
  obtain ⟨s, t, h⟩ := (monic_integralNormalization hnz).exists_discr_eq_sq_sub_four_mul
  obtain ⟨k, hk⟩ : Even ((n - 1) * (n - 2)) := by
    simpa only [Nat.sub_sub, one_add_one_eq_two] using Nat.even_mul_pred_self (n - 1)
  rw [discr_integralNormalization, natDegree_universalPoly, leadingCoeff_universalPoly,
    ← universalDiscr_def, hk, pow_add, ← pow_two] at h
  exact exists_eq_sq_sub_four_mul_of_X_pow_mul (Fin.last n) k h

/-- The universal binary-form discriminant modulo four depends only on the coefficient
vector modulo two. -/
theorem eval_universalDiscr_modEq_four {n : ℕ} {a b : Fin (n + 1) → ℤ}
    (h : ∀ i, a i ≡ b i [ZMOD 2]) :
    eval a (universalDiscr n) ≡ eval b (universalDiscr n) [ZMOD 4] := by
  obtain ⟨s, t, hd⟩ := exists_universalDiscr_eq_sq_sub_four_mul n
  exact Int.modEq_iff_dvd.mpr
    (four_dvd_eval_sub_eval_of_eq_sq_sub_four_mul hd fun i ↦ (h i).dvd)

/-- If the discriminant at an integral coefficient vector is even, it is divisible by four. -/
theorem four_dvd_eval_universalDiscr_of_two_dvd {n : ℕ} {a : Fin (n + 1) → ℤ}
    (ha : 2 ∣ eval a (universalDiscr n)) : 4 ∣ eval a (universalDiscr n) := by
  obtain ⟨s, t, hd⟩ := exists_universalDiscr_eq_sq_sub_four_mul n
  have he : eval a (universalDiscr n) % 4 = eval a s ^ 2 % 4 := by
    simp [hd, map_ofNat, Int.sub_mul_emod_self_left]
  have hs := Int.sq_emod_four (eval a s)
  omega

/-- If four divides the discriminant at one coefficient vector, it divides the discriminant at
every coefficient vector congruent to it modulo two. Thus weak square divisibility at two
is absent. -/
@[simp]
theorem not_weaklyDvdAt_sq_universalDiscr_two (n : ℕ) (a : Fin (n + 1) → ℤ) :
    ¬ (universalDiscr n).WeaklyDvdAt 2 4 a := by
  obtain ⟨s, t, h⟩ := exists_universalDiscr_eq_sq_sub_four_mul n
  exact not_weaklyDvdAt_of_eq_sq_sub_four_mul h

end TauCeti

namespace Polynomial

/-- The fixed-degree binary-form discriminant is a square minus four times an element of
the coefficient ring. -/
theorem exists_formDiscr_eq_sq_sub_four_mul {R : Type*} [CommRing R] (f : R[X]) (n : ℕ) :
    ∃ s t : R, f.formDiscr n = s ^ 2 - 4 * t := by
  obtain ⟨s, t, h⟩ := TauCeti.exists_universalDiscr_eq_sq_sub_four_mul n
  let φ := MvPolynomial.aeval (R := ℤ) fun i : Fin (n + 1) ↦ f.coeff i
  exact ⟨φ s, φ t, by simp [formDiscr_def, φ, h, map_ofNat]⟩

/-- The discriminant of a polynomial is a square minus four times an element of its
coefficient ring. -/
theorem exists_discr_eq_sq_sub_four_mul {R : Type*} [CommRing R] (f : R[X]) :
    ∃ s t : R, f.discr = s ^ 2 - 4 * t := by
  rw [← formDiscr_of_natDegree_eq (G := f) rfl]
  exact f.exists_formDiscr_eq_sq_sub_four_mul f.natDegree

/-- Stickelberger's congruence for an integral binary form, including a form with zero leading
coefficient at the specified degree. -/
theorem formDiscr_emod_four_eq_zero_or_one (f : ℤ[X]) (n : ℕ) :
    f.formDiscr n % 4 = 0 ∨ f.formDiscr n % 4 = 1 := by
  obtain ⟨s, t, h⟩ := f.exists_formDiscr_eq_sq_sub_four_mul n
  rw [h, Int.sub_mul_emod_self_left]
  have hs := Int.sq_emod_four s
  omega

end Polynomial
