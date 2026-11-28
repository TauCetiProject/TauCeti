/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Polynomial correction of approximate idempotents

The polynomial `1 - (1 - X ^ d) ^ d` vanishes modulo `X ^ d` and is one modulo
`(X - 1) ^ d`. Evaluating it on an element with `(x - x ^ 2) ^ d = 0` gives the
idempotent of Mathlib's `isIdempotentElem_one_sub_one_sub_pow_pow`. The congruences
also compare it with the polynomial `((X - 1) ^ d + 1) ^ d` for odd `d`.

## References

* A. Caraiani, *Local-global compatibility and the action of monodromy on nearby
  cycles*, arXiv:1010.2188v1, §2.1.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The polynomial correcting an idempotence error of nilpotence index at most `d`. -/
noncomputable def idempotentCorrection (d : ℕ) : R[X] :=
  1 - (1 - X ^ d) ^ d

/-- The defining formula for the idempotent correction polynomial. -/
theorem idempotentCorrection_def (d : ℕ) :
    idempotentCorrection (R := R) d = 1 - (1 - X ^ d) ^ d := (rfl)

/-- The correction evaluated in an algebra. -/
@[simp]
theorem aeval_idempotentCorrection {A : Type*} [Ring A] [Algebra R A] (x : A) (d : ℕ) :
    aeval x (idempotentCorrection (R := R) d) = 1 - (1 - x ^ d) ^ d := by
  simp [idempotentCorrection]

/-- The correction is zero modulo `X ^ d`. -/
theorem X_pow_dvd_idempotentCorrection (d : ℕ) :
    (X : R[X]) ^ d ∣ idempotentCorrection d := by
  have h := sub_dvd_pow_sub_pow (1 : R[X]) (1 - X ^ d) d
  rw [sub_sub_self, one_pow] at h
  exact h

/-- The correction is one modulo `(X - 1) ^ d`. -/
theorem X_sub_one_pow_dvd_idempotentCorrection_sub_one (d : ℕ) :
    ((X : R[X]) - 1) ^ d ∣ idempotentCorrection d - 1 := by
  have h : (X : R[X]) - 1 ∣ 1 - X ^ d := by
    simpa using (dvd_neg.mpr (sub_dvd_pow_sub_pow (X : R[X]) 1 d))
  simpa [idempotentCorrection] using dvd_neg.mpr (pow_dvd_pow_of_dvd h d)

/-- The correction leaves idempotent elements unchanged, as recorded by this polynomial
congruence modulo `X * (X - 1)`. -/
theorem X_mul_X_sub_one_dvd_idempotentCorrection_sub_X {d : ℕ} (hd : d ≠ 0) :
    (X : R[X]) * (X - 1) ∣ idempotentCorrection d - X := by
  apply (IsCoprime.sub_one_right_of_dvd dvd_rfl).mul_dvd
  · exact dvd_sub ((dvd_pow_self _ hd).trans (X_pow_dvd_idempotentCorrection d)) dvd_rfl
  · have h : ((X : R[X]) - 1) ∣ idempotentCorrection d - 1 :=
      (dvd_pow_self _ hd).trans (X_sub_one_pow_dvd_idempotentCorrection_sub_one d)
    simpa only [sub_sub_sub_cancel_right] using dvd_sub h (dvd_refl (X - 1))

/-- For odd `d`, Caraiani's correction and `idempotentCorrection d` differ by a multiple of
`X ^ d * (X - 1) ^ d`. -/
theorem X_pow_mul_X_sub_one_pow_dvd_sub_idempotentCorrection {d : ℕ} (hd : Odd d) :
    (X : R[X]) ^ d * (X - 1) ^ d ∣ ((X - 1) ^ d + 1) ^ d - idempotentCorrection d := by
  have hCoprime : IsCoprime (X : R[X]) (X - 1) := IsCoprime.sub_one_right_of_dvd dvd_rfl
  apply (hCoprime.pow_left.pow_right).mul_dvd
  · have h : (X : R[X]) ∣ (X - 1) ^ d + 1 := by
      simpa [hd.neg_pow] using sub_dvd_pow_sub_pow ((X : R[X]) - 1) (-1) d
    exact dvd_sub (pow_dvd_pow_of_dvd h d) (X_pow_dvd_idempotentCorrection d)
  · have h : ((X : R[X]) - 1) ^ d ∣ ((X - 1) ^ d + 1) ^ d - 1 := by
      simpa using sub_dvd_pow_sub_pow (((X : R[X]) - 1) ^ d + 1) 1 d
    simpa only [sub_sub_sub_cancel_right] using
      dvd_sub h (X_sub_one_pow_dvd_idempotentCorrection_sub_one d)

/-- At an element whose idempotence error has zero `d`-th power, Caraiani's formula for odd
`d` gives the same correction. -/
theorem aeval_idempotentCorrection_eq_of_odd {A : Type*} [Ring A] [Algebra R A] (x : A)
    {d : ℕ} (hd : Odd d) (hx : (x - x ^ 2) ^ d = 0) :
    aeval x (idempotentCorrection (R := R) d) = ((x - 1) ^ d + 1) ^ d := by
  have hc : Commute x (x - 1) := (Commute.refl x).sub_right (Commute.one_right x)
  have hz : aeval x ((X : R[X]) ^ d * (X - 1) ^ d) = 0 := by
    simp only [map_mul, map_pow, map_sub, map_one, aeval_X]
    rw [← hc.mul_pow, mul_sub, mul_one, ← pow_two, ← neg_sub, neg_pow, hx, mul_zero]
  have h := aeval_eq_zero_of_dvd_aeval_eq_zero
    (X_pow_mul_X_sub_one_pow_dvd_sub_idempotentCorrection hd) hz
  rw [map_sub, sub_eq_zero] at h
  simpa only [map_sub, map_pow, map_add, map_one, aeval_X] using h.symm

end Polynomial
