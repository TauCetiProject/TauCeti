/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Int.Basic

/-!
# Divisibility of integers by powers of a prime, read in a domain

Let `p` be a prime number and `R` an integral domain in which the image of `p` is nonzero and not
a unit, for instance a discrete valuation ring with uniformiser `p` such as `ℤ_[p]` or the
localisation of `ℤ` at `p`. Then the cast `ℤ → R` reflects divisibility by powers of `p`:
`(p : R) ^ n ∣ (x : R)` exactly when `p ^ n ∣ x` in `ℤ`. Divisibility conditions on integral
Weierstrass coefficients can therefore be checked over `ℤ`, by computation, and read over `R`.

The proof peels off one factor of `p` at a time: if `p` does not divide an integer `y`, then `p`
and `y` are coprime in `ℤ`, so `(p : R) ∣ (y : R)` would make `(p : R)` divide `1`.

## Main results

* `Nat.Prime.pow_dvd_intCast_iff`: `(p : R) ^ n ∣ (x : R) ↔ (p : ℤ) ^ n ∣ x`.
-/

public section

namespace Nat.Prime

/-- **Over a domain in which a prime `p` is a nonzero nonunit, divisibility of integers by powers
of `p` can be read in `ℤ`.** This is the general form of `PadicInt.pow_p_dvd_int_iff`. -/
theorem pow_dvd_intCast_iff {p : ℕ} (hp : p.Prime) {R : Type*} [CommRing R] [IsDomain R]
    (h₀ : (p : R) ≠ 0) (hu : ¬ IsUnit (p : R)) (n : ℕ) (x : ℤ) :
    (p : R) ^ n ∣ (x : R) ↔ (p : ℤ) ^ n ∣ x := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa using map_dvd (Int.castRingHom R) h⟩
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨y, rfl⟩ := ih x ((pow_dvd_pow _ n.le_succ).trans h)
    rw [pow_succ]
    refine mul_dvd_mul_left _ (not_not.1 fun hpy ↦ hu ?_)
    rw [pow_succ, Int.cast_mul, Int.cast_pow, Int.cast_natCast] at h
    have hy : (p : R) ∣ (y : R) := (mul_dvd_mul_iff_left (pow_ne_zero n h₀)).1 h
    obtain ⟨a, b, hab⟩ :=
      ((Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd).2 hpy
    have hab' := congrArg (Int.cast : ℤ → R) hab
    push_cast at hab'
    exact isUnit_of_dvd_one (hab' ▸ dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_right hy _))

end Nat.Prime
