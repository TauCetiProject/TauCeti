/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-!
# Rational algebraic integers

`ℤ` is integrally closed in `ℚ`, so an algebraic integer that happens to be rational is an
integer. This file records the numerical reading of that fact: an identity `n · z = m` between an
algebraic integer `z` and two natural numbers is a divisibility `n ∣ m`. It holds in an arbitrary
ring of characteristic zero, which need not contain `m / n`: scaling the roots of a monic integer
polynomial `p` killing `z` by `n` gives one with the integer root `m`, so `p (m / n) = 0` in `ℚ`.

## Main results

* `IsIntegral.dvd_of_natCast_mul_eq`: if `(n : k) * z = m` with `z` integral over `ℤ` in a ring of
  characteristic zero, then `n ∣ m`.
-/

public section

open Polynomial

/-- **A rational algebraic integer is an integer**, read as a divisibility: if `n · z = m` for
natural numbers `m` and `n`, and `z` is integral over `ℤ` in a ring of characteristic zero, then
`n` divides `m`. -/
theorem IsIntegral.dvd_of_natCast_mul_eq {k : Type*} [Ring k] [CharZero k] {m n : ℕ} {z : k}
    (hz : IsIntegral ℤ z) (h : (n : k) * z = m) : n ∣ m := by
  obtain rfl | hn := eq_or_ne n 0
  · simp_all [eq_comm]
  obtain ⟨p, hp, hpz⟩ := hz
  -- scaling the roots of `p` by `n` moves the root `z` to the integer `n * z = m`
  have hm : (p.scaleRoots n).eval (m : ℤ) = 0 := by
    have := scaleRoots_aeval_eq_zero (r := (n : ℤ)) hpz
    rw [map_natCast, h, ← map_natCast (algebraMap ℤ k), aeval_algebraMap_apply] at this
    simpa using this
  -- so `m / n` is a rational root of the monic `p`, hence an integer
  have hq : IsIntegral ℤ ((m : ℚ) / n) := by
    refine ⟨p, hp, ?_⟩
    have := scaleRoots_eval₂_mul (p := p) (algebraMap ℤ ℚ) ((m : ℚ) / n) n
    simpa [mul_div_cancel₀, aeval_def, hn, hm] using this.symm
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq
  rw [eq_intCast] at hy
  exact (Rat.den_div_natCast_eq_one_iff m n hn).mp (hy ▸ Rat.den_intCast y)
