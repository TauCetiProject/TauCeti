/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Data.ZMod.Basic

/-!
# Reduction of integer polynomials modulo `n`

An integer polynomial reduces to zero in `(ZMod n)[X]` exactly when `n` divides every one of its
coefficients, that is, when the constant `n` divides it in `ℤ[X]`. Consequently two integer
polynomials with the same reduction modulo `n` differ by `n` times an integer polynomial.

## Main results

* `Polynomial.map_intCastRingHom_zmod_eq_zero_iff`: `G.map (Int.castRingHom (ZMod n)) = 0`
  exactly when `C n ∣ G`.
* `Polynomial.exists_C_mul_eq_sub_of_map_zmod_eq`: polynomials with the same reduction modulo
  `n` differ by `C n * D`.
-/

public section

namespace Polynomial

variable {n : ℕ}

/-- An integer polynomial reduces to zero modulo `n` exactly when the constant `n` divides it,
that is, when `n` divides each of its coefficients. -/
theorem map_intCastRingHom_zmod_eq_zero_iff (G : ℤ[X]) :
    G.map (Int.castRingHom (ZMod n)) = 0 ↔ C (n : ℤ) ∣ G := by
  rw [C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  simp only [coeff_map, coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Two integer polynomials with the same reduction modulo `n` differ by `n` times an integer
polynomial. -/
theorem exists_C_mul_eq_sub_of_map_zmod_eq {G G' : ℤ[X]}
    (h : G.map (Int.castRingHom (ZMod n)) = G'.map (Int.castRingHom (ZMod n))) :
    ∃ D : ℤ[X], C (n : ℤ) * D = G - G' := by
  obtain ⟨D, hD⟩ := (map_intCastRingHom_zmod_eq_zero_iff (n := n) (G - G')).mp (by
    rw [Polynomial.map_sub, h, sub_self])
  exact ⟨D, hD.symm⟩

end Polynomial
