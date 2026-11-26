/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.RingTheory.PowerSeries.Binomial

/-!
# Formal complex powers of power series

For a complex power series `P : ℂ⟦X⟧` whose constant coefficient is `Complex.exp ℓ`, this file
defines the formal complex power `PowerSeries.formalCpow ℓ r P` (`P ^ r` on the branch specified
by `ℓ`) by writing `P = Complex.exp ℓ * (1 + U)` with `constantCoeff U = 0` and taking the
formal binomial power `PowerSeries.binomialPow`:

`formalCpow ℓ r P = C (Complex.exp (r * ℓ)) * (C (Complex.exp (-ℓ)) * P).binomialPow r`.

The branch parameter `ℓ` fixes the constant term to `Complex.exp (r * ℓ)`, makes `formalCpow ℓ`
a homomorphism in the exponent `r` (`formalCpow_add`, `formalCpow_zero`, `formalCpow_one`,
`formalCpow_natCast`, `formalCpow_neg`), and shifts by `cexp (2πir)` when `ℓ` is shifted by
`2πi`.

## Main definitions

* `PowerSeries.formalCpow`: the formal power `P ^ r` of `P : ℂ⟦X⟧` whose constant coefficient is
  `Complex.exp ℓ`, with constant term fixed to `Complex.exp (r * ℓ)`.

## Main results

* `PowerSeries.constantCoeff_formalCpow`: the constant term of `formalCpow ℓ r P` is
  `Complex.exp (r * ℓ)`.
* `PowerSeries.formalCpow_zero`, `PowerSeries.formalCpow_one`, `PowerSeries.formalCpow_add`,
  `PowerSeries.formalCpow_natCast`, `PowerSeries.formalCpow_neg`: exponent laws for `formalCpow`.
* `PowerSeries.formalCpow_zero_one_add_X`: on `1 + X` with branch `ℓ = 0`, `formalCpow` reduces to
  `PowerSeries.binomialSeries ℂ r`.
* `PowerSeries.formalCpow_add_two_pi_mul_I`: shifting `ℓ` by `2πi` multiplies `formalCpow ℓ r P` by
  `cexp (2πir)`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.1(iii),
  <https://dlmf.nist.gov/2.1#iii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 1, §8.
-/

public section

open scoped Real

namespace PowerSeries

/-- The formal complex power `P ^ r` of a power series `P : ℂ⟦X⟧` whose constant term is
`Complex.exp ℓ`, with the branch fixed so that the constant term of `formalCpow ℓ r P` is
`Complex.exp (r * ℓ)` (DLMF §2.1(iii)). -/
noncomputable def formalCpow (ℓ r : ℂ) (P : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  C (Complex.exp (r * ℓ)) * (C (Complex.exp (-ℓ)) * P).binomialPow r

/-- Definitional equation for `formalCpow`. -/
theorem formalCpow_def (ℓ r : ℂ) (P : ℂ⟦X⟧) :
    formalCpow ℓ r P =
      C (Complex.exp (r * ℓ)) * (C (Complex.exp (-ℓ)) * P).binomialPow r := by
  rfl

private theorem constantCoeff_exp_neg_mul {ℓ : ℂ} {P : ℂ⟦X⟧}
    (hP : constantCoeff P = Complex.exp ℓ) :
    constantCoeff (C (Complex.exp (-ℓ)) * P) = 1 := by
  rw [map_mul, constantCoeff_C, hP, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- Rescaling a power series `P` with constant coefficient `Complex.exp ℓ` by `Complex.exp (-ℓ)`
and subtracting `1` yields a power series with zero constant coefficient. -/
theorem constantCoeff_exp_neg_mul_sub_one {ℓ : ℂ} {P : ℂ⟦X⟧}
    (hP : constantCoeff P = Complex.exp ℓ) :
    constantCoeff (C (Complex.exp (-ℓ)) * P - 1) = 0 := by
  rw [map_sub, map_one, constantCoeff_exp_neg_mul hP, sub_self]

/-- The constant term of `formalCpow ℓ r P` is `Complex.exp (r * ℓ)` when
`constantCoeff P = Complex.exp ℓ`. -/
@[simp]
theorem constantCoeff_formalCpow {ℓ r : ℂ} {P : ℂ⟦X⟧} (hP : constantCoeff P = Complex.exp ℓ) :
    constantCoeff (formalCpow ℓ r P) = Complex.exp (r * ℓ) := by
  rw [formalCpow_def, map_mul, constantCoeff_C,
    constantCoeff_binomialPow (constantCoeff_exp_neg_mul hP), mul_one]

/-- The zeroth formal complex power of any power series is `1`. -/
@[simp]
theorem formalCpow_zero (ℓ : ℂ) (P : ℂ⟦X⟧) : formalCpow ℓ 0 P = 1 := by
  rw [formalCpow_def, zero_mul, Complex.exp_zero, map_one, one_mul, binomialPow_zero]

/-- The first formal complex power recovers `P` when `constantCoeff P = Complex.exp ℓ`. -/
@[simp]
theorem formalCpow_one {ℓ : ℂ} {P : ℂ⟦X⟧} (hP : constantCoeff P = Complex.exp ℓ) :
    formalCpow ℓ 1 P = P := by
  rw [formalCpow_def, one_mul, binomialPow_one (constantCoeff_exp_neg_mul hP), ← mul_assoc,
    ← map_mul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, map_one, one_mul]

/-- Exponent addition law for formal complex powers with a fixed branch `ℓ`. -/
theorem formalCpow_add {ℓ : ℂ} (r r' : ℂ) {P : ℂ⟦X⟧} (hP : constantCoeff P = Complex.exp ℓ) :
    formalCpow ℓ (r + r') P = formalCpow ℓ r P * formalCpow ℓ r' P := by
  rw [formalCpow_def, formalCpow_def, formalCpow_def, add_mul, Complex.exp_add, map_mul,
    binomialPow_add (constantCoeff_exp_neg_mul hP)]
  ring

/-- Natural formal complex powers agree with ordinary powers in `ℂ⟦X⟧`. -/
@[simp]
theorem formalCpow_natCast {ℓ : ℂ} (n : ℕ) {P : ℂ⟦X⟧} (hP : constantCoeff P = Complex.exp ℓ) :
    formalCpow ℓ (n : ℂ) P = P ^ n := by
  rw [formalCpow_def, binomialPow_natCast (constantCoeff_exp_neg_mul hP), mul_pow, ← map_pow,
    ← Complex.exp_natCast_mul, ← mul_assoc, ← map_mul, ← Complex.exp_add]
  simp

/-- Negating the exponent in `formalCpow` gives the reciprocal power series. -/
@[simp]
theorem formalCpow_neg {ℓ : ℂ} (r : ℂ) {P : ℂ⟦X⟧} (hP : constantCoeff P = Complex.exp ℓ) :
    formalCpow ℓ (-r) P = (formalCpow ℓ r P)⁻¹ := by
  refine (PowerSeries.eq_inv_iff_mul_eq_one ?_).mpr ?_
  · rw [constantCoeff_formalCpow hP]
    exact Complex.exp_ne_zero _
  · rw [← formalCpow_add (-r) r hP, neg_add_cancel, formalCpow_zero]

/-- On `1 + X` with branch `ℓ = 0`, `formalCpow` reduces to `PowerSeries.binomialSeries ℂ r`. -/
@[simp]
theorem formalCpow_zero_one_add_X (r : ℂ) :
    formalCpow 0 r (1 + X) = PowerSeries.binomialSeries ℂ r := by
  rw [formalCpow_def, mul_zero, neg_zero, Complex.exp_zero, map_one, one_mul, one_mul,
    binomialPow_one_add_X]

/-- Shifting the branch parameter `ℓ` by `2πi` multiplies `formalCpow ℓ r P` by `cexp (2πir)`. -/
theorem formalCpow_add_two_pi_mul_I (ℓ r : ℂ) (P : ℂ⟦X⟧) :
    formalCpow (ℓ + 2 * π * Complex.I) r P =
      C (Complex.exp (2 * π * Complex.I * r)) * formalCpow ℓ r P := by
  have hexp_neg : Complex.exp (-(ℓ + 2 * π * Complex.I)) = Complex.exp (-ℓ) := by
    rw [neg_add, Complex.exp_add, Complex.exp_neg (2 * π * Complex.I), Complex.exp_two_pi_mul_I,
      inv_one, mul_one]
  have hexp_pos : Complex.exp (r * (ℓ + 2 * π * Complex.I)) =
      Complex.exp (2 * π * Complex.I * r) * Complex.exp (r * ℓ) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [formalCpow_def, formalCpow_def, hexp_neg, hexp_pos, map_mul, mul_assoc]

end PowerSeries
