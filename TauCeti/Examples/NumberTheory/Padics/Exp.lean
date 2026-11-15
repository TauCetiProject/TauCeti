/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.Algebraic.Defs
import TauCeti.NumberTheory.Padics.Complex.Basic
import TauCeti.NumberTheory.Padics.Complex.RootsOfUnity
import TauCeti.NumberTheory.Padics.Exp.Basic

/-!
# Worked examples and boundary checks for the `p`-adic exponential

Concrete norm calculations, boundary divergence witnesses, and rejection checks for
`TauCeti.PadicExp`:

* At `p = 3`, `3` lies strictly inside the `3`-adic exponential disc (`‖3‖ = 1 / 3 < 3 ^ (-1 / 2)`),
  so `‖exp (3 : ℂ_[3]) - 1‖ = 1 / 3`, `‖exp (3 : ℂ_[3])‖ = 1`, and `exp (3 : ℂ_[3]) ≠ 1`.
* At `p = 2`, `2` has norm `1 / 2 = 2 ^ (-1 / (2 - 1))`, lying on the boundary of the `2`-adic
  exponential disc; the exponential series diverges there and `exp (2 : ℂ_[2]) = 0`.
* More generally, for every prime `p` and every primitive `p`-th root of unity `ζ : ℂ_[p]`,
  `ζ - 1` has norm `p ^ (-1 / (p - 1))` and therefore sits on the boundary circle of
  `NormedSpace.expSeries ℂ_[p] ℂ_[p]`, where the exponential series diverges.
* At `x = 1`, `NormedSpace.exp (1 : ℂ_[p]) = 0` is algebraic over `ℚ` while `(-1) + 1 * 1 = 0`,
  showing that linear independence of `p`-adic logarithms of algebraic numbers requires the disc
  hypothesis `‖ℓ‖ < p ^ (-1 / (p - 1))`.
-/

open NormedSpace TauCeti

section OddPrimes

/-- At `p = 3`, `3` lies inside the `3`-adic exponential disc and `‖exp 3 - 1‖ = 1 / 3`. -/
example : ‖NormedSpace.exp (3 : ℂ_[3]) - 1‖ = 1 / 3 := by
  have h3 : ‖((3 : ℕ) : ℂ_[3])‖ < (3 : ℝ) ^ (-((3 : ℝ) - 1)⁻¹) :=
    (PadicExp.norm_natCast_prime_lt_iff (p := 3) (L := ℂ_[3])).mpr (by decide)
  have hnorm : ‖(3 : ℂ_[3])‖ = 1 / 3 := by
    simpa [one_div] using PadicComplex.norm_p 3
  rw [PadicExp.norm_exp_sub_one (p := 3) (by simpa using h3), hnorm]

/-- At `p = 3`, `exp 3` lies on the unit sphere of `ℂ_[3]` and is distinct from `1`. -/
example : ‖NormedSpace.exp (3 : ℂ_[3])‖ = 1 ∧ NormedSpace.exp (3 : ℂ_[3]) ≠ 1 := by
  have h3 : ‖(3 : ℂ_[3])‖ < (3 : ℝ) ^ (-((3 : ℝ) - 1)⁻¹) := by
    simpa using (PadicExp.norm_natCast_prime_lt_iff (p := 3) (L := ℂ_[3])).mpr (by decide)
  exact ⟨PadicExp.norm_exp (p := 3) h3, (PadicExp.exp_eq_one_iff 3).not.mpr (by norm_num)⟩

/-- For every odd prime `p`, the prime `p` lies in the `p`-adic exponential disc, the series
`∑ p ^ n / n !` converges in `ℂ_[p]`, `‖exp p - 1‖ = p⁻¹`, and `‖exp p‖ = 1`. -/
example {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Summable (fun n : ℕ => (p : ℂ_[p]) ^ n / (n.factorial : ℂ_[p])) ∧
      ‖NormedSpace.exp (p : ℂ_[p]) - 1‖ = (p : ℝ)⁻¹ ∧
      ‖NormedSpace.exp (p : ℂ_[p])‖ = 1 := by
  have hp : ‖(p : ℂ_[p])‖ < (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) :=
    PadicExp.norm_natCast_prime_lt_iff.mpr hp2
  exact ⟨(PadicExp.summable_pow_div_factorial_iff (p := p)).mpr hp,
    (PadicExp.norm_exp_sub_one hp).trans (PadicComplex.norm_p p),
    PadicExp.norm_exp hp⟩

end OddPrimes

section BoundaryAndRejection

/-- Boundary sharpness at `p = 2`: `‖(2 : ℂ_[2])‖ = 1 / 2` equals the radius `2 ^ (-1 / (2 - 1))`,
the exponential series at `2` is not summable, and `NormedSpace.exp (2 : ℂ_[2]) = 0`. -/
example :
    ‖(2 : ℂ_[2])‖ = 1 / 2 ∧
      ¬ Summable (fun n : ℕ => (2 : ℂ_[2]) ^ n / (n.factorial : ℂ_[2])) ∧
      NormedSpace.exp (2 : ℂ_[2]) = 0 := by
  have h2 : ‖(2 : ℂ_[2])‖ = (2 : ℝ) ^ (-((2 : ℝ) - 1)⁻¹) := PadicExp.norm_two_eq
  refine ⟨by norm_num [h2], PadicExp.not_summable_pow_div_factorial (p := 2) h2.ge,
    PadicExp.exp_eq_zero_of_le_norm (p := 2) h2.ge⟩

/-- For every prime `p` and every primitive `p`-th root of unity `ζ : ℂ_[p]`, `ζ - 1` lies on the
boundary circle of radius `p ^ (-1 / (p - 1))`, so the exponential series at `ζ - 1` diverges and
`NormedSpace.exp (ζ - 1) = 0`. -/
example {p : ℕ} [Fact p.Prime] {ζ : ℂ_[p]} (hζ : IsPrimitiveRoot ζ p) :
    ‖ζ - 1‖ = (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ∧
      ¬ Summable (fun n : ℕ => (ζ - 1) ^ n / (n.factorial : ℂ_[p])) ∧
      NormedSpace.exp (ζ - 1) = 0 := by
  have hnorm : ‖ζ - 1‖ = (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) := by
    simpa [neg_div, one_div] using hζ.norm_sub_one_padicComplex
  exact ⟨hnorm, PadicExp.not_summable_pow_div_factorial hnorm.ge,
    PadicExp.exp_eq_zero_of_le_norm hnorm.ge⟩

/-- Rejection check for the disc hypothesis: at `ℓ = 1` in `ℂ_[p]`, `NormedSpace.exp ℓ = 0` is
algebraic over `ℚ`, yet the nontrivial `ℚ`-linear relation `-1 + 1 * ℓ = 0` holds. -/
example (p : ℕ) [hp : Fact p.Prime] :
    NormedSpace.exp (1 : ℂ_[p]) = 0 ∧
      IsAlgebraic ℚ (NormedSpace.exp (1 : ℂ_[p])) ∧
      (-1 : ℂ_[p]) + 1 * (1 : ℂ_[p]) = 0 := by
  have h1 : (p : ℝ) ^ (-((p : ℝ) - 1)⁻¹) ≤ ‖(1 : ℂ_[p])‖ := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
    rw [norm_one]
    exact Real.rpow_le_one_of_one_le_of_nonpos hp1
      (neg_nonpos.mpr (inv_nonneg.mpr (sub_nonneg.mpr hp1)))
  have hexp : NormedSpace.exp (1 : ℂ_[p]) = 0 := PadicExp.exp_eq_zero_of_le_norm h1
  exact ⟨hexp, hexp ▸ isAlgebraic_zero, by ring⟩

end BoundaryAndRejection
