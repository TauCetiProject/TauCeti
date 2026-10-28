/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Exponential.Norm
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.NumberTheory.Padics.Distribution.Amice.Norm
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergence of integral formal exponentials

If a ring map to a normed field over `ℚ_p` takes values in the closed unit ball, the formal
exponential of a formal group mapped along it converges absolutely for
`‖t‖ < p ^ (-1 / (p - 1))`, including for `p = 2`. Summability of the series itself additionally
requires completeness of the field. In particular, this applies to formal groups over `ℤ_p`.
The factorial denominator estimate and the existing lower bound for factorial norms give a
geometric majorant on this disc.
This is the disc on which the exponential can be used to invert an evaluated formal logarithm; the
exponential need not converge throughout the open unit disc.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4–6.
-/

public section

namespace FormalGroup

-- Retain the caller's rational algebra structure, which occurs in the formal exponential.
variable {p : ℕ} [hp : Fact p.Prime] {R K : Type*} [CommRing R]
  [NormedField K] [Algebra ℚ K] [NormedAlgebra ℚ_[p] K]
  (F : FormalGroup R) (f : R →+* K) (hf : ∀ a, ‖f a‖ ≤ 1)

include hf

/-- A geometric bound for formal exponential coefficients when the coefficient map takes values
in the closed unit ball. -/
theorem norm_coeff_exp_le (n : ℕ) :
    ‖PowerSeries.coeff n (F.map f).exp‖ ≤
      ((p : ℝ) ^ ((p - 1 : ℝ)⁻¹)) ^ n := by
  refine (F.norm_coeff_exp_le_inv_norm_factorial f hf n).trans ?_
  have hnorm : ‖(n.factorial : K)‖ = ‖(n.factorial : ℚ_[p])‖ := by
    simpa only [map_natCast] using norm_algebraMap' K (n.factorial : ℚ_[p])
  rw [hnorm]
  have h := inv_anti₀ (pow_pos (TauCeti.amiceRadius_pos (p := p) 0) n)
    (TauCeti.amiceRadius_pow_le_norm_factorial (p := p) 0 n)
  simpa only [TauCeti.amiceRadius_def, pow_zero, mul_one, Nat.div_one, one_div,
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ p), inv_pow, inv_inv] using h

/-- The formal exponential of an integral formal group converges absolutely over any normed
field over `ℚ_p` on the standard p-adic exponential disc, including for `p = 2`. -/
theorem summable_norm_coeff_exp_mul_pow {t : K}
    (ht : ‖t‖ < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    Summable fun n : ℕ ↦
      ‖PowerSeries.coeff n (F.map f).exp * t ^ n‖ := by
  have hpos : 0 < (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _
  have ht' : (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) * ‖t‖ < 1 := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p)] at ht
    have h := mul_lt_mul_of_pos_left ht hpos
    simpa [hpos.ne'] using h
  refine (summable_geometric_of_lt_one (mul_nonneg hpos.le (norm_nonneg t)) ht').of_nonneg_of_le
    (fun n ↦ norm_nonneg _) fun n ↦ ?_
  rw [norm_mul, norm_pow, mul_pow]
  exact mul_le_mul_of_nonneg_right (F.norm_coeff_exp_le (p := p) f hf n) (by positivity)

/-- The exponential series of an integral formal group is summable in any complete normed field
over `ℚ_p` on its p-adic convergence disc. -/
theorem summable_coeff_exp_mul_pow [CompleteSpace K] {t : K}
    (ht : ‖t‖ < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    Summable fun n : ℕ ↦
      PowerSeries.coeff n (F.map f).exp * t ^ n :=
  (F.summable_norm_coeff_exp_mul_pow (p := p) f hf ht).of_norm

end FormalGroup
