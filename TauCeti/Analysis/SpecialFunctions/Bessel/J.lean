/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Bessel's integral for `J₀`

This file proves Bessel's integral representation of the Bessel function of the first kind of
order zero,
`J₀(a) = (2π)⁻¹ ∫₀^{2π} e^{i a cos φ} dφ`,
for every complex `a`, where `J₀` is Mathlib's `Complex.besselJ 0`. The right side is the
average of the plane wave `e^{i a cos φ}` over all directions, so in polar coordinates it reduces
a plane integral of `e^{i r cos φ}` times a radial weight to a one-dimensional integral against
`J₀(r)`; this is how the representation DLMF 9.11.3 of the square of the Airy function is
derived. The formula is the case `n = 0` of Bessel's integrals DLMF 10.9.1.

## Main results

* `Complex.integral_exp_mul_cos_mul_I` — `∫_{-π}^{π} e^{i a cos θ} dθ = 2π J₀(a)`.
* `Complex.besselJ_zero_left_eq_integral` — `J₀(a) = (2π)⁻¹ ∫₀^{2π} e^{i a cos φ} dφ`.

## Implementation notes

The exponential series `e^{i a cos θ} = ∑ₖ (i a)ᵏ cosᵏ θ / k!` is integrated termwise over
`[-π, π]`, and `TauCeti.integral_cos_pow_mul_cexp` evaluates `∫_{-π}^{π} cosᵏ θ dθ`, which
vanishes for odd `k` and is `2π 4⁻ˡ (2l choose l)` for `k = 2 l`. The surviving terms are
`2π (-(a/2)²)ˡ / (l!)²`, those of the series `₀F₁(; 1; -(a/2)²)` through which Mathlib defines
`J₀(a)`.

## References

* *NIST Digital Library of Mathematical Functions*, 10.9.1, <https://dlmf.nist.gov/10.9.E1>.
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge University
  Press, 1944, §2.2.
-/

public section

noncomputable section

open scoped Nat Real

namespace Complex

/-- Termwise integration of the exponential series `e^{i a cos θ} = ∑ₖ (i a)ᵏ cosᵏ θ / k!` over
`[-π, π]`. -/
private theorem hasSum_integral_exp_mul_cos_mul_I (a : ℂ) :
    HasSum (fun k : ℕ => (a * I) ^ k / k ! * ∫ θ in -π..π, (Real.cos θ : ℂ) ^ k)
      (∫ θ in -π..π, exp (a * Real.cos θ * I)) := by
  simp_rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => ‖a‖ ^ k / k !)
    (fun k => by fun_prop) (fun k => MeasureTheory.ae_of_all _ fun θ _ => ?_)
    (MeasureTheory.ae_of_all _ fun _ _ => Real.summable_pow_div_factorial ‖a‖)
    intervalIntegrable_const (MeasureTheory.ae_of_all _ fun θ _ => ?_)
  · have hcos : ‖(Real.cos θ : ℂ)‖ ≤ 1 := by
      rw [norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one θ
    rw [norm_mul, norm_div, norm_pow, norm_mul, norm_I, mul_one, norm_natCast, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg _) hcos)
  · have h := NormedSpace.expSeries_div_hasSum_exp (a * Real.cos θ * I)
    rw [← exp_eq_exp_ℂ] at h
    convert h using 2 with k
    ring

/-- **Bessel's integral for `J₀`, symmetric form.** For every complex `a`,
`∫_{-π}^{π} e^{i a cos θ} dθ = 2π J₀(a)`. -/
theorem integral_exp_mul_cos_mul_I (a : ℂ) :
    ∫ θ in -π..π, exp (a * Real.cos θ * I) = 2 * π * besselJ 0 a := by
  have h := hasSum_integral_exp_mul_cos_mul_I a
  have hcos (k : ℕ) : ∫ θ in -π..π, (Real.cos θ : ℂ) ^ k =
      ∑ m ∈ Finset.range (k + 1),
        (1 / 2 : ℂ) ^ k * k.choose m * if 2 * (m : ℤ) - k = 0 then 2 * (π : ℂ) else 0 := by
    simpa using TauCeti.integral_cos_pow_mul_cexp k 0
  simp only [hcos] at h
  -- Only the even exponents `k = 2 l` contribute.
  have hz : ∀ k ∉ Set.range (fun l : ℕ => 2 * l), (a * I) ^ k / k ! *
      (∑ m ∈ Finset.range (k + 1),
        (1 / 2 : ℂ) ^ k * k.choose m * if 2 * (m : ℤ) - k = 0 then 2 * (π : ℂ) else 0) = 0 := by
    intro k hk
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun m _ => ?_)
    rw [ite_eq_right fun hm => hk ⟨m, by dsimp only; omega⟩, mul_zero]
  have hinj : Function.Injective fun l : ℕ => 2 * l := fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff hz] at h
  refine h.unique ?_
  -- At `k = 2 l` only `m = l` contributes, and the term is that of the series of `J₀(a)`.
  have hJ := (hasSum_regularizedHGFun (a := 0) (b := {(0 : ℂ) + 1}) (by simp)
    (-(a / 2) ^ 2)).mul_left (2 * (π : ℂ))
  rw [besselJ, cpow_zero, one_mul]
  convert hJ using 2 with l
  dsimp only [Function.comp_apply]
  rw [Finset.sum_eq_single l (fun m _ hm => by rw [ite_eq_right (by omega), mul_zero])
    (fun hl => absurd (Finset.mem_range.mpr (by omega)) hl), ite_eq_left (by push_cast; ring),
    regularizedHGFunCoeff_zero_singleton, zero_add, add_comm (1 : ℂ), Gamma_nat_eq_factorial,
    mul_pow, pow_mul I, I_sq]
  have hfac := Nat.choose_mul_factorial_mul_factorial (by omega : l ≤ 2 * l)
  rw [show 2 * l - l = l by omega] at hfac
  have hc : ((2 * l).choose l : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have h4 : (-(a / 2) ^ 2) ^ l = (-1) ^ l * (1 / 2 : ℂ) ^ (2 * l) * a ^ (2 * l) := by
    rw [neg_pow, ← pow_mul, div_eq_mul_one_div a, mul_pow]
    ring
  rw [← hfac, h4]
  push_cast
  field_simp

/-- **Bessel's integral for `J₀`.** For every complex `a`,
`J₀(a) = (2π)⁻¹ ∫₀^{2π} e^{i a cos θ} dθ`. -/
theorem besselJ_zero_left_eq_integral (a : ℂ) :
    besselJ 0 a = (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, exp (a * Real.cos θ * I) := by
  have hper : Function.Periodic (fun θ : ℝ => exp (a * Real.cos θ * I)) (2 * π) := fun θ => by
    simp only [Real.cos_add_two_pi]
  have h := hper.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at h
  rw [h, integral_exp_mul_cos_mul_I]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end Complex
