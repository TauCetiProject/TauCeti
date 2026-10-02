/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EichlerIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.ExpDecay

/-!
# The Eichler integral as an integral

The `(n + 1)`-fold Eichler integral `E_{n+1} f = ∑ (h / m)ⁿ⁺¹ aₘ qᵐ` of
`TauCeti.NumberTheory.ModularForms.EichlerIntegral.Basic` is defined by its `q`-expansion. When
the constant term `a₀` of `f` vanishes, it is also the integral

`E_{n+1} f (τ) = (-2πi)ⁿ⁺¹ / n! · ∫_τ^{i∞} f(z) (z - τ)ⁿ dz`

along the vertical ray from `τ` to `i∞`, parametrized as `z = τ + i t` for `t > 0`. Along the
ray `qᵐ` decays like `e^{-2πmt/h}`, so termwise this is the Gamma integral
`∫₀^∞ tⁿ e^{-ct} dt = n! / cⁿ⁺¹` at `c = 2πm / h`.

For a cusp form `f` of weight `k = n + 2`, the integrand `f(z) (z - τ)ⁿ dz` is the period integrand
of `f` against the binary form `(X - τY)ⁿ`, so this representation ties the Eichler integral to
the periods of `f`. Substituting `z ↦ γz` in it shows that `E_{k-1} f` transforms in weight `2 - k`
up to a polynomial in `τ` of degree at most `k - 2` whose coefficients are periods of `f`; that
transformation law is not part of this file.

## Main results

* `TauCeti.eichlerIntegral_eq_integral`: the integral representation, for a holomorphic periodic
  function bounded at `i∞` with vanishing constant term.
* `TauCeti.CuspFormClass.eichlerIntegral_eq_integral`: the integral representation for a cusp
  form.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §8.2.
* W. Kohnen, D. Zagier, *Modular forms with rational periods*, in *Modular forms (Durham, 1983)*,
  Ellis Horwood, 1984, 197–249.
-/

public noncomputable section

open Complex Filter Function MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real Nat Manifold

local notation "𝕢" => Function.Periodic.qParam

namespace TauCeti

variable {h : ℝ} {f : ℍ → ℂ}

/-- Along the vertical ray from `τ`, the `q`-parameter decays exponentially:
`𝕢(τ + it)ᵐ = 𝕢(τ)ᵐ e^{-2πmt/h}`. -/
private lemma qParam_add_mul_I_pow (h : ℝ) (τ : ℂ) (t : ℝ) (m : ℕ) :
    𝕢 h (τ + t * I) ^ m = 𝕢 h τ ^ m * (Real.exp (-(2 * π * m / h * t)) : ℂ) := by
  simp only [Periodic.qParam, ← Complex.exp_nat_mul, ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- The `m`-th term of the `q`-expansion of `f(z) (z - τ)ⁿ dz` along the vertical ray from `τ`,
with coefficient `A = aₘ 𝕢(τ)ᵐ`, is integrable. Its integral is `n! / (-2πi)ⁿ⁺¹` times the `m`-th
term `(h / m)ⁿ⁺¹ A` of the Eichler series, and its `L¹`-norm is `n! / (2π)ⁿ⁺¹` times the norm of
that term. -/
private lemma integrable_and_integral_rayTerm (hh : 0 < h) (n : ℕ) {m : ℕ} (hm : 0 < m) (A : ℂ) :
    Integrable (fun t : ℝ ↦ A * I ^ (n + 1) * ((t ^ n * Real.exp (-(2 * π * m / h * t)) : ℝ) : ℂ))
        (volume.restrict (Ioi 0)) ∧
      ∫ t in Ioi (0 : ℝ), A * I ^ (n + 1) * ((t ^ n * Real.exp (-(2 * π * m / h * t)) : ℝ) : ℂ) =
        n ! / (-2 * π * I) ^ (n + 1) * (((h : ℂ) / m) ^ (n + 1) * A) ∧
      ∫ t in Ioi (0 : ℝ),
          ‖A * I ^ (n + 1) * ((t ^ n * Real.exp (-(2 * π * m / h * t)) : ℝ) : ℂ)‖ =
        n ! / (2 * π) ^ (n + 1) * ‖((h : ℂ) / m) ^ (n + 1) * A‖ := by
  have hcm : 0 < 2 * π * m / h := div_pos (by positivity) hh
  have hint := integrableOn_pow_mul_exp_neg_mul_Ioi n hcm
  have hval := integral_pow_mul_exp_neg_mul_Ioi n hcm
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hh' : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  refine ⟨hint.ofReal.const_mul _, ?_, ?_⟩
  · rw [integral_const_mul, integral_complex_ofReal, hval]
    have hI : -2 * π * I * I = 2 * π := by
      rw [mul_assoc, I_mul_I]
      ring
    have hkey : ((h : ℂ) / m) ^ (n + 1) =
        ((-2 * π * I) ^ (n + 1) * I ^ (n + 1)) / (2 * π * m / h) ^ (n + 1) := by
      rw [← mul_pow, ← div_pow, hI]
      congr 1
      field_simp
    rw [hkey]
    push_cast
    field_simp
  · rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t ↦ ‖A * I ^ (n + 1)‖ *
      (t ^ n * Real.exp (-(2 * π * m / h * t)))) fun t ht ↦ by
        rw [norm_mul (A * I ^ (n + 1)), norm_real,
          Real.norm_of_nonneg (mul_nonneg (pow_nonneg (le_of_lt ht) n) (Real.exp_pos _).le)]]
    rw [integral_const_mul, hval]
    simp only [norm_mul, norm_pow, norm_div, norm_real, Complex.norm_natCast, norm_I, one_pow,
      mul_one, Real.norm_of_nonneg hh.le]
    have hmh : 2 * π * m / h * (h / m) = 2 * π := by
      field_simp [hh.ne', (Nat.cast_pos.mpr hm).ne']
    rw [← hmh, mul_pow]
    field_simp

/-- **The Eichler integral as an integral**: if `f` is holomorphic, `h`-periodic and bounded at
`i∞` with vanishing constant term `a₀`, then

`E_{n+1} f (τ) = (-2πi)ⁿ⁺¹ / n! · ∫_τ^{i∞} f(z) (z - τ)ⁿ dz`,

the integral taken along the vertical ray `z = τ + i t`, `t > 0`. -/
theorem eichlerIntegral_eq_integral (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (h₀ : (qExpansion h f).coeff 0 = 0)
    (n : ℕ) (τ : ℍ) :
    eichlerIntegral h (n + 1) f τ = (-2 * π * I) ^ (n + 1) / n ! *
      ∫ t in Ioi (0 : ℝ), f (ofComplex (τ + t * I)) * (t * I) ^ n * I := by
  set a : ℕ → ℂ := fun m ↦ (qExpansion h f).coeff m
  have hc : (n ! : ℂ) / (-2 * π * I) ^ (n + 1) ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
      (pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero]))
  -- The `m`-th term of the `q`-expansion of the integrand along the ray.
  set F : ℕ → ℝ → ℂ := fun m t ↦ a m * 𝕢 h τ ^ m * I ^ (n + 1) *
    ((t ^ n * Real.exp (-(2 * π * m / h * t)) : ℝ) : ℂ)
  -- The terms of the Eichler series.
  set E : ℕ → ℂ := fun m ↦ ((h : ℂ) / m) ^ (n + 1) * (a m * 𝕢 h τ ^ m)
  have hE : HasSum E (eichlerIntegral h (n + 1) f τ) := by
    simpa only [E, mul_assoc] using hasSum_eichlerIntegral hh hfper hfhol hfbdd (n + 1) τ
  have hF (m : ℕ) : Integrable (F m) (volume.restrict (Ioi 0)) ∧
      ∫ t in Ioi (0 : ℝ), F m t = n ! / (-2 * π * I) ^ (n + 1) * E m ∧
      ∫ t in Ioi (0 : ℝ), ‖F m t‖ = n ! / (2 * π) ^ (n + 1) * ‖E m‖ := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [F, E, a, h₀]
    · exact integrable_and_integral_rayTerm hh n hm _
  -- Along the ray, the integrand is the sum of the `F m`.
  have hsum : ∀ t ∈ Ioi (0 : ℝ),
      f (ofComplex (τ + t * I)) * (t * I) ^ n * I = ∑' m, F m t := fun t ht ↦ by
    have him : 0 < (τ + t * I : ℂ).im := by simpa using add_pos τ.im_pos ht
    have hq := (hasSum_qExpansion hh hfper hfhol hfbdd (ofComplex (τ + t * I))).mul_right
      ((t * I) ^ n * I)
    rw [← mul_assoc] at hq
    refine (hq.tsum_eq.symm.trans (tsum_congr fun m ↦ ?_))
    simp only [ofComplex_apply_of_im_pos him, smul_eq_mul, qParam_add_mul_I_pow, F, a]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsum,
    ← integral_tsum_of_summable_integral_norm (fun m ↦ (hF m).1)
      (by simpa only [(hF _).2.2] using hE.summable.norm.mul_left _)]
  simp only [fun m ↦ (hF m).2.1]
  rw [tsum_mul_left, hE.tsum_eq, ← mul_assoc, ← inv_div, inv_mul_cancel₀ hc, one_mul]

/-- **The Eichler integral of a cusp form as an integral**: for a cusp form `f`,

`E_{n+1} f (τ) = (-2πi)ⁿ⁺¹ / n! · ∫_τ^{i∞} f(z) (z - τ)ⁿ dz`,

the integral taken along the vertical ray `z = τ + i t`, `t > 0`. For a cusp form of weight
`k ≥ 2` and `n = k - 2`, this is the classical integral formula for its Eichler integral. -/
theorem CuspFormClass.eichlerIntegral_eq_integral {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [CuspFormClass F Γ k] (f : F) (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (n : ℕ) (τ : ℍ) :
    eichlerIntegral h (n + 1) f τ = (-2 * π * I) ^ (n + 1) / n ! *
      ∫ t in Ioi (0 : ℝ), f (ofComplex (τ + t * I)) * (t * I) ^ n * I := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  exact TauCeti.eichlerIntegral_eq_integral hh
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) (_root_.CuspFormClass.qExpansion_coeff_zero f hh hΓ) n τ

end TauCeti
