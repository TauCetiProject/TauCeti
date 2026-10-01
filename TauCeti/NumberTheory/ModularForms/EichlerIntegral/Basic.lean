/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.Derivative
public import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Complex.LocallyUniformLimit
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The Eichler integral of a cusp form

For a function `f` on `ℍ` with `q`-expansion `f = ∑ aₘ qᵐ` at width `h` (where
`q = exp (2πiτ / h)`), the `n`-fold **Eichler integral** is the termwise antiderivative

`E_n f = ∑ (h / m)ⁿ aₘ qᵐ`

for the normalized derivative `D = (2πi)⁻¹ d/dτ` of `Derivative.normalizedDerivOfComplex`, which
acts on `qᵐ` as multiplication by `m / h`. For `n ≥ 1` the constant term is dropped (the
coefficient `(h / 0)ⁿ` is `0`), so `E_n f` vanishes at `i∞`, and differentiating `n` times returns
`f` minus its constant term. For a cusp form `f` of weight `k ≥ 2` the function `E_{k-1} f` is the
classical Eichler integral of `f`, a `(k - 1)`-fold antiderivative: `D^{k-1} E_{k-1} f = f`.
Classically, the failure of the Eichler integral to transform in weight `2 - k` is a polynomial
whose coefficients are periods of `f`, which is how vanishing periods force a cusp form to vanish
(the injectivity of the Eichler–Shimura period map); that transformation law is not part of this
file.

## Main definitions

* `TauCeti.eichlerIntegral h n f`: the `n`-fold Eichler integral `∑ (h / m)ⁿ aₘ qᵐ`.

## Main results

* `TauCeti.eichlerIntegral_zero`, `TauCeti.eichlerIntegral_add`,
  `TauCeti.eichlerIntegral_smul`: linearity under the appropriate analytic hypotheses.
* `TauCeti.hasSum_eichlerIntegral`: the defining series converges to
  `eichlerIntegral h n f` at every point of `ℍ`.
* `TauCeti.qExpansion_eichlerIntegral_coeff`: the `q`-expansion coefficients of
  `eichlerIntegral h n f` are `(h / m)ⁿ aₘ`.
* `TauCeti.mdifferentiable_eichlerIntegral`: the Eichler integral is holomorphic on `ℍ`.
* `TauCeti.isZeroAtImInfty_eichlerIntegral`: for `n ≥ 1` it vanishes at `i∞`.
* `TauCeti.normalizedDerivOfComplex_eichlerIntegral_add_two`,
  `TauCeti.normalizedDerivOfComplex_eichlerIntegral_one`: `D E_{n+2} f = E_{n+1} f` and
  `D E_1 f = f - a₀`.
* `TauCeti.iterate_normalizedDerivOfComplex_eichlerIntegral`: `D^{n+1} E_{n+1} f = f - a₀`.
* `TauCeti.CuspFormClass.iterate_normalizedDerivOfComplex_eichlerIntegral`: for a cusp form,
  `D^{n+1} E_{n+1} f = f`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §8.2.
* M. Eichler, *Eine Verallgemeinerung der Abelschen Integrale*, Math. Z. **67** (1957), 267–298.
* The AINTLIB `LeanModularForms` project, `ModularSymbols/EichlerInjective.lean`
  (`eichlerCoeff`, `bol_iterated_eichler`), whose coefficient normalization `aₘ / m^{k-1}` is the
  width-one case of the one used here.
-/

public noncomputable section

open Complex Filter Function
open UpperHalfPlane hiding I
open scoped Real Topology Manifold Derivative

local notation "𝕢" => Function.Periodic.qParam

namespace TauCeti

variable {h : ℝ} {f : ℍ → ℂ}

/-- The `n`-fold **Eichler integral** of `f : ℍ → ℂ` at width `h`: the series
`∑ (h / m)ⁿ aₘ qᵐ`, where `aₘ` are the coefficients of `qExpansion h f` and `q = 𝕢 h τ`.
It is the termwise `n`-fold antiderivative of the `q`-expansion of `f` for the normalized
derivative `D = (2πi)⁻¹ d/dτ`, with the constant term dropped when `n ≥ 1`. For a cusp form of
weight `k ≥ 2`, `eichlerIntegral h (k - 1) f` is the classical Eichler integral of `f`. -/
def eichlerIntegral (h : ℝ) (n : ℕ) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ∑' m : ℕ, ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m * 𝕢 h τ ^ m

/-- A term of the Eichler series is bounded by `hⁿ` times the corresponding term of the
`q`-expansion: the rescaling factor `h / m` has norm at most `h` (it is `0` at `m = 0`). -/
private lemma norm_eichlerTerm_le (hh : 0 < h) (n m : ℕ) (a q : ℂ) :
    ‖((h : ℂ) / m) ^ n * a * q ^ m‖ ≤ h ^ n * (‖a‖ * ‖q‖ ^ m) := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, ← mul_assoc]
  gcongr
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hh.le]
  · rw [norm_div, Complex.norm_real, Complex.norm_natCast, Real.norm_of_nonneg hh.le]
    exact div_le_self hh.le (by exact_mod_cast hm)

/-- **The defining series of the Eichler integral converges** at every point of `ℍ`. -/
theorem hasSum_eichlerIntegral (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (n : ℕ) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m * 𝕢 h τ ^ m)
      (eichlerIntegral h n f τ) := by
  have hs := (hasSum_qExpansion_of_norm_lt hh hfper hfhol hfbdd
    (q := (‖𝕢 h τ‖ : ℂ)) (by simpa using Periodic.norm_qParam_lt_one hh τ.im_pos)).summable.norm
  simp only [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at hs
  exact (Summable.of_norm_bounded (hs.mul_left (h ^ n))
    fun m ↦ norm_eichlerTerm_le hh n m _ _).hasSum

/-- The Eichler integral of the zero function is zero. -/
@[simp]
theorem eichlerIntegral_zero (h : ℝ) (n : ℕ) : eichlerIntegral h n 0 = 0 := by
  ext τ
  simp [eichlerIntegral, qExpansion_zero]

/-- The Eichler integral commutes with complex scalar multiplication when the cusp function
is analytic at zero. -/
theorem eichlerIntegral_smul (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) (a : ℂ) :
    eichlerIntegral h n (a • f) = a • eichlerIntegral h n f := by
  ext τ
  simp only [eichlerIntegral, qExpansion_smul hf, PowerSeries.coeff_smul, smul_eq_mul,
    Pi.smul_apply]
  simp_rw [mul_left_comm (((h : ℂ) / _) ^ n) a, mul_assoc a]
  rw [tsum_mul_left]

/-- The Eichler integral commutes with negation when the cusp function is analytic at zero. -/
theorem eichlerIntegral_neg (hf : AnalyticAt ℂ (cuspFunction h f) 0) (n : ℕ) :
    eichlerIntegral h n (-f) = -eichlerIntegral h n f := by
  simpa using eichlerIntegral_smul hf n (-1)

/-- The Eichler integral is additive on holomorphic periodic functions bounded at `i∞`. -/
theorem eichlerIntegral_add {g : ℍ → ℂ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (hgper : Periodic (g ∘ ofComplex) h) (hghol : MDiff g) (hgbdd : IsBoundedAtImInfty g)
    (n : ℕ) : eichlerIntegral h n (f + g) = eichlerIntegral h n f + eichlerIntegral h n g := by
  ext τ
  have hf := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  have hg := analyticAt_cuspFunction_zero hh hgper hghol hgbdd
  simpa only [eichlerIntegral, qExpansion_add hf hg, map_add, mul_add, add_mul, Pi.add_apply]
    using ((hasSum_eichlerIntegral hh hfper hfhol hfbdd n τ).add
      (hasSum_eichlerIntegral hh hgper hghol hgbdd n τ)).tsum_eq

/-- The Eichler integral commutes with subtraction on holomorphic periodic functions bounded
at `i∞`. -/
theorem eichlerIntegral_sub {g : ℍ → ℂ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (hgper : Periodic (g ∘ ofComplex) h) (hghol : MDiff g) (hgbdd : IsBoundedAtImInfty g)
    (n : ℕ) : eichlerIntegral h n (f - g) = eichlerIntegral h n f - eichlerIntegral h n g := by
  ext τ
  have hf := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  have hg := analyticAt_cuspFunction_zero hh hgper hghol hgbdd
  simpa only [eichlerIntegral, qExpansion_sub hf hg, map_sub, mul_sub, sub_mul, Pi.sub_apply]
    using ((hasSum_eichlerIntegral hh hfper hfhol hfbdd n τ).sub
      (hasSum_eichlerIntegral hh hgper hghol hgbdd n τ)).tsum_eq

/-- The `0`-fold Eichler integral is the function itself. -/
@[simp]
theorem eichlerIntegral_order_zero (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) : eichlerIntegral h 0 f = f :=
  funext fun τ ↦ (hasSum_eichlerIntegral hh hfper hfhol hfbdd 0 τ).unique (by
    simpa using hasSum_qExpansion hh hfper hfhol hfbdd τ)

/-- The Eichler integral has the same period `h` as the `q`-parameter. -/
theorem periodic_eichlerIntegral_comp_ofComplex (hh : h ≠ 0) (n : ℕ) :
    Periodic (eichlerIntegral h n f ∘ ofComplex) h :=
  periodic_comp_ofComplex fun τ ↦ by
    simp only [eichlerIntegral, coe_vadd, Periodic.qParam, mul_add, add_div,
      mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hh), Complex.exp_add,
      Complex.exp_two_pi_mul_I, one_mul]

/-- On a half-plane `ε < im w` the terms of the Eichler series are dominated by a summable
sequence independent of `w`. -/
private lemma norm_eichlerTerm_le_of_lt_im (hh : 0 < h) (n m : ℕ) (a : ℂ) {ε : ℝ} {w : ℂ}
    (hw : ε < w.im) :
    ‖((h : ℂ) / m) ^ n * a * 𝕢 h w ^ m‖ ≤ h ^ n * (‖a‖ * Real.exp (-2 * π * ε / h) ^ m) := by
  refine (norm_eichlerTerm_le hh n m a _).trans ?_
  gcongr
  exact ((Periodic.norm_qParam_lt_iff hh ε w).mpr hw).le

/-- The Eichler series, as a function on `ℂ`, is differentiable on the upper half-plane, and its
derivative is the termwise derivative. -/
private lemma eichlerSeries_hasSum_deriv (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (n : ℕ) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ
        (fun w : ℂ ↦ ∑' m : ℕ, ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m * 𝕢 h w ^ m) z ∧
      HasSum (fun m : ℕ ↦ ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m *
          (2 * π * I * m / h * 𝕢 h z ^ m))
        (deriv (fun w : ℂ ↦ ∑' m : ℕ, ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m *
          𝕢 h w ^ m) z) := by
  set ε := z.im / 2
  have hε : 0 < ε := half_pos hz
  have hU : IsOpen {w : ℂ | ε < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ {w : ℂ | ε < w.im} := half_lt_self hz
  have hr : Real.exp (-2 * π * ε / h) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) hh)
  have hu := (hasSum_qExpansion_of_norm_lt hh hfper hfhol hfbdd
    (q := (Real.exp (-2 * π * ε / h) : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      using hr)).summable.norm
  simp only [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hu
  have hu := hu.mul_left (h ^ n)
  have hdiff (m : ℕ) : DifferentiableOn ℂ
      (fun w : ℂ ↦ ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m * 𝕢 h w ^ m)
      {w : ℂ | ε < w.im} :=
    ((Periodic.differentiable_qParam.pow m).const_mul _).differentiableOn
  have hle (m : ℕ) (w : ℂ) (hw : w ∈ {w : ℂ | ε < w.im}) :=
    norm_eichlerTerm_le_of_lt_im hh n m ((qExpansion h f).coeff m) hw
  refine ⟨(differentiableOn_tsum_of_summable_norm hu hdiff hU hle).differentiableAt
    (hU.mem_nhds hzU), ?_⟩
  convert hasSum_deriv_of_summable_norm hu hdiff hU hle hzU using 2 with m
  have hpow : HasDerivAt (fun w ↦ 𝕢 h w ^ m) (2 * π * I * m / h * 𝕢 h z ^ m) z := by
    convert (TauCeti.Periodic.hasDerivAt_qParam h z).pow m using 1
    rcases m with _ | m
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      push_cast
      ring
  exact ((hpow.const_mul _).deriv).symm

/-- The Eichler integral, read on `ℂ` through `ofComplex`, agrees with its defining series near
every point of the upper half-plane. -/
private lemma eichlerIntegral_comp_ofComplex_eventuallyEq (n : ℕ) (τ : ℍ) :
    eichlerIntegral h n f ∘ ofComplex =ᶠ[𝓝 (τ : ℂ)]
      fun w : ℂ ↦ ∑' m : ℕ, ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m * 𝕢 h w ^ m := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
  simp [eichlerIntegral, ofComplex_apply_of_im_pos hw]

/-- **The Eichler integral is holomorphic** on `ℍ`. -/
theorem mdifferentiable_eichlerIntegral (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (n : ℕ) :
    MDiff (eichlerIntegral h n f) := fun τ ↦
  mdifferentiableAt_iff.mpr <| (eichlerSeries_hasSum_deriv hh hfper hfhol hfbdd n
    τ.im_pos).1.congr_of_eventuallyEq (eichlerIntegral_comp_ofComplex_eventuallyEq n τ)

/-- **The Eichler integral vanishes at `i∞`** once at least one antiderivative is taken: its
`q`-expansion has no constant term. -/
theorem isZeroAtImInfty_eichlerIntegral (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (n : ℕ) :
    IsZeroAtImInfty (eichlerIntegral h (n + 1) f) := by
  simpa [IsZeroAtImInfty, ZeroAtFilter] using tendsto_atImInfty_of_hasSum_qExpansion hh
    (c := fun m ↦ ((h : ℂ) / m) ^ (n + 1) * (qExpansion h f).coeff m)
    (by simpa using hasSum_eichlerIntegral hh hfper hfhol hfbdd (n + 1))

/-- **The `q`-expansion of the Eichler integral**: its `m`-th coefficient is `(h / m)ⁿ aₘ`. -/
@[simp]
theorem qExpansion_eichlerIntegral_coeff (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (n m : ℕ) :
    (qExpansion h (eichlerIntegral h n f)).coeff m =
      ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m := by
  have hE : ∀ τ : ℍ, HasSum
      (fun m : ℕ ↦ (((h : ℂ) / m) ^ n * (qExpansion h f).coeff m) • 𝕢 h τ ^ m)
      (eichlerIntegral h n f τ) := by
    simpa using hasSum_eichlerIntegral hh hfper hfhol hfbdd n
  exact (UpperHalfPlane.qExpansion_coeff_unique hh
    (analyticAt_cuspFunction_zero hh (periodic_eichlerIntegral_comp_ofComplex hh.ne' n)
      (mdifferentiable_eichlerIntegral hh hfper hfhol hfbdd n)
      (isBoundedAtImInfty_of_hasSum_qExpansion hh hE)) hE m).symm

/-- The normalized derivative acts on the Eichler series termwise, as multiplication of the
`m`-th term by `m / h`. -/
private lemma hasSum_normalizedDerivOfComplex_eichlerIntegral (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (n : ℕ) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (m / h) * ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m * 𝕢 h τ ^ m)
      (D (eichlerIntegral h n f) τ) := by
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [Derivative.normalizedDerivOfComplex,
    (eichlerIntegral_comp_ofComplex_eventuallyEq n τ).deriv_eq]
  convert (eichlerSeries_hasSum_deriv hh hfper hfhol hfbdd n τ.im_pos).2.mul_left
    (2 * π * I)⁻¹ using 2 with m
  field_simp

/-- The rescaling factors of consecutive Eichler integrals differ by the factor `m / h` that
`D` produces, away from the constant term. -/
private lemma natCast_div_mul_div_natCast_pow_succ (hh : h ≠ 0) {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    (m / h) * ((h : ℂ) / m) ^ (n + 1) = ((h : ℂ) / m) ^ n := by
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [pow_succ]
  field_simp

/-- **Differentiating an Eichler integral of order at least two** lowers the order by one:
`D E_{n+2} f = E_{n+1} f`. -/
theorem normalizedDerivOfComplex_eichlerIntegral_add_two (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (n : ℕ) : D (eichlerIntegral h (n + 2) f) = eichlerIntegral h (n + 1) f := by
  funext τ
  refine (hasSum_normalizedDerivOfComplex_eichlerIntegral hh hfper hfhol hfbdd (n + 2) τ).unique ?_
  convert hasSum_eichlerIntegral hh hfper hfhol hfbdd (n + 1) τ using 2 with m
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [natCast_div_mul_div_natCast_pow_succ hh.ne' hm]

/-- **Differentiating the first Eichler integral** returns the function minus its constant term:
`D E_1 f = f - a₀`. -/
theorem normalizedDerivOfComplex_eichlerIntegral_one (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    D (eichlerIntegral h 1 f) = fun τ ↦ f τ - (qExpansion h f).coeff 0 := by
  funext τ
  refine (hasSum_normalizedDerivOfComplex_eichlerIntegral hh hfper hfhol hfbdd 1 τ).unique ?_
  convert (hasSum_qExpansion hh hfper hfhol hfbdd τ).sub
    (hasSum_ite_eq 0 ((qExpansion h f).coeff 0)) using 2 with m
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [natCast_div_mul_div_natCast_pow_succ hh.ne' hm]
    simp [hm]

/-- **The Eichler integral is an iterated antiderivative**: differentiating `E_{n+1} f` exactly
`n + 1` times with the normalized derivative `D` returns `f` minus its constant term. -/
theorem iterate_normalizedDerivOfComplex_eichlerIntegral (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (n : ℕ) :
    D^[n + 1] (eichlerIntegral h (n + 1) f) = fun τ ↦ f τ - (qExpansion h f).coeff 0 := by
  induction n with
  | zero => exact normalizedDerivOfComplex_eichlerIntegral_one hh hfper hfhol hfbdd
  | succ n ih =>
    rw [iterate_succ_apply, normalizedDerivOfComplex_eichlerIntegral_add_two hh hfper hfhol hfbdd,
      ih]

/-- **The Eichler integral of a cusp form is an iterated antiderivative**:
`D^{n+1} E_{n+1} f = f`. For a cusp form of weight `k ≥ 2` and `n + 1 = k - 1`, this recovers `f`
from its Eichler integral. -/
theorem CuspFormClass.iterate_normalizedDerivOfComplex_eichlerIntegral {F : Type*}
    [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [CuspFormClass F Γ k] (f : F)
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (n : ℕ) :
    D^[n + 1] (eichlerIntegral h (n + 1) f) = f := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  rw [TauCeti.iterate_normalizedDerivOfComplex_eichlerIntegral hh
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f), _root_.CuspFormClass.qExpansion_coeff_zero f hh hΓ]
  simp

end TauCeti
