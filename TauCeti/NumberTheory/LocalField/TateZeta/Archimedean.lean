/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import TauCeti.Analysis.SpecialFunctions.Complex.ArchimedeanCharacter
public import TauCeti.MeasureTheory.Constructions.Polish.Units
public import TauCeti.MeasureTheory.Measure.Haar.ArchimedeanMultHaar
public import TauCeti.NumberTheory.LocalField.TateZeta.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.SingularWeight
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The local Tate zeta integral at the real and complex places

At an archimedean place the local field is `ℝ`, with normalized absolute value `|x|`, or `ℂ`, with
normalized absolute value `|z|_ℂ = z conj(z) = normSq z`. Following Tate and Kudla, the
multiplicative Haar measures are `dx / |x|` on `ℝˣ` and `2 dx dy / |z|_ℂ` on `ℂˣ`
(`TauCeti.realUnitsMultHaar`, `TauCeti.complexUnitsMultHaar`, the pullbacks to the units of
`TauCeti.realMultHaar` and `TauCeti.complexMultHaar`). For a Schwartz function `f` and a
quasi-character `χ` of exponent `r`, that is `‖χ(x)‖ = |x| ^ r`, this file studies

`z(s, χ; f) = ∫ f(x) χ(x) |x| ^ s d^×x`

(`TauCeti.TateZeta.localZetaIntegral`).

* **Convergence and holomorphy.** The integrand has norm `‖f(x)‖ |x| ^ (re s + r)`, which is
  `‖f(x)‖ ‖x‖ ^ (re s + r - 1)` against Lebesgue measure on `ℝ` and twice
  `‖f(z)‖ ‖z‖ ^ (2 (re s + r) - 2)` on `ℂ`. Both are integrable for `re s + r > 0`
  (`SchwartzMap.integrable_norm_rpow_mul_norm_of_neg_finrank_lt`), so `z(s, χ; f)` converges
  absolutely on that half-plane and is holomorphic there; for a unitary `χ` this is `re s > 0`.
  For fixed `s` in the half-plane, `f ↦ z(s, χ; f)` is a continuous linear functional on the
  Schwartz space.
* **Gaussians.** `z(s, 1; e^(-π x²)) = Γ_ℝ(s)` and `z(s, 1; e^(-2π |z|_ℂ)) = π Γ_ℂ(s)` on
  `re s > 0`, with Deligne's `Γ_ℝ(s) = π^(-s/2) Γ(s/2)` and `Γ_ℂ(s) = 2 (2π)^(-s) Γ(s)`.
* **Standard functions.** For `ω(x) = x^(-a)`, `a ∈ {0, 1}`, on `ℝˣ` (Kudla's normal form), the
  standard function `x^a e^(-π x²)` has zeta integral `Γ_ℝ(s) = L(s, ω)`. For
  `ω(z) = z^(-a) conj(z)^(-b)` on `ℂˣ`, the standard function `π⁻¹ z^a conj(z)^b e^(-2π |z|_ℂ)`
  has zeta integral `Γ_ℂ(s)`; when `min(a, b) = 0`, `ω` is in Kudla's normal form and this is
  the archimedean local factor `L(s, ω)`. Test functions of the wrong angular weight have zeta
  integral `0`.

## Main definitions

* `TauCeti.TateZeta.realLocalZetaCLM`, `TauCeti.TateZeta.complexLocalZetaCLM`: for `s` in the
  half-plane of absolute convergence, `f ↦ z(s, χ; f)` as a continuous linear functional on
  `𝓢(ℝ, ℂ)` and `𝓢(ℂ, ℂ)`.

## Main results

* `TauCeti.TateZeta.integrable_localZetaIntegrand_real`,
  `TauCeti.TateZeta.differentiableOn_localZetaIntegral_real`: absolute convergence and
  holomorphy at `ℝ` on `re s + r > 0`; `..._complex` likewise at `ℂ`.
* `TauCeti.TateZeta.localZetaIntegral_real_gaussian`: `z(s, 1; e^(-π x²)) = Γ_ℝ(s)`.
* `TauCeti.TateZeta.localZetaIntegral_complex_gaussian`: `z(s, 1; e^(-2π |z|_ℂ)) = π Γ_ℂ(s)`.
* `TauCeti.TateZeta.localZetaIntegral_realUnitsCharacter_standard`,
  `TauCeti.TateZeta.localZetaIntegral_complexUnitsCharacter_standard`: the standard functions
  have zeta integral `Γ_ℝ(s)` and `Γ_ℂ(s)`.
* `TauCeti.TateZeta.localZetaIntegral_complexUnitsCharacter_eq_zero_of_rotation`: a test function
  of angular weight `m` has zeta integral `0` against a character of angular weight `k ≠ -m`.

## Implementation notes

The complex place uses Tate's and Kudla's normalized absolute value `|z|_ℂ = normSq z` in the zeta
integral, as in `TauCeti.existsUnique_norm_coe_complexUnits_eq_rpow`; the parameters of
`TauCeti.complexUnitsCharacter s k`, `z ↦ |z| ^ s (z / |z|) ^ k`, use the usual modulus, so its
exponent for `|z|_ℂ` is `re s / 2`. The complex Gaussian integral is `π Γ_ℂ(s) = (2π)^(1-s) Γ(s)`
for the twice-Lebesgue additive measure (Kudla's normalization); the standard function carries
the factor `π⁻¹` so that its value is Deligne's `Γ_ℂ(s)`.

Every Haar measure on `ℝˣ` or `ℂˣ` is a positive multiple of the ones here, and
`TauCeti.TateZeta.localZetaIntegral_smul_measure` rescales the zeta integral accordingly.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels
  and A. Fröhlich, eds., *Algebraic Number Theory*, §2.4–2.5.
* S. S. Kudla, *Tate's thesis*, in J. Bernstein and S. Gelbart, eds., *An Introduction to the
  Langlands Program*, §3, (3.18)–(3.21).
* The convergence statement at the infinite places of a number field is
  `infiniteLocalIdelicZetaIntegral_integrable` and the Gaussian values are
  `infiniteLocalIdelicZFunction_standardGaussian` in `RiemannMasullo/Ch03_IdelicZeta/Sec3b.lean`
  and `RiemannMasullo/Ch03_IdelicZeta/Sec4.lean` of the Riemann–Masullo formalization
  (https://github.com/mccorvie/riemann-masullo). That development uses Bruhat's Schwartz–Bruhat
  space, the norm `‖z‖²` with angular weight `(z / ‖z‖) ^ k`, and the complex factor
  `(2π) ^ (-s) Γ(s) = Γ_ℂ(s) / 2`; this file uses Mathlib's Schwartz space and Deligne's
  `Γ_ℂ`.
-/

public section
noncomputable section

open MeasureTheory Measure Set Complex Filter Topology SchwartzMap
open scoped Real

namespace TauCeti

namespace TateZeta

/-! ### The real place -/

section Real

variable (f : 𝓢(ℝ, ℂ))

/-- The density of `dx / |x|` turns the weight `|y| ^ σ` into `‖y‖ ^ (σ - 1)` against Lebesgue
measure. -/
private theorem abs_inv_smul_mul_abs_rpow (c σ : ℝ) {y : ℝ} (hy : y ≠ 0) :
    |y|⁻¹ • (c * |y| ^ σ) = ‖y‖ ^ (σ - 1) * c := by
  rw [smul_eq_mul, Real.norm_eq_abs, Real.rpow_sub_one (abs_pos.2 hy).ne']
  field_simp

/-- For `σ > 0`, `‖f(y)‖ |y| ^ σ` is integrable against `dx / |x|`, since against Lebesgue measure
it is `‖f(y)‖ |y| ^ (σ - 1)` with `σ - 1 > -1`. -/
private theorem integrable_realMultHaar_norm_mul_rpow {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun y : ℝ ↦ ‖f y‖ * |y| ^ σ) realMultHaar := by
  rw [integrable_realMultHaar_iff]
  exact (f.integrable_norm_rpow_mul_norm_of_neg_finrank_lt volume (t := σ - 1)
    (by simp; linarith)).congr ((Measure.ae_ne volume 0).mono fun y hy ↦
      (abs_inv_smul_mul_abs_rpow _ σ hy).symm)

/-- `∫ ‖f(y)‖ |y| ^ σ dy / |y| = ∫ ‖y‖ ^ (σ - 1) ‖f(y)‖ dy`. -/
private theorem integral_realMultHaar_norm_mul_rpow (σ : ℝ) :
    ∫ y : ℝ, ‖f y‖ * |y| ^ σ ∂realMultHaar = ∫ y : ℝ, ‖y‖ ^ (σ - 1) * ‖f y‖ := by
  rw [integral_realMultHaar]
  exact integral_congr_ae ((Measure.ae_ne volume 0).mono fun y hy ↦
    abs_inv_smul_mul_abs_rpow _ σ hy)

/-- `‖f(x) χ(x)‖ |x| ^ σ = ‖f(x)‖ |x| ^ (σ + r)` for a quasi-character `χ` of exponent `r`. -/
private theorem norm_mul_mul_rpow_real {χ : ℝˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ x : ℝˣ, ‖(χ x : ℂ)‖ = |(x : ℝ)| ^ r) (σ : ℝ) (x : ℝˣ) :
    ‖f x * (χ x : ℂ)‖ * |(x : ℝ)| ^ σ = ‖f x‖ * |(x : ℝ)| ^ (σ + r) := by
  rw [norm_mul, hχ, mul_assoc, ← Real.rpow_add (abs_pos.2 x.ne_zero), add_comm r]

/-- The norm of the zeta integrand at `ℝ`, for a quasi-character of exponent `r`. -/
private theorem norm_zetaIntegrand_real {χ : ℝˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ x : ℝˣ, ‖(χ x : ℂ)‖ = |(x : ℝ)| ^ r) (s : ℂ) (x : ℝˣ) :
    ‖f x * (χ x : ℂ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ s‖ = ‖f x‖ * |(x : ℝ)| ^ (s.re + r) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (abs_pos.2 x.ne_zero), norm_mul_mul_rpow_real f hχ]

private theorem measurable_zetaIntegrand_real (χ : ℝˣ →ₜ* ℂˣ) (s : ℂ) :
    Measurable fun x : ℝˣ ↦ f x * (χ x : ℂ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ s :=
  ((f.continuous.comp Units.continuous_val).measurable.mul
    (Units.continuous_val.comp χ.continuous).measurable).mul
    ((Complex.continuous_ofReal.comp (continuous_abs.comp
      Units.continuous_val)).measurable.pow_const s)

/-- **Absolute convergence at `ℝ`.** For a Schwartz function `f` and a quasi-character `χ` of
`ℝˣ` of exponent `r`, the zeta integrand `f(x) χ(x) |x| ^ s` is integrable against `dx / |x|`
for `re s + r > 0`. -/
theorem integrable_localZetaIntegrand_real {χ : ℝˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ x : ℝˣ, ‖(χ x : ℂ)‖ = |(x : ℝ)| ^ r) {s : ℂ} (hs : 0 < s.re + r) :
    Integrable (fun x : ℝˣ ↦ f x * (χ x : ℂ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ s) realUnitsMultHaar :=
  (integrable_realUnitsMultHaar_iff.2 (integrable_realMultHaar_norm_mul_rpow f hs)).mono'
    (measurable_zetaIntegrand_real f χ s).aestronglyMeasurable
    (ae_of_all _ fun x ↦ (norm_zetaIntegrand_real f hχ s x).le)

/-- **Holomorphy at `ℝ`.** For a Schwartz function `f` and a quasi-character `χ` of `ℝˣ` of
exponent `r`, `s ↦ z(s, χ; f)` is holomorphic on `re s + r > 0`. -/
theorem differentiableOn_localZetaIntegral_real {χ : ℝˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ x : ℝˣ, ‖(χ x : ℂ)‖ = |(x : ℝ)| ^ r) :
    DifferentiableOn ℂ (localZetaIntegral realUnitsMultHaar (fun x ↦ |x|) χ f)
      {s | 0 < s.re + r} :=
  (differentiableOn_localZetaIntegral_of_integrable realUnitsMultHaar _ χ
    (fun x ↦ abs_pos.2 x.ne_zero) (continuous_abs.comp Units.continuous_val).measurable
    ((f.continuous.comp Units.continuous_val).mul
      (Units.continuous_val.comp χ.continuous)).aestronglyMeasurable (α := -r)
    fun σ hσ ↦ (integrable_realUnitsMultHaar_iff.2
      (integrable_realMultHaar_norm_mul_rpow f (σ := σ + r) (by linarith))).congr
      (ae_of_all _ fun x ↦ (norm_mul_mul_rpow_real f hχ σ x).symm)).mono
    fun s (hs : 0 < s.re + r) ↦ show -r < s.re by linarith

/-- **Continuity on the Schwartz space at `ℝ`.** For a quasi-character `χ` of `ℝˣ` of exponent
`r` and `re s + r > 0`, the local zeta integral `f ↦ z(s, χ; f)` is a continuous linear functional
on `𝓢(ℝ, ℂ)`. -/
def realLocalZetaCLM (χ : ℝˣ →ₜ* ℂˣ) {r : ℝ} (hχ : ∀ x : ℝˣ, ‖(χ x : ℂ)‖ = |(x : ℝ)| ^ r)
    {s : ℂ} (hs : 0 < s.re + r) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
  mkCLMtoNormedSpace (fun f ↦ localZetaIntegral realUnitsMultHaar (fun x ↦ |x|) χ f s)
    (fun f g ↦ localZetaIntegral_add realUnitsMultHaar _ χ
        (integrable_localZetaIntegrand_real f hχ hs) (integrable_localZetaIntegrand_real g hχ hs))
    (fun c f ↦ localZetaIntegral_const_mul realUnitsMultHaar _ χ c f s)
    (by
      obtain ⟨S, C, hC, hbound⟩ := exists_integral_norm_rpow_mul_norm_le (E := ℝ) (F := ℂ) volume ℂ
        (t := s.re + r - 1) (by simp; linarith)
      refine ⟨S, C, hC, fun f ↦ ?_⟩
      rw [localZetaIntegral_def]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ (hbound f))
      simp_rw [norm_zetaIntegrand_real f hχ s]
      rw [integral_realUnitsMultHaar (fun y ↦ ‖f y‖ * |y| ^ (s.re + r)),
        integral_realMultHaar_norm_mul_rpow])

@[simp]
theorem realLocalZetaCLM_apply (χ : ℝˣ →ₜ* ℂˣ) {r : ℝ}
    (hχ : ∀ x : ℝˣ, ‖(χ x : ℂ)‖ = |(x : ℝ)| ^ r) {s : ℂ} (hs : 0 < s.re + r) :
    realLocalZetaCLM χ hχ hs f = localZetaIntegral realUnitsMultHaar (fun x ↦ |x|) χ f s :=
  (rfl)

/-- **The real Gaussian.** `z(s, 1; e^(-π x²)) = Γ_ℝ(s) = π^(-s/2) Γ(s/2)` on `re s > 0`. -/
theorem localZetaIntegral_real_gaussian {s : ℂ} (hs : 0 < s.re) :
    localZetaIntegral realUnitsMultHaar (fun x ↦ |x|) 1
      (fun x ↦ (Real.exp (-(π * x ^ 2)) : ℂ)) s = Gammaℝ s := by
  rw [localZetaIntegral_def]
  simp only [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, mul_one]
  rw [integral_realUnitsMultHaar (fun y ↦ (Real.exp (-(π * y ^ 2)) : ℂ) * ((|y| : ℝ) : ℂ) ^ s)]
  have h := integral_realMultHaar_comp_abs (fun t ↦ (Real.exp (-(π * t ^ 2)) : ℂ) * (t : ℂ) ^ s)
  simp only [sq_abs] at h
  rw [h]
  simp_rw [mul_comm (Real.exp _ : ℂ)]
  rw [integral_multHaar_cpow_mul_exp_neg_mul_sq Real.pi_pos hs, Gammaℝ_def, real_smul,
    ofReal_ofNat, neg_div]
  ring

/-- **The real standard functions.** In Kudla's normal form `ω(x) = x ^ (-a)`, `a ∈ {0, 1}`
(`TauCeti.realUnitsCharacter (-a) a`), the standard function `x ^ a e^(-π x²)` has zeta integral
`L(s, ω) = Γ_ℝ(s)` on `re s > 0`. -/
theorem localZetaIntegral_realUnitsCharacter_standard (ε : ZMod 2) {s : ℂ} (hs : 0 < s.re) :
    localZetaIntegral realUnitsMultHaar (fun x ↦ |x|) (realUnitsCharacter (-(ε.val : ℂ)) ε)
      (fun x ↦ (x : ℂ) ^ ε.val * (Real.exp (-(π * x ^ 2)) : ℂ)) s = Gammaℝ s := by
  rw [← localZetaIntegral_real_gaussian hs, localZetaIntegral_def, localZetaIntegral_def]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  have h := coe_realUnitsCharacter_sub_val_apply 0 ε x
  rw [zero_sub, cpow_zero, mul_one] at h
  simp only [h, ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, mul_one]
  have hx : ((x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 x.ne_zero
  rw [zpow_neg, zpow_natCast]
  field_simp

end Real

/-! ### The complex place -/

section Complex

variable (f : 𝓢(ℂ, ℂ))

/-- The density of `2 dx dy / |z|_ℂ` turns the weight `|z|_ℂ ^ σ` into twice `‖z‖ ^ (2 σ - 2)`
against Lebesgue measure. -/
private theorem two_mul_inv_sq_smul_mul_normSq_rpow (c σ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    (2 * (‖z‖ ^ 2)⁻¹) • (c * normSq z ^ σ) = 2 * (‖z‖ ^ (2 * σ - 2) * c) := by
  rw [smul_eq_mul, normSq_rpow, Real.rpow_sub (norm_pos_iff.2 hz), Real.rpow_two]
  field_simp

/-- For `σ > 0`, `‖f(z)‖ |z|_ℂ ^ σ` is integrable against `2 dx dy / |z|_ℂ`, since against
Lebesgue measure it is twice `‖f(z)‖ ‖z‖ ^ (2 σ - 2)` with `2 σ - 2 > -2`. -/
private theorem integrable_complexMultHaar_norm_mul_rpow {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun z : ℂ ↦ ‖f z‖ * normSq z ^ σ) complexMultHaar := by
  rw [integrable_complexMultHaar_iff]
  exact ((f.integrable_norm_rpow_mul_norm_of_neg_finrank_lt volume (t := 2 * σ - 2)
    (by simp; linarith)).const_mul 2).congr ((Measure.ae_ne volume 0).mono fun z hz ↦
      (two_mul_inv_sq_smul_mul_normSq_rpow _ σ hz).symm)

/-- `∫ ‖f(z)‖ |z|_ℂ ^ σ (2 dx dy / |z|_ℂ) = 2 ∫ ‖z‖ ^ (2 σ - 2) ‖f(z)‖ dx dy`. -/
private theorem integral_complexMultHaar_norm_mul_rpow (σ : ℝ) :
    ∫ z : ℂ, ‖f z‖ * normSq z ^ σ ∂complexMultHaar =
      2 * ∫ z : ℂ, ‖z‖ ^ (2 * σ - 2) * ‖f z‖ := by
  rw [integral_complexMultHaar, ← integral_const_mul]
  exact integral_congr_ae ((Measure.ae_ne volume 0).mono fun z hz ↦
    two_mul_inv_sq_smul_mul_normSq_rpow _ σ hz)

/-- `‖f(z) χ(z)‖ |z|_ℂ ^ σ = ‖f(z)‖ |z|_ℂ ^ (σ + r)` for a quasi-character `χ` of exponent `r`. -/
private theorem norm_mul_mul_rpow_complex {χ : ℂˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ z : ℂˣ, ‖(χ z : ℂ)‖ = normSq (z : ℂ) ^ r) (σ : ℝ) (z : ℂˣ) :
    ‖f z * (χ z : ℂ)‖ * normSq (z : ℂ) ^ σ = ‖f z‖ * normSq (z : ℂ) ^ (σ + r) := by
  rw [norm_mul, hχ, mul_assoc, ← Real.rpow_add (normSq_pos.2 z.ne_zero), add_comm r]

/-- The norm of the zeta integrand at `ℂ`, for a quasi-character of exponent `r`. -/
private theorem norm_zetaIntegrand_complex {χ : ℂˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ z : ℂˣ, ‖(χ z : ℂ)‖ = normSq (z : ℂ) ^ r) (s : ℂ) (z : ℂˣ) :
    ‖f z * (χ z : ℂ) * ((normSq (z : ℂ) : ℝ) : ℂ) ^ s‖ =
      ‖f z‖ * normSq (z : ℂ) ^ (s.re + r) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (normSq_pos.2 z.ne_zero),
    norm_mul_mul_rpow_complex f hχ]

private theorem measurable_zetaIntegrand_complex (χ : ℂˣ →ₜ* ℂˣ) (s : ℂ) :
    Measurable fun z : ℂˣ ↦ f z * (χ z : ℂ) * ((normSq (z : ℂ) : ℝ) : ℂ) ^ s :=
  ((f.continuous.comp Units.continuous_val).measurable.mul
    (Units.continuous_val.comp χ.continuous).measurable).mul
    ((Complex.continuous_ofReal.comp (continuous_normSq.comp
      Units.continuous_val)).measurable.pow_const s)

/-- **Absolute convergence at `ℂ`.** For a Schwartz function `f` and a quasi-character `χ` of
`ℂˣ` of exponent `r` for `|z|_ℂ = normSq z`, the zeta integrand `f(z) χ(z) |z|_ℂ ^ s` is
integrable against `2 dx dy / |z|_ℂ` for `re s + r > 0`. -/
theorem integrable_localZetaIntegrand_complex {χ : ℂˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ z : ℂˣ, ‖(χ z : ℂ)‖ = normSq (z : ℂ) ^ r) {s : ℂ} (hs : 0 < s.re + r) :
    Integrable (fun z : ℂˣ ↦ f z * (χ z : ℂ) * ((normSq (z : ℂ) : ℝ) : ℂ) ^ s)
      complexUnitsMultHaar :=
  (integrable_complexUnitsMultHaar_iff.2 (integrable_complexMultHaar_norm_mul_rpow f hs)).mono'
    (measurable_zetaIntegrand_complex f χ s).aestronglyMeasurable
    (ae_of_all _ fun z ↦ (norm_zetaIntegrand_complex f hχ s z).le)

/-- **Holomorphy at `ℂ`.** For a Schwartz function `f` and a quasi-character `χ` of `ℂˣ` of
exponent `r` for `|z|_ℂ = normSq z`, `s ↦ z(s, χ; f)` is holomorphic on `re s + r > 0`. -/
theorem differentiableOn_localZetaIntegral_complex {χ : ℂˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ z : ℂˣ, ‖(χ z : ℂ)‖ = normSq (z : ℂ) ^ r) :
    DifferentiableOn ℂ (localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z) χ f)
      {s | 0 < s.re + r} :=
  (differentiableOn_localZetaIntegral_of_integrable complexUnitsMultHaar _ χ
    (fun z ↦ normSq_pos.2 z.ne_zero) (continuous_normSq.comp Units.continuous_val).measurable
    ((f.continuous.comp Units.continuous_val).mul
      (Units.continuous_val.comp χ.continuous)).aestronglyMeasurable (α := -r)
    fun σ hσ ↦ (integrable_complexUnitsMultHaar_iff.2
      (integrable_complexMultHaar_norm_mul_rpow f (σ := σ + r) (by linarith))).congr
      (ae_of_all _ fun z ↦ (norm_mul_mul_rpow_complex f hχ σ z).symm)).mono
    fun s (hs : 0 < s.re + r) ↦ show -r < s.re by linarith

/-- **Continuity on the Schwartz space at `ℂ`.** For a quasi-character `χ` of `ℂˣ` of exponent
`r` for `|z|_ℂ` and `re s + r > 0`, the local zeta integral `f ↦ z(s, χ; f)` is a continuous
linear functional on `𝓢(ℂ, ℂ)`. -/
def complexLocalZetaCLM (χ : ℂˣ →ₜ* ℂˣ) {r : ℝ}
    (hχ : ∀ z : ℂˣ, ‖(χ z : ℂ)‖ = normSq (z : ℂ) ^ r) {s : ℂ} (hs : 0 < s.re + r) :
    𝓢(ℂ, ℂ) →L[ℂ] ℂ :=
  mkCLMtoNormedSpace (fun f ↦ localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z) χ f s)
    (fun f g ↦ localZetaIntegral_add complexUnitsMultHaar _ χ
        (integrable_localZetaIntegrand_complex f hχ hs)
        (integrable_localZetaIntegrand_complex g hχ hs))
    (fun c f ↦ localZetaIntegral_const_mul complexUnitsMultHaar _ χ c f s)
    (by
      obtain ⟨S, C, hC, hbound⟩ := exists_integral_norm_rpow_mul_norm_le (E := ℂ) (F := ℂ) volume ℂ
        (t := 2 * (s.re + r) - 2) (by simp; linarith)
      refine ⟨S, 2 * C, by positivity, fun f ↦ ?_⟩
      rw [localZetaIntegral_def]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_
        ((mul_le_mul_of_nonneg_left (hbound f) zero_le_two).trans_eq (mul_assoc _ _ _).symm))
      simp_rw [norm_zetaIntegrand_complex f hχ s]
      rw [integral_complexUnitsMultHaar (fun w ↦ ‖f w‖ * normSq w ^ (s.re + r)),
        integral_complexMultHaar_norm_mul_rpow])

@[simp]
theorem complexLocalZetaCLM_apply (χ : ℂˣ →ₜ* ℂˣ) {r : ℝ}
    (hχ : ∀ z : ℂˣ, ‖(χ z : ℂ)‖ = normSq (z : ℂ) ^ r) {s : ℂ} (hs : 0 < s.re + r) :
    complexLocalZetaCLM χ hχ hs f =
      localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z) χ f s :=
  (rfl)

/-- **The complex Gaussian.** For the twice-Lebesgue additive measure,
`z(s, 1; e^(-2π |z|_ℂ)) = (2π) ^ (1 - s) Γ(s) = π Γ_ℂ(s)` on `re s > 0`. -/
theorem localZetaIntegral_complex_gaussian {s : ℂ} (hs : 0 < s.re) :
    localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z) 1
      (fun z ↦ (Real.exp (-(2 * π * normSq z)) : ℂ)) s = π * Gammaℂ s := by
  rw [localZetaIntegral_def]
  simp only [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, mul_one]
  rw [integral_complexUnitsMultHaar
    (fun w ↦ (Real.exp (-(2 * π * normSq w)) : ℂ) * ((normSq w : ℝ) : ℂ) ^ s)]
  have h := integral_complexMultHaar_comp_norm
    (fun t ↦ (Real.exp (-(2 * π * t ^ 2)) : ℂ) * (t : ℂ) ^ (2 * s))
  rw [← integral_congr_ae (ae_of_all _ fun w ↦ ?_)] at h
  · rw [h]
    simp_rw [mul_comm (Real.exp _ : ℂ)]
    rw [integral_multHaar_cpow_mul_exp_neg_mul_sq (by positivity) (by simpa using hs), Gammaℂ_def,
      mul_div_cancel_left₀ _ two_ne_zero, real_smul]
    push_cast
    ring
  · rw [normSq_eq_norm_sq, ofReal_pow, ofReal_pow_cpow (norm_nonneg w), Nat.cast_ofNat]

/-- **The complex standard functions.** For `ω(z) = z ^ (-a) conj(z) ^ (-b)`
(`TauCeti.complexUnitsCharacter (-(a + b)) (b - a)`), the standard function
`π⁻¹ z ^ a conj(z) ^ b e^(-2π |z|_ℂ)` has zeta integral `Γ_ℂ(s)` on `re s > 0`. When
`min(a, b) = 0`, `ω` is in Kudla's normal form and `Γ_ℂ(s)` is its local factor `L(s, ω)`. -/
theorem localZetaIntegral_complexUnitsCharacter_standard (a b : ℕ) {s : ℂ} (hs : 0 < s.re) :
    localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z)
      (complexUnitsCharacter (-(a + b : ℂ)) (b - a))
      (fun z ↦ (π : ℂ)⁻¹ * (z ^ a * (starRingEnd ℂ z) ^ b) *
        (Real.exp (-(2 * π * normSq z)) : ℂ)) s = Gammaℂ s := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [← mul_div_cancel_left₀ (Gammaℂ s) hπ, ← localZetaIntegral_complex_gaussian hs,
    div_eq_inv_mul, ← localZetaIntegral_const_mul, localZetaIntegral_def, localZetaIntegral_def]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  have h := coe_complexUnitsCharacter_two_mul_sub_apply a b 0 z
  rw [mul_zero, zero_sub, cpow_zero, mul_one] at h
  simp only [h, ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, mul_one]
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hz' : (starRingEnd ℂ) (z : ℂ) ≠ 0 := (map_ne_zero _).2 hz
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  field_simp

/-- **Vanishing by angular weight.** If the test function has angular weight `m`, that is
`f(e^(iθ) z) = e^(i m θ) f(z)`, and the character `TauCeti.complexUnitsCharacter u k` has angular
weight `k` with `m + k ≠ 0`, then `z(s, χ; f) = 0` for every `s`. -/
theorem localZetaIntegral_complexUnitsCharacter_eq_zero_of_rotation {f : ℂ → ℂ} {m k : ℤ}
    (hmk : m + k ≠ 0) (hf : ∀ (θ : ℝ) (z : ℂ), f (exp (θ * I) * z) = exp (θ * I) ^ m * f z)
    (u s : ℂ) :
    localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z) (complexUnitsCharacter u k) f s =
      0 := by
  set θ : ℝ := π / (m + k)
  have hmkC : (m : ℂ) + k ≠ 0 := by exact_mod_cast hmk
  set ζ : ℂˣ := Units.mk0 (exp (θ * I)) (exp_ne_zero _)
  have hζ : ‖(ζ : ℂ)‖ = 1 := norm_exp_ofReal_mul_I θ
  have hθ : ((m + k : ℤ) : ℂ) * (θ : ℂ) = π := by
    simp only [θ]
    push_cast
    field_simp
  have hpow : (ζ : ℂ) ^ (m + k) = -1 := by
    rw [Units.val_mk0, ← exp_intCast_mul, ← mul_assoc, hθ, exp_pi_mul_I]
  have hnormSq : normSq (ζ : ℂ) = 1 := by rw [normSq_eq_norm_sq, hζ, one_pow]
  -- Rotating by `ζ` multiplies `f` by `ζ ^ m` and the integrand's character part by `ζ ^ k`.
  refine localZetaIntegral_eq_zero_of_comp_mul_left complexUnitsMultHaar (fun z ↦ normSq z)
    (complexUnitsCharacter u k) (fun z ↦ normSq_pos.2 z.ne_zero)
    (fun z w ↦ by simp only [Units.val_mul, map_mul]) (b := ζ) (c := (ζ : ℂ) ^ m) (hf θ) ?_
  rw [coe_complexUnitsCharacter_apply, hζ, hnormSq]
  norm_num [← zpow_add₀ ζ.ne_zero, hpow]

end Complex

end TateZeta

end TauCeti
