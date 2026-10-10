/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import TauCeti.Analysis.InnerProductSpace.CompleteSquare
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The heat kernel on a Euclidean space

On a finite-dimensional real inner product space `E` of dimension `n`, the **heat kernel**
(Gauss–Weierstrass kernel) at time `t > 0` is the Gaussian

`K_t(x) = (4πt)^(-n/2) exp(-‖x‖² / (4t))`.

It is the fundamental solution of the heat equation `∂ₜu = Δu` on `ℝⁿ`: the solution of the Cauchy
problem with initial datum `g` is `u(t, ·) = K_t ⋆ g`, and the heat semigroup is convolution with
`K_t`. This file records the basic properties of the kernel itself on which that theory rests:

* `K_t` is smooth in `x`, positive, and has total mass one;
* `K` solves the heat equation: `∂ₜ K_t(x) = Δ K_t(x)` for `t > 0`;
* the semigroup (Chapman–Kolmogorov) identity `K_t ⋆ K_s = K_{t+s}`;
* its Fourier transform, in Mathlib's convention `𝓕 f(ξ) = ∫ e^{-2πi⟪x, ξ⟫} f(x) dx`, is
  `𝓕 K_t(ξ) = exp(-4π² t ‖ξ‖²)`.

The value of `heatKernel t x` for `t ≤ 0` carries no meaning; every statement about the kernel as
a heat kernel assumes `0 < t`.

## Main declarations

* `TauCeti.heatKernel`: the heat kernel `K_t(x)`.
* `TauCeti.heatKernel_pos`: `K_t > 0` for `t > 0`.
* `TauCeti.heatKernel_eq_mul_heatKernel_one_smul`: the parabolic scaling
  `K_t(x) = (√t)⁻¹ ^ n K_1((√t)⁻¹ • x)`.
* `TauCeti.contDiff_heatKernel`: `K_t` is smooth.
* `TauCeti.integral_heatKernel`: `∫ K_t = 1` for `t > 0`.
* `TauCeti.laplacian_heatKernel`: `Δ K_t(x) = (‖x‖² / (4t²) - n / (2t)) K_t(x)`.
* `TauCeti.hasDerivAt_heatKernel`: the heat equation `∂ₜ K_t(x) = Δ K_t(x)` for `t > 0`.
* `TauCeti.heatKernel_convolution_heatKernel`: the semigroup identity `K_t ⋆ K_s = K_{t+s}`.
* `TauCeti.fourier_heatKernel`: `𝓕 K_t(ξ) = exp(-4π² t ‖ξ‖²)`.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.3.1.
* E. M. Stein, G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Chapter I,
  Theorem 1.13.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Real
open scoped RealInnerProductSpace Convolution FourierTransform ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **heat kernel** (Gauss–Weierstrass kernel) on a finite-dimensional real inner product
space `E` of dimension `n`: `K_t(x) = (4πt)^(-n/2) exp(-‖x‖² / (4t))`. It is meaningful only for
`t > 0`. -/
def heatKernel (t : ℝ) (x : E) : ℝ :=
  (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * exp (-‖x‖ ^ 2 / (4 * t))

/-- The defining formula of the heat kernel. -/
theorem heatKernel_apply (t : ℝ) (x : E) :
    heatKernel t x = (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * exp (-‖x‖ ^ 2 / (4 * t)) :=
  (rfl)

/-- The heat kernel is positive at every positive time. -/
theorem heatKernel_pos {t : ℝ} (ht : 0 < t) (x : E) : 0 < heatKernel t x := by
  rw [heatKernel_apply]
  positivity

/-- The heat kernel is radial; in particular it is even. -/
@[simp]
theorem heatKernel_neg (t : ℝ) (x : E) : heatKernel t (-x) = heatKernel t x := by
  simp [heatKernel_apply]

/-- **Parabolic scaling of the heat kernel.** For `t > 0`, `K_t` is the `L¹`-normalized dilation
of `K_1` by the factor `(√t)⁻¹`: `K_t(x) = (√t)⁻¹ ^ n K_1((√t)⁻¹ • x)` with `n = dim E`. -/
theorem heatKernel_eq_mul_heatKernel_one_smul {t : ℝ} (ht : 0 < t) (x : E) :
    heatKernel t x = (√t)⁻¹ ^ Module.finrank ℝ E * heatKernel 1 ((√t)⁻¹ • x) := by
  have hst : 0 < √t := sqrt_pos.2 ht
  have hpow : (√t)⁻¹ ^ Module.finrank ℝ E = t ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
    rw [sqrt_eq_rpow, ← rpow_natCast, inv_rpow (by positivity), ← rpow_mul ht.le, ← rpow_neg ht.le]
    ring_nf
  have hnorm : ‖(√t)⁻¹ • x‖ ^ 2 = ‖x‖ ^ 2 / t := by
    rw [norm_smul, norm_inv, norm_of_nonneg hst.le, mul_pow, inv_pow, sq_sqrt ht.le]
    ring
  rw [heatKernel_apply, heatKernel_apply, hnorm, hpow, mul_one, mul_rpow (by positivity) ht.le]
  field_simp

/-- The heat kernel `K_t` is smooth in the space variable (for every `t`). -/
theorem contDiff_heatKernel (t : ℝ) {k : WithTop ℕ∞} : ContDiff ℝ k (heatKernel t : E → ℝ) :=
  contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const _).exp)

section Laplacian

variable [FiniteDimensional ℝ E]

/-- The Laplacian of the heat kernel: `Δ K_t(x) = (‖x‖² / (4t²) - n / (2t)) K_t(x)`. -/
theorem laplacian_heatKernel (t : ℝ) (x : E) :
    Δ (heatKernel t : E → ℝ) x =
      (‖x‖ ^ 2 / (4 * t ^ 2) - Module.finrank ℝ E / (2 * t)) * heatKernel t x := by
  set c : ℝ := (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)
  -- `K_t` is the radial function `x ↦ ρ (‖x‖²)` for `ρ r = c exp(-r / (4t))`.
  set ρ : ℝ → ℝ := fun r => c * exp (-r / (4 * t))
  have hρ : ∀ r, HasDerivAt ρ (-(4 * t)⁻¹ * ρ r) r := fun r => by
    refine ((((hasDerivAt_id r).neg.div_const (4 * t)).exp).const_mul c).congr_deriv ?_
    simp only [ρ, Pi.neg_apply, id_eq]
    ring
  have hdρ : deriv ρ = fun r => -(4 * t)⁻¹ * ρ r := funext fun r => (hρ r).deriv
  have hddρ : deriv (deriv ρ) = fun r => (4 * t)⁻¹ ^ 2 * ρ r := by
    rw [hdρ]
    funext r
    rw [((hρ r).const_mul (-(4 * t)⁻¹)).deriv]
    ring
  have hK : heatKernel t = fun y : E => ρ (‖y‖ ^ 2) := funext fun y => heatKernel_apply t y
  have hρc : ContDiff ℝ 2 ρ := contDiff_const.mul ((contDiff_id.neg.div_const _).exp)
  rw [hK, hρc.laplacian_comp_norm_sq, hddρ, hdρ]
  ring

/-- **The heat equation.** For `t > 0`, the heat kernel solves `∂ₜ K_t(x) = Δ K_t(x)`. -/
theorem hasDerivAt_heatKernel {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => heatKernel s x) (Δ (heatKernel t : E → ℝ) x) t := by
  set p : ℝ := -(Module.finrank ℝ E : ℝ) / 2
  have h4πt : 0 < 4 * π * t := by positivity
  have hpow : HasDerivAt (fun s : ℝ => (4 * π * s) ^ p)
      (4 * π * p * (4 * π * t) ^ p / (4 * π * t)) t := by
    refine (((hasDerivAt_id t).const_mul (4 * π)).rpow_const (p := p)
      (Or.inl h4πt.ne')).congr_deriv ?_
    rw [id, rpow_sub_one h4πt.ne']
    ring
  have hexp : HasDerivAt (fun s : ℝ => exp (-‖x‖ ^ 2 / (4 * s)))
      (exp (-‖x‖ ^ 2 / (4 * t)) * (‖x‖ ^ 2 / (4 * t ^ 2))) t := by
    have hfun : (fun s : ℝ => exp (-‖x‖ ^ 2 / (4 * s))) =
        fun s => exp (-‖x‖ ^ 2 / 4 * s⁻¹) := funext fun s => by ring_nf
    rw [hfun]
    refine ((hasDerivAt_inv ht.ne').const_mul (-‖x‖ ^ 2 / 4)).exp.congr_deriv ?_
    field_simp
  have hK : (fun s => heatKernel s x) = fun s => (4 * π * s) ^ p * exp (-‖x‖ ^ 2 / (4 * s)) :=
    funext fun s => heatKernel_apply s x
  rw [hK]
  refine (hpow.mul hexp).congr_deriv ?_
  rw [laplacian_heatKernel, heatKernel_apply]
  field_simp
  simp only [p, neg_div]
  ring

end Laplacian

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The heat kernel has mass one. -/
@[simp]
theorem integral_heatKernel {t : ℝ} (ht : 0 < t) : ∫ x : E, heatKernel t x = 1 := by
  have h4t : 0 < 4 * t := by positivity
  have hexp : ∀ x : E, -‖x‖ ^ 2 / (4 * t) = -(4 * t)⁻¹ * ‖x‖ ^ 2 := fun x => by ring
  simp_rw [heatKernel_apply, hexp, integral_const_mul,
    GaussianFourier.integral_rexp_neg_mul_sq_norm (inv_pos.2 h4t), div_inv_eq_mul, neg_div,
    rpow_neg (by positivity : 0 ≤ 4 * π * t)]
  rw [show π * (4 * t) = 4 * π * t by ring, inv_mul_cancel₀ (by positivity)]

/-- The heat kernel is integrable at every positive time. -/
theorem integrable_heatKernel {t : ℝ} (ht : 0 < t) : Integrable (heatKernel t : E → ℝ) :=
  Integrable.of_integral_ne_zero (by simp [integral_heatKernel ht])

/-- **The semigroup property of the heat kernel** (Chapman–Kolmogorov):
`K_t ⋆ K_s = K_{t+s}` for `t, s > 0`. -/
theorem heatKernel_convolution_heatKernel {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    heatKernel t ⋆ heatKernel s = (heatKernel (t + s) : E → ℝ) := by
  set p : ℝ := (Module.finrank ℝ E : ℝ) / 2
  set b : ℝ := (t + s) / (4 * t * s)
  have hb : 0 < b := by positivity
  funext x
  -- The integrand is a translate of a centred Gaussian, by completing the square.
  have hint : ∀ y : E, heatKernel t y * heatKernel s (x - y) =
      (4 * π * t) ^ (-p) * (4 * π * s) ^ (-p) * exp (-‖x‖ ^ 2 / (4 * (t + s))) *
        exp (-b * ‖y - (t / (t + s)) • x‖ ^ 2) := fun y => by
    have hexp : -‖y‖ ^ 2 / (4 * t) + -‖x - y‖ ^ 2 / (4 * s) =
        -‖x‖ ^ 2 / (4 * (t + s)) + -b * ‖y - (t / (t + s)) • x‖ ^ 2 := by
      have := mul_norm_sq_add_mul_norm_sub_sq (a := (4 * t)⁻¹) (b := (4 * s)⁻¹) (by positivity) x y
      rw [show (4 * s)⁻¹ / ((4 * t)⁻¹ + (4 * s)⁻¹) = t / (t + s) by field_simp; ring,
        show (4 * t)⁻¹ + (4 * s)⁻¹ = b by simp only [b]; field_simp; ring,
        show (4 * t)⁻¹ * (4 * s)⁻¹ / b = (4 * (t + s))⁻¹ by simp only [b]; field_simp] at this
      linear_combination -this
    rw [heatKernel_apply, heatKernel_apply, mul_mul_mul_comm, ← exp_add, hexp, exp_add]
    simp only [p, neg_div]
    ring
  simp_rw [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hint,
    integral_const_mul, integral_sub_right_eq_self (fun y : E => exp (-b * ‖y‖ ^ 2)),
    GaussianFourier.integral_rexp_neg_mul_sq_norm hb, heatKernel_apply, neg_div]
  -- The normalizing constants: `(4πt)^(-p) (4πs)^(-p) (π / b)^p = (4π(t + s))^(-p)`.
  have hπb : π / b = 4 * π * t * (4 * π * s) / (4 * π * (t + s)) := by
    simp only [b]
    field_simp
  rw [hπb, div_rpow (by positivity) (by positivity),
    mul_rpow (x := 4 * π * t) (y := 4 * π * s) (by positivity) (by positivity),
    rpow_neg (by positivity), rpow_neg (by positivity), rpow_neg (by positivity)]
  field_simp
  simp only [p]

/-- **The Fourier transform of the heat kernel.** In Mathlib's normalization
`𝓕 f(ξ) = ∫ e^{-2πi⟪x, ξ⟫} f(x) dx`, `𝓕 K_t(ξ) = exp(-4π² t ‖ξ‖²)` for `t > 0`. -/
theorem fourier_heatKernel {t : ℝ} (ht : 0 < t) (ξ : E) :
    𝓕 (fun x : E => (heatKernel t x : ℂ)) ξ = (exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℂ) := by
  set c : ℝ := (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)
  have hb : 0 < ((4 * t : ℝ)⁻¹ : ℂ).re := by
    rw [← Complex.ofReal_inv, Complex.ofReal_re]
    positivity
  have hK : (fun x : E => (heatKernel t x : ℂ)) =
      (c : ℂ) • fun x => Complex.exp (-((4 * t : ℝ)⁻¹ : ℂ) * ‖x‖ ^ 2) := funext fun x => by
    rw [Pi.smul_apply, smul_eq_mul, heatKernel_apply, Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  -- The Fourier transform is homogeneous, and Mathlib computes it on a centred Gaussian.
  rw [hK, fourier_eq]
  simp_rw [Pi.smul_apply, smul_comm _ (c : ℂ), integral_smul, ← fourier_eq,
    fourier_gaussian_innerProductSpace hb, smul_eq_mul]
  -- Collect the normalizing constants: `(4πt)^(-n/2) (π / (4t)⁻¹)^(n/2) = 1`.
  have hpow : ((π : ℂ) / ((4 * t : ℝ) : ℂ)⁻¹) ^ ((Module.finrank ℝ E : ℂ) / 2) =
      ((4 * π * t) ^ ((Module.finrank ℝ E : ℝ) / 2) : ℝ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    congr 1
    field_simp
  have hexp : Complex.exp (-(π : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2 / ((4 * t : ℝ) : ℂ)⁻¹) =
      (exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    congr 1
    field_simp
  have hc : c * (4 * π * t) ^ ((Module.finrank ℝ E : ℝ) / 2) = 1 := by
    simp only [c, neg_div]
    rw [rpow_neg (by positivity), inv_mul_cancel₀ (by positivity)]
  rw [hpow, hexp, ← mul_assoc, ← Complex.ofReal_mul, hc, Complex.ofReal_one, one_mul]

end TauCeti
