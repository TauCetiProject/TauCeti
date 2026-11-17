/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
public import TauCeti.Analysis.PDE.Schrodinger.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Lp
import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# The Schrödinger evolution of a Gaussian

On a finite-dimensional real inner product space `E` of dimension `n`, the Gaussian
`g(x) = exp(-π ‖x‖²)`, which is its own Fourier transform, evolves under the Schrödinger
propagator `S(t) = exp(itΔ)` (`TauCeti.schrodingerPropagator`) into the complex Gaussian

`S(t) g (x) = (1 + 4πit)^(-n/2) exp(-π ‖x‖² / (1 + 4πit))`

(`TauCeti.coeFn_schrodingerPropagator_toLp_gaussian`), whose modulus is the real Gaussian

`|S(t) g (x)| = (1 + 16π²t²)^(-n/4) exp(-π ‖x‖² / (1 + 16π²t²))`.

So all the Lebesgue norms of `S(t) g` are explicit: `‖S(t) g‖_∞ = (1 + 16π²t²)^(-n/4)`, and for
`0 < r < ∞`,

`‖S(t) g‖_r = r^(-n/(2r)) (1 + 16π²t²)^(-n (1/2 - 1/r) / 2)`.

At `t = 0` this is `‖g‖_r = r^(-n/(2r))` (`SchwartzMap.eLpNorm_gaussian`), in particular
`‖g‖₁ = 1`.

This is the basic test case of the dispersive and Strichartz estimates.

* **The dispersive estimate is sharp in rate.** The dispersive estimate
  `‖S(t) f‖_∞ ≤ (4π|t|)^(-n/2) ‖f‖₁` (`TauCeti.eLpNorm_schrodingerPropagator_le`) is attained by
  `g` as `|t| → ∞`: `(4π|t|)^(n/2) ‖S(t) g‖_∞ → 1 = ‖g‖₁`, so neither the decay exponent `n/2`
  nor the constant can be improved.
* **The time integrability of the Strichartz norms.** The function `t ↦ ‖S(t) g‖_r` lies in
  `L^q(ℝ)` exactly when `q n (1/2 - 1/r) > 1`. In particular it does so for every admissible pair
  `2/q + n/r = n/2` with `q < ∞`, where `q n (1/2 - 1/r) = 2`. On the line the Gaussian evolution
  lies in `L⁴_t L^∞_x`, at the endpoint `(4, ∞)` of the admissible range, but not in
  `L²_t L^∞_x`, a non-admissible pair where `q n (1/2 - 1/r) = 1`.

## Main declarations

* `TauCeti.coeFn_schrodingerPropagator_toLp_gaussian`: the evolution of the Gaussian.
* `TauCeti.ae_norm_schrodingerPropagator_toLp_gaussian`: its modulus.
* `TauCeti.eLpNorm_schrodingerPropagator_toLp_gaussian_top`,
  `TauCeti.eLpNorm_schrodingerPropagator_toLp_gaussian`: its `L^∞` and `Lʳ` norms.
* `TauCeti.tendsto_rpow_mul_eLpNorm_schrodingerPropagator_toLp_gaussian_top`: the dispersive
  estimate is attained in rate.
* `TauCeti.memLp_eLpNorm_schrodingerPropagator_toLp_gaussian_iff`: the exact range of time
  integrability, and `TauCeti.memLp_eLpNorm_schrodingerPropagator_toLp_gaussian_of_admissible` at
  the admissible pairs.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.2.
-/

public section

noncomputable section

open scoped ENNReal FourierTransform Topology SchwartzMap
open MeasureTheory Filter Complex
open Real hiding exp

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The modulus of the evolved Gaussian -/

/-- The modulus of the complex Gaussian `(1 + 4πit)^(-n/2) exp(-π ‖x‖² / (1 + 4πit))`. -/
private theorem norm_cpow_mul_cexp_div_one_add (t : ℝ) (x : E) :
    ‖(1 + 4 * π * t * I) ^ (-(Module.finrank ℝ E : ℂ) / 2) *
        cexp (-π * ‖x‖ ^ 2 / (1 + 4 * π * t * I))‖ =
      (1 + 16 * π ^ 2 * t ^ 2) ^ (-(Module.finrank ℝ E : ℝ) / 4) *
        rexp (-π * ‖x‖ ^ 2 / (1 + 16 * π ^ 2 * t ^ 2)) := by
  have hs : -(Module.finrank ℝ E : ℂ) / 2 = ((-(Module.finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hw : (1 + 4 * π * t * I : ℂ) = ((1 : ℝ) : ℂ) + ((4 * π * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hnorm : ‖(1 + 4 * π * t * I : ℂ)‖ = √(1 + 16 * π ^ 2 * t ^ 2) := by
    rw [hw, norm_add_mul_I]
    ring_nf
  -- The real part of `-π ‖x‖² / (1 + 4πit)` is `-π ‖x‖² / (1 + 16π²t²)`.
  have hre : (-π * ‖x‖ ^ 2 / (1 + 4 * π * t * I) : ℂ).re =
      -π * ‖x‖ ^ 2 / (1 + 16 * π ^ 2 * t ^ 2) := by
    have hz : (-π * ‖x‖ ^ 2 : ℂ) = ((-π * ‖x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hz, hw, div_re, normSq_add_mul_I]
    simp only [ofReal_re, ofReal_im, zero_mul, add_zero, add_re, mul_re, I_re, I_im, mul_zero,
      mul_one, sub_zero]
    ring_nf
  rw [norm_mul, hs, norm_cpow_real, hnorm, Complex.norm_exp, hre, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by positivity)]
  ring_nf

omit [InnerProductSpace ℝ E] in
private theorem continuous_rpow_mul_rexp_div {u : ℝ} (a : ℝ) :
    Continuous fun x : E ↦ u ^ a * rexp (-π * ‖x‖ ^ 2 / u) := by
  fun_prop

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The Schrödinger evolution of a Gaussian.** The Gaussian `g(x) = exp(-π ‖x‖²)`, which is its
own Fourier transform, evolves into the complex Gaussian

`S(t) g (x) = (1 + 4πit)^(-n/2) exp(-π ‖x‖² / (1 + 4πit))`,

with the principal power. -/
theorem coeFn_schrodingerPropagator_toLp_gaussian (t : ℝ) :
    schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := π) (by simpa using pi_pos) : 𝓢(E, ℂ)).toLp 2) =ᵐ[volume]
      fun x ↦ (1 + 4 * π * t * I) ^ (-(Module.finrank ℝ E : ℂ) / 2) *
        cexp (-π * ‖x‖ ^ 2 / (1 + 4 * π * t * I)) := by
  have hπ : 0 < (π : ℂ).re := by simpa using pi_pos
  set b : ℂ := π * (1 + 4 * π * t * I)
  have hb : 0 < b.re := by
    have : b.re = π := by simp [b]
    rw [this]
    exact pi_pos
  have hfourier : ∀ ξ : E, 𝓕 (𝓕⁻ (SchwartzMap.gaussian hb : 𝓢(E, ℂ))) ξ =
      phaseSymbol laplacianSymbol t ξ • 𝓕 (SchwartzMap.gaussian hπ : 𝓢(E, ℂ)) ξ := fun ξ ↦ by
    rw [FourierTransform.fourier_fourierInv_eq, SchwartzMap.fourier_coe]
    have : ⇑(SchwartzMap.gaussian hπ : 𝓢(E, ℂ)) = fun ξ ↦ cexp (-π * ‖ξ‖ ^ 2) :=
      funext (SchwartzMap.gaussian_apply hπ)
    rw [this, fourier_gaussian_innerProductSpace hπ]
    simp only [div_self (ofReal_ne_zero.2 pi_ne_zero), one_cpow, one_mul,
      SchwartzMap.gaussian_apply, phaseSymbol_apply, laplacianSymbol_apply, smul_eq_mul]
    rw [← Complex.exp_add]
    congr 1
    simp only [b]
    push_cast
    field_simp
    ring
  have h := SchwartzMap.toLp_eq_fourierMultiplierCLM_of_fourier_eq_smul _
    (memLp_phaseSymbol (E := E) laplacianSymbol t).coeFn_toLp hfourier
  rw [schrodingerPropagator_def, phasePropagator_def, ← h]
  filter_upwards [(𝓕⁻ (SchwartzMap.gaussian hb : 𝓢(E, ℂ))).coeFn_toLp 2] with x hx
  have h1 : (1 + 4 * π * t * I : ℂ).arg ≠ π :=
    (mem_slitPlane_iff_arg.1 (mem_slitPlane_iff.2 (Or.inl (by simp)))).1
  -- The coefficient `π / b` of the inverse-Fourier Gaussian is `(1 + 4πit)⁻¹`.
  have hcoeff : (π : ℂ) / b = (1 + 4 * π * t * I)⁻¹ := by
    simp only [b]
    field_simp
  rw [hx, SchwartzMap.fourierInv_gaussian]
  congr 1
  · rw [hcoeff, inv_cpow _ _ h1, ← cpow_neg, neg_div]
  · congr 1
    simp only [b]
    field_simp

/-! ### Lebesgue norms -/

/-- The real Gaussian `u^(-n/4) exp(-π ‖x‖² / u)` is `u^(-n/4)` times the Schwartz Gaussian
`exp(-(π / u) ‖x‖²)`, in every Lebesgue norm. -/
private theorem eLpNorm_rpow_mul_rexp_div {u : ℝ} (hu : 0 < u) (r : ℝ≥0∞) :
    eLpNorm (fun x : E ↦ u ^ (-(Module.finrank ℝ E : ℝ) / 4) * rexp (-π * ‖x‖ ^ 2 / u)) r
        volume =
      ENNReal.ofReal (u ^ (-(Module.finrank ℝ E : ℝ) / 4)) *
        eLpNorm (SchwartzMap.gaussian (b := ((π / u : ℝ) : ℂ))
          (by simpa using div_pos pi_pos hu) : 𝓢(E, ℂ)) r volume := by
  have hf : (fun x : E ↦ u ^ (-(Module.finrank ℝ E : ℝ) / 4) * rexp (-π * ‖x‖ ^ 2 / u)) =
      u ^ (-(Module.finrank ℝ E : ℝ) / 4) • fun x : E ↦ rexp (-(π / u) * ‖x‖ ^ 2) := by
    ext x
    rw [Pi.smul_apply, smul_eq_mul]
    ring_nf
  rw [hf, eLpNorm_const_smul, ← ofReal_norm, Real.norm_of_nonneg (by positivity)]
  congr 1
  refine eLpNorm_congr_norm_ae (Continuous.aestronglyMeasurable (by fun_prop))
    (SchwartzMap.continuous _).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  rw [SchwartzMap.coe_gaussian_ofReal, norm_real]
  ring_nf

/-- **The modulus of the evolved Gaussian.** `|S(t) g (x)| = (1 + 16π²t²)^(-n/4)
exp(-π ‖x‖² / (1 + 16π²t²))` for the Gaussian `g(x) = exp(-π ‖x‖²)`. -/
theorem ae_norm_schrodingerPropagator_toLp_gaussian (t : ℝ) :
    ∀ᵐ x ∂volume, ‖schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := π) (by simpa using pi_pos) : 𝓢(E, ℂ)).toLp 2) x‖ =
      (1 + 16 * π ^ 2 * t ^ 2) ^ (-(Module.finrank ℝ E : ℝ) / 4) *
        rexp (-π * ‖x‖ ^ 2 / (1 + 16 * π ^ 2 * t ^ 2)) := by
  filter_upwards [coeFn_schrodingerPropagator_toLp_gaussian (E := E) t] with x hx
  rw [hx, norm_cpow_mul_cexp_div_one_add]

/-- The `Lʳ` norms of the evolved Gaussian are those of the real Gaussian giving its modulus. -/
private theorem eLpNorm_schrodingerPropagator_toLp_gaussian_eq (t : ℝ) (r : ℝ≥0∞) :
    eLpNorm (schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := π) (by simpa using pi_pos) : 𝓢(E, ℂ)).toLp 2)) r volume =
      eLpNorm (fun x : E ↦ (1 + 16 * π ^ 2 * t ^ 2) ^ (-(Module.finrank ℝ E : ℝ) / 4) *
        rexp (-π * ‖x‖ ^ 2 / (1 + 16 * π ^ 2 * t ^ 2))) r volume := by
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
    (continuous_rpow_mul_rexp_div _).aestronglyMeasurable ?_
  filter_upwards [ae_norm_schrodingerPropagator_toLp_gaussian (E := E) t] with x hx
  rw [hx, Real.norm_of_nonneg (by positivity)]

/-- **The supremum of the evolved Gaussian.** `‖S(t) g‖_∞ = (1 + 16π²t²)^(-n/4)` for the Gaussian
`g(x) = exp(-π ‖x‖²)`. -/
theorem eLpNorm_schrodingerPropagator_toLp_gaussian_top (t : ℝ) :
    eLpNorm (schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := π) (by simpa using pi_pos) : 𝓢(E, ℂ)).toLp 2)) ∞ volume =
      ENNReal.ofReal ((1 + 16 * π ^ 2 * t ^ 2) ^ (-(Module.finrank ℝ E : ℝ) / 4)) := by
  rw [eLpNorm_schrodingerPropagator_toLp_gaussian_eq, eLpNorm_rpow_mul_rexp_div (by positivity),
    SchwartzMap.eLpNorm_gaussian_top, mul_one]

/-- **The Lebesgue norms of the evolved Gaussian.** For `0 < r < ∞`,
`‖S(t) g‖_r = r^(-n/(2r)) (1 + 16π²t²)^(-n (1/2 - 1/r) / 2)` for the Gaussian
`g(x) = exp(-π ‖x‖²)`. -/
theorem eLpNorm_schrodingerPropagator_toLp_gaussian {r : ℝ≥0∞} (hr0 : r ≠ 0) (hr : r ≠ ∞)
    (t : ℝ) :
    eLpNorm (schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := π) (by simpa using pi_pos) : 𝓢(E, ℂ)).toLp 2)) r volume =
      ENNReal.ofReal (r.toReal ^ (-(Module.finrank ℝ E : ℝ) / (2 * r.toReal)) *
        (1 + 16 * π ^ 2 * t ^ 2) ^ (-(Module.finrank ℝ E : ℝ) * (2⁻¹ - r.toReal⁻¹) / 2)) := by
  have hρ : 0 < r.toReal := ENNReal.toReal_pos hr0 hr
  set u : ℝ := 1 + 16 * π ^ 2 * t ^ 2
  have hu : 0 < u := by positivity
  -- The real identity `u^(-n/4) (u / r)^(n/(2r)) = r^(-n/(2r)) u^(-n (1/2 - 1/r) / 2)`.
  have key : u ^ (-(Module.finrank ℝ E : ℝ) / 4) *
      (π / (π / u * r.toReal)) ^ ((Module.finrank ℝ E : ℝ) / (2 * r.toReal)) =
      r.toReal ^ (-(Module.finrank ℝ E : ℝ) / (2 * r.toReal)) *
        u ^ (-(Module.finrank ℝ E : ℝ) * (2⁻¹ - r.toReal⁻¹) / 2) := by
    rw [show π / (π / u * r.toReal) = u * r.toReal⁻¹ by field_simp,
      Real.mul_rpow hu.le (inv_nonneg.2 hρ.le), Real.inv_rpow hρ.le, ← Real.rpow_neg hρ.le,
      ← mul_assoc, ← Real.rpow_add hu, mul_comm]
    congr 2 <;> ring
  rw [eLpNorm_schrodingerPropagator_toLp_gaussian_eq, eLpNorm_rpow_mul_rexp_div hu,
    SchwartzMap.eLpNorm_gaussian _ hr0 hr, ofReal_re, ← ENNReal.ofReal_mul (by positivity), key]

/-! ### Sharpness of the dispersive estimate -/

/-- **The dispersive estimate is attained in rate.** For the Gaussian `g(x) = exp(-π ‖x‖²)`, which
has `‖g‖₁ = 1` (`SchwartzMap.eLpNorm_gaussian`), `(4π|t|)^(n/2) ‖S(t) g‖_∞ → 1` as `|t| → ∞`. So the
dispersive estimate `‖S(t) f‖_∞ ≤ (4π|t|)^(-n/2) ‖f‖₁`
(`TauCeti.eLpNorm_schrodingerPropagator_le`) is sharp, both in the decay exponent `n/2` and in
the constant. -/
theorem tendsto_rpow_mul_eLpNorm_schrodingerPropagator_toLp_gaussian_top :
    Tendsto (fun t : ℝ ↦ (4 * π * |t|) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        (eLpNorm (schrodingerPropagator ℂ t
          ((SchwartzMap.gaussian (b := π) (by simpa using pi_pos) : 𝓢(E, ℂ)).toLp 2)) ∞
          volume).toReal) (cocompact ℝ) (𝓝 1) := by
  -- With `v = 16π²t²`, the product is `(v / (1 + v))^(n/4)`, and `v → ∞`.
  have hv : Tendsto (fun t : ℝ ↦ 16 * π ^ 2 * t ^ 2) (cocompact ℝ) atTop := by
    refine Tendsto.const_mul_atTop (by positivity) ?_
    refine ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cocompact_atTop).congr fun t ↦ ?_
    simp [Real.norm_eq_abs, sq_abs]
  have hfrac : Tendsto (fun v : ℝ ↦ v / (1 + v)) atTop (𝓝 1) := by
    have h : Tendsto (fun v : ℝ ↦ 1 - (1 + v)⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub
        (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id))
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with v hv
    field_simp
    ring
  -- The product `(4π|t|)^(n/2) (1 + v)^(-n/4)` is `(v / (1 + v))^(n/4)`.
  have key (t : ℝ) : (16 * π ^ 2 * t ^ 2 / (1 + 16 * π ^ 2 * t ^ 2)) ^
      ((Module.finrank ℝ E : ℝ) / 4) = (4 * π * |t|) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        (1 + 16 * π ^ 2 * t ^ 2) ^ (-(Module.finrank ℝ E : ℝ) / 4) := by
    have hv : (16 * π ^ 2 * t ^ 2) ^ ((Module.finrank ℝ E : ℝ) / 4) =
        (4 * π * |t|) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
      rw [show 16 * π ^ 2 * t ^ 2 = (4 * π * |t|) ^ (2 : ℝ) by
        rw [Real.rpow_two, mul_pow, sq_abs]; ring, ← Real.rpow_mul (by positivity)]
      ring_nf
    rw [Real.div_rpow (by positivity) (by positivity), hv, neg_div, Real.rpow_neg (by positivity),
      div_eq_mul_inv]
  have hlim := (hfrac.comp hv).rpow_const (p := (Module.finrank ℝ E : ℝ) / 4) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at hlim
  refine hlim.congr fun t ↦ ?_
  rw [eLpNorm_schrodingerPropagator_toLp_gaussian_top, ENNReal.toReal_ofReal (by positivity),
    Function.comp_apply, key]

/-! ### Time integrability -/

/-- `t ↦ c (1 + 16π²t²)^(-a/2)`, `c > 0`, lies in `L^q(ℝ)`, `0 < q < ∞`, exactly when
`q a > 1`: it is a multiple of the dilated Japanese bracket `(1 + ‖4πt‖²)^(-a/2)`. -/
private theorem memLp_mul_one_add_rpow_iff {c : ℝ} (hc : 0 < c) (a : ℝ) {q : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq : q ≠ ∞) :
    MemLp (fun t : ℝ ↦ c * (1 + 16 * π ^ 2 * t ^ 2) ^ (-a / 2)) q volume ↔ 1 < q.toReal * a := by
  set g : ℝ → ℝ := fun s ↦ (1 + ‖s‖ ^ 2) ^ (-a / 2)
  have hf : (fun t : ℝ ↦ c * (1 + 16 * π ^ 2 * t ^ 2) ^ (-a / 2)) =
      c • fun t ↦ g ((4 * π)⁻¹⁻¹ • t) := by
    ext t
    simp only [g, Pi.smul_apply, smul_eq_mul, inv_inv, Real.norm_eq_abs, sq_abs]
    ring_nf
  -- Scaling the variable and the value multiplies the `L^q` norm by a positive finite constant.
  have he : eLpNorm (c • fun t ↦ g ((4 * π)⁻¹⁻¹ • t)) q volume =
      ‖c‖ₑ * ENNReal.ofReal (|(4 * π)⁻¹| ^ (1 / q.toReal)) * eLpNorm g q volume := by
    rw [eLpNorm_const_smul, Measure.eLpNorm_comp_inv_smul volume g (by positivity),
      Module.finrank_self, Nat.cast_one, mul_assoc]
  have hk0 : ‖c‖ₑ * ENNReal.ofReal (|(4 * π)⁻¹| ^ (1 / q.toReal)) ≠ 0 :=
    mul_ne_zero (eNorm_ne_zero.2 hc.ne') (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hiff := memLp_rpow_neg_one_add_norm_sq_iff (V := ℝ) volume a hq0 hq
  rw [Module.finrank_self, Nat.cast_one] at hiff
  rw [hf, ← hiff, memLp_iff, memLp_iff, he]
  exact ⟨fun h ↦ ENNReal.lt_top_of_mul_ne_top_right h.ne hk0,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top eNorm_lt_top ENNReal.ofReal_lt_top)⟩

/-- **The exact time integrability of the Strichartz norms of the evolved Gaussian.** For
`0 < q < ∞` and `0 < r ≤ ∞`, the function `t ↦ ‖S(t) g‖_r` of the Gaussian `g(x) = exp(-π ‖x‖²)`
lies in `L^q(ℝ)` exactly when `q n (1/2 - 1/r) > 1`, with `1/∞ = 0`. -/
theorem memLp_eLpNorm_schrodingerPropagator_toLp_gaussian_iff {q r : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq : q ≠ ∞) (hr0 : r ≠ 0) :
    MemLp (fun t : ℝ ↦ (eLpNorm (schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := π) (by simpa using pi_pos) : 𝓢(E, ℂ)).toLp 2)) r
          volume).toReal) q volume ↔
      1 < q.toReal * (Module.finrank ℝ E * (2⁻¹ - r.toReal⁻¹)) := by
  rcases eq_or_ne r ∞ with rfl | hr
  · simp_rw [eLpNorm_schrodingerPropagator_toLp_gaussian_top]
    convert memLp_mul_one_add_rpow_iff one_pos ((Module.finrank ℝ E : ℝ) * 2⁻¹) hq0 hq using 2
    · ext t
      rw [ENNReal.toReal_ofReal (by positivity), one_mul]
      ring_nf
    · simp
  · simp_rw [eLpNorm_schrodingerPropagator_toLp_gaussian hr0 hr]
    convert memLp_mul_one_add_rpow_iff (c := r.toReal ^ (-(Module.finrank ℝ E : ℝ) /
      (2 * r.toReal))) (by have := ENNReal.toReal_pos hr0 hr; positivity)
      ((Module.finrank ℝ E : ℝ) * (2⁻¹ - r.toReal⁻¹)) hq0 hq using 2
    ext t
    rw [ENNReal.toReal_ofReal (by have := ENNReal.toReal_pos hr0 hr; positivity)]
    ring_nf

/-- **The evolved Gaussian at the admissible pairs.** If `2/q + n/r = n/2` with `0 < q < ∞`, then
`t ↦ ‖S(t) g‖_r` lies in `L^q(ℝ)` for the Gaussian `g(x) = exp(-π ‖x‖²)`. On the line the
admissible pairs are the `(q, r)` with `4 ≤ q` and `1/r = 1/2 - 2/q`, and `(4, ∞)` is the endpoint
of this range. The non-admissible pair `(2, ∞)`, where `q n (1/2 - 1/r) = 1`, fails
(`TauCeti.memLp_eLpNorm_schrodingerPropagator_toLp_gaussian_iff`). -/
theorem memLp_eLpNorm_schrodingerPropagator_toLp_gaussian_of_admissible {q r : ℝ≥0∞}
    (hq0 : q ≠ 0) (hq : q ≠ ∞) (hr0 : r ≠ 0)
    (hqr : 2 * q.toReal⁻¹ + Module.finrank ℝ E * r.toReal⁻¹ = Module.finrank ℝ E / 2) :
    MemLp (fun t : ℝ ↦ (eLpNorm (schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := π) (by simpa using pi_pos) : 𝓢(E, ℂ)).toLp 2)) r
          volume).toReal) q volume := by
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [memLp_eLpNorm_schrodingerPropagator_toLp_gaussian_iff hq0 hq hr0]
  have : q.toReal * (Module.finrank ℝ E * (2⁻¹ - r.toReal⁻¹)) = 2 := by
    have h2 : (Module.finrank ℝ E : ℝ) * (2⁻¹ - r.toReal⁻¹) = 2 * q.toReal⁻¹ := by linarith
    rw [h2]
    field_simp
  rw [this]
  norm_num

end TauCeti
