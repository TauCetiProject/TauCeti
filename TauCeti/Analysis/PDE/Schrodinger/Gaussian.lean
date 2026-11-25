/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
public import TauCeti.Analysis.PDE.Schrodinger.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Lp
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The Schrödinger evolution of a Gaussian

On a finite-dimensional real inner product space `E` of dimension `n`, the Gaussian
`g_c(x) = exp(-c ‖x‖²)`, `c > 0`, evolves under the Schrödinger propagator
`S(t) = exp(itΔ)` (`TauCeti.schrodingerPropagator`) into the complex Gaussian

`S(t) g_c (x) = (1 + 4ict)^(-n/2) exp(-c ‖x‖² / (1 + 4ict))`

(`TauCeti.coeFn_schrodingerPropagator_toLp_gaussian`), whose modulus is the real Gaussian

`|S(t) g_c (x)| = (1 + 16c²t²)^(-n/4) exp(-c ‖x‖² / (1 + 16c²t²))`.

So `‖S(t) g_c‖_∞ = (1 + 16c²t²)^(-n/4)`. For the self-dual Gaussian `g = g_π` all the Lebesgue
norms are explicit: for `0 < r < ∞`,

`‖S(t) g‖_r = r^(-n/(2r)) (1 + 16π²t²)^(-n (1/2 - 1/r) / 2)`.

At `t = 0` this is `‖g‖_r = r^(-n/(2r))` (`SchwartzMap.eLpNorm_gaussian`), in particular
`‖g‖₁ = 1`. These explicit solutions test the constants and exponents of the dispersive and
Strichartz estimates.

* **The dispersive estimate is sharp.** The dispersive estimate
  `‖S(t) f‖_∞ ≤ (4π|t|)^(-n/2) ‖f‖₁` (`TauCeti.eLpNorm_schrodingerPropagator_le`) is attained by
  `g` as `|t| → ∞`: `(4π|t|)^(n/2) ‖S(t) g‖_∞ → 1 = ‖g‖₁`. Hence neither the decay exponent `n/2`
  nor the constant can be improved: no estimate `‖S(t) f‖_∞ ≤ A |t|^(-n/2) ‖f‖₁` holds with
  `A < (4π)^(-n/2)`.
* **The time integrability of the Strichartz norms.** The function `t ↦ ‖S(t) g‖_r` lies in
  `L^q(ℝ)` exactly when `q n (1/2 - 1/r) > 1`. In particular it does so for every admissible pair
  `2/q + n/r = n/2` with `q < ∞`, where `q n (1/2 - 1/r) = 2`. On the line the Gaussian evolution
  lies in `L⁴_t L^∞_x`, at the endpoint `(4, ∞)` of the admissible range, but not in
  `L²_t L^∞_x`, a non-admissible pair where `q n (1/2 - 1/r) = 1`.
* **Scaling forces admissibility.** The Gaussians are dilates of one another,
  `S(t) g_c (x) = S(ct) g_1 (√c x)`, so `‖S(·) g_c‖_{L^q_t L^r_x} = c^(-n/(2r) - 1/q) ‖S(·) g_1‖`
  while `‖g_c‖₂ = c^(-n/4) ‖g_1‖₂`. A homogeneous Strichartz estimate
  `‖S(·) f‖_{L^q_t L^r_x} ≤ C ‖f‖₂` on the whole time line, applied to every `g_c`, therefore
  forces the two powers of `c` to agree: `2/q + n/r = n/2`. No pair of exponents off this line
  admits such an estimate.
* **The endpoint `r = ∞`.** On the line `2/q = n/2`, the time integral of `‖S(t) g_c‖_∞^q` is
  `∫ (1 + 16c²t²)⁻¹ dt = π / (4c)`. In dimension one this is the pair `(4, ∞)`.

## Main declarations

* `TauCeti.coeFn_schrodingerPropagator_toLp_gaussian`: the evolution of `g_c`.
* `TauCeti.ae_norm_schrodingerPropagator_toLp_gaussian`: its modulus.
* `TauCeti.eLpNorm_schrodingerPropagator_toLp_gaussian_top`: its supremum norm, and
  `TauCeti.eLpNorm_schrodingerPropagator_toLp_gaussian`: the `Lʳ` norms of the evolution of `g_π`.
* `TauCeti.tendsto_rpow_mul_eLpNorm_schrodingerPropagator_toLp_gaussian_top`: the dispersive
  estimate is attained in rate, and
  `TauCeti.four_mul_pi_rpow_le_of_eLpNorm_schrodingerPropagator_le`: the dispersive constant
  `(4π)^(-n/2)` cannot be lowered.
* `TauCeti.memLp_eLpNorm_schrodingerPropagator_toLp_gaussian_iff`: the exact range of time
  integrability, and `TauCeti.memLp_eLpNorm_schrodingerPropagator_toLp_gaussian_of_admissible` at
  the admissible pairs.
* `TauCeti.two_mul_inv_add_finrank_mul_inv_eq_of_eLpNorm_schrodingerPropagator_le`: a
  homogeneous Strichartz estimate on the whole time line can only hold for `2/q + n/r = n/2`.
* `TauCeti.eLpNorm_eLpNorm_schrodingerPropagator_toLp_gaussian_top`: the `L^q_t L^∞_x` norm of the
  evolution of `g_c` on the line `2/q = n/2`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.2 (the dispersive estimate) and Section 2.3
  (the scaling condition on the Strichartz exponents).
-/

public section

noncomputable section

open scoped ENNReal NNReal FourierTransform Topology SchwartzMap
open MeasureTheory Filter Complex Module
open Real hiding exp

namespace TauCeti
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The evolution of a Gaussian -/

/-- The evolution `S(s) g_1` of the Gaussian `g_1(y) = exp(-‖y‖²)`, as an explicit function of
`y`. Dilating it by `√c` gives `S(s / c) g_c`. -/
private def profile (s : ℝ) (y : E) : ℂ :=
  (1 + 4 * s * I) ^ (-(finrank ℝ E : ℂ) / 2) * cexp (-‖y‖ ^ 2 / (1 + 4 * s * I))

private theorem ofReal_norm_sqrt_smul_sq {c : ℝ} (hc : 0 < c) (x : E) :
    (‖√c • x‖ : ℂ) ^ 2 = c * ‖x‖ ^ 2 := by
  exact_mod_cast norm_sqrt_smul_sq hc.le x

private theorem profile_mul_sqrt_smul {c : ℝ} (hc : 0 < c) (t : ℝ) (x : E) :
    (1 + 4 * c * t * I) ^ (-(finrank ℝ E : ℂ) / 2) *
        cexp (-c * ‖x‖ ^ 2 / (1 + 4 * c * t * I)) =
      profile (c * t) (√c • x) := by
  rw [profile, ofReal_norm_sqrt_smul_sq hc]
  push_cast
  congr 2 <;> ring

private theorem norm_profile (s : ℝ) (y : E) :
    ‖profile s y‖ = (1 + 16 * s ^ 2) ^ (-(finrank ℝ E : ℝ) / 4) *
      Real.exp (-‖y‖ ^ 2 / (1 + 16 * s ^ 2)) := by
  have hw : (1 + 4 * s * I : ℂ) = ((1 : ℝ) : ℂ) + ((4 * s : ℝ) : ℂ) * I := by push_cast; ring
  have hs : (-(finrank ℝ E : ℂ) / 2) = ((-(finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [profile, norm_mul, hs, norm_cpow_real, norm_exp, hw, norm_add_mul_I,
    Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1
  · congr 1
    · ring
    · ring
  · congr 1
    rw [← ofReal_pow, ← ofReal_neg, div_re, normSq_add_mul_I, ofReal_re, ofReal_im]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, sub_zero, zero_mul,
      add_zero, mul_one]
    field_simp
    ring

private theorem profile_ne_zero (s : ℝ) (y : E) : profile s y ≠ 0 :=
  norm_pos_iff.1 (by rw [norm_profile]; positivity)

private theorem continuous_profile (s : ℝ) : Continuous (profile (E := E) s) := by
  unfold profile
  fun_prop

/-- At time `0` the profile is the Gaussian `exp(-‖y‖²)`. -/
private theorem profile_zero (y : E) :
    profile 0 y = (SchwartzMap.gaussian (b := 1) (by simp) : 𝓢(E, ℂ)) y := by
  simp [profile, SchwartzMap.gaussian_apply]

omit [InnerProductSpace ℝ E] in
private theorem continuous_rpow_mul_rexp_div {u : ℝ} (a : ℝ) :
    Continuous fun x : E ↦ u ^ a * rexp (-π * ‖x‖ ^ 2 / u) := by
  fun_prop

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The Schrödinger evolution of a Gaussian.** For `c > 0`, the Gaussian `g_c(x) = exp(-c ‖x‖²)`
evolves into the complex Gaussian

`S(t) g_c (x) = (1 + 4ict)^(-n/2) exp(-c ‖x‖² / (1 + 4ict))`,

with the principal power. -/
theorem coeFn_schrodingerPropagator_toLp_gaussian {c : ℝ} (hc : 0 < c) (t : ℝ) :
    schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := c) (by simpa using hc) : 𝓢(E, ℂ)).toLp 2) =ᵐ[volume]
      fun x ↦ (1 + 4 * c * t * I) ^ (-(finrank ℝ E : ℂ) / 2) *
        cexp (-c * ‖x‖ ^ 2 / (1 + 4 * c * t * I)) := by
  have hc' : 0 < (c : ℂ).re := by simpa using hc
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
  have hπ0 : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 pi_ne_zero
  set w : ℂ := 1 + 4 * c * t * I
  have hw0 : w ≠ 0 := fun h ↦ by simpa [w] using congrArg re h
  -- The symbol times `𝓕 g_c` is a multiple of the Gaussian with parameter `b = π² w / c`.
  set b : ℂ := ((π ^ 2 / c : ℝ) : ℂ) * w
  have hb : 0 < b.re := by
    have : b.re = π ^ 2 / c := by rw [re_ofReal_mul]; simp [w]
    rw [this]
    positivity
  set a : ℂ := ((π / c : ℝ) : ℂ) ^ ((finrank ℝ E : ℂ) / 2) with ha
  have hfourier : ∀ ξ : E, 𝓕 (𝓕⁻ (a • SchwartzMap.gaussian hb : 𝓢(E, ℂ))) ξ =
      phaseSymbol laplacianSymbol t ξ • 𝓕 (SchwartzMap.gaussian hc' : 𝓢(E, ℂ)) ξ := fun ξ ↦ by
    rw [FourierTransform.fourier_fourierInv_eq, SchwartzMap.fourier_coe]
    have : ⇑(SchwartzMap.gaussian hc' : 𝓢(E, ℂ)) = fun ξ ↦ cexp (-c * ‖ξ‖ ^ 2) :=
      funext (SchwartzMap.gaussian_apply hc')
    rw [this, fourier_gaussian_innerProductSpace hc']
    simp only [smul_apply, SchwartzMap.gaussian_apply, phaseSymbol_apply,
      laplacianSymbol_apply, smul_eq_mul, ha]
    rw [mul_left_comm, ← Complex.exp_add, ofReal_div]
    congr 2
    simp only [b, w]
    push_cast
    field_simp
    ring
  have h := SchwartzMap.toLp_eq_fourierMultiplierCLM_of_fourier_eq_smul _
    (memLp_phaseSymbol (E := E) laplacianSymbol t).coeFn_toLp hfourier
  rw [schrodingerPropagator_def, phasePropagator_def, ← h]
  filter_upwards [(𝓕⁻ (a • SchwartzMap.gaussian hb : 𝓢(E, ℂ))).coeFn_toLp 2] with x hx
  rw [hx, FourierTransform.fourierInv_smul, smul_apply,
    SchwartzMap.fourierInv_gaussian, smul_eq_mul, ← mul_assoc]
  have hw : w.arg ≠ π := (mem_slitPlane_iff_arg.1 (mem_slitPlane_iff.2 (Or.inl (by simp [w])))).1
  congr 1
  · -- `(π / c)^(n/2) (π / b)^(n/2) = w^(-n/2)`, since `π / b = (π / c)⁻¹ w⁻¹`.
    have hb' : (π : ℂ) / b = ((π / c : ℝ) : ℂ)⁻¹ * w⁻¹ := by
      simp only [b]
      push_cast
      field_simp
    rw [hb', ha, ofReal_cpow_mul_inv_mul_inv_cpow (by positivity) hw, neg_div]
  · congr 1
    simp only [b, w]
    push_cast
    field_simp

/-- **The modulus of the evolved Gaussian:**
`|S(t) g_c (x)| = (1 + 16c²t²)^(-n/4) exp(-c ‖x‖² / (1 + 16c²t²))` almost everywhere. -/
theorem ae_norm_schrodingerPropagator_toLp_gaussian {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∀ᵐ x ∂volume, ‖schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := c) (by simpa using hc) : 𝓢(E, ℂ)).toLp 2) x‖ =
      (1 + 16 * c ^ 2 * t ^ 2) ^ (-(finrank ℝ E : ℝ) / 4) *
        Real.exp (-c * ‖x‖ ^ 2 / (1 + 16 * c ^ 2 * t ^ 2)) := by
  filter_upwards [coeFn_schrodingerPropagator_toLp_gaussian hc t] with x hx
  rw [hx, profile_mul_sqrt_smul hc, norm_profile, norm_sqrt_smul_sq hc.le]
  congr 2 <;> ring

/-! ### Lebesgue norms of the evolved Gaussian -/

/-- The `Lʳ` norm of the evolution of `g_c` at time `t` is `c^(-n/(2r))` times that of the
profile at time `ct`. -/
private theorem eLpNorm_schrodingerPropagator_toLp_gaussian_eq_profile {c : ℝ} (hc : 0 < c)
    (t : ℝ) (r : ℝ≥0∞) :
    eLpNorm (schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := c) (by simpa using hc) : 𝓢(E, ℂ)).toLp 2)) r volume =
      ENNReal.ofReal ((√c)⁻¹ ^ ((finrank ℝ E : ℝ) / r.toReal)) *
        eLpNorm (profile (E := E) (c * t)) r volume := by
  have hs : (√c)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hc).ne'
  rw [eLpNorm_congr_ae (coeFn_schrodingerPropagator_toLp_gaussian hc t)]
  simp_rw [profile_mul_sqrt_smul hc]
  have h := Measure.eLpNorm_comp_inv_smul (volume : Measure E) (profile (c * t)) hs r
  rw [inv_inv] at h
  rw [h, abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hc))]

private theorem eLpNorm_profile_top (s : ℝ) :
    eLpNorm (profile (E := E) s) ∞ volume =
      ENNReal.ofReal ((1 + 16 * s ^ 2) ^ (-(finrank ℝ E : ℝ) / 4)) := by
  rw [eLpNorm_exponent_top (continuous_profile s).aestronglyMeasurable]
  refine le_antisymm (eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun y ↦ ?_)) ?_
  · rw [norm_profile]
    refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) (by positivity)
  · -- The essential supremum dominates the continuous function `‖profile s ·‖ₑ` everywhere.
    have hle : ‖profile (E := E) s 0‖ₑ ≤ eLpNormEssSup (profile s) volume :=
      (Continuous.ae_le_iff_le volume (continuous_profile s).eNorm continuous_const).1
        (ae_le_eLpNormEssSup (f := profile (E := E) s) (μ := volume)) 0
    rw [← ofReal_norm, norm_profile] at hle
    simpa using hle

/-- **The supremum norm of the evolved Gaussian:** `‖S(t) g_c‖_∞ = (1 + 16c²t²)^(-n/4)`. -/
theorem eLpNorm_schrodingerPropagator_toLp_gaussian_top {c : ℝ} (hc : 0 < c) (t : ℝ) :
    eLpNorm (schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := c) (by simpa using hc) : 𝓢(E, ℂ)).toLp 2)) ∞ volume =
      ENNReal.ofReal ((1 + 16 * c ^ 2 * t ^ 2) ^ (-(finrank ℝ E : ℝ) / 4)) := by
  rw [eLpNorm_schrodingerPropagator_toLp_gaussian_eq_profile hc t, eLpNorm_profile_top,
    ENNReal.toReal_top, div_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul, mul_pow, ← mul_assoc]

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

/-- The `Lʳ` norms of the evolved Gaussian are those of the real Gaussian giving its modulus. -/
private theorem eLpNorm_schrodingerPropagator_toLp_gaussian_eq (t : ℝ) (r : ℝ≥0∞) :
    eLpNorm (schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := π) (by simpa using pi_pos) : 𝓢(E, ℂ)).toLp 2)) r volume =
      eLpNorm (fun x : E ↦ (1 + 16 * π ^ 2 * t ^ 2) ^ (-(Module.finrank ℝ E : ℝ) / 4) *
        rexp (-π * ‖x‖ ^ 2 / (1 + 16 * π ^ 2 * t ^ 2))) r volume := by
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
    (continuous_rpow_mul_rexp_div _).aestronglyMeasurable ?_
  filter_upwards [ae_norm_schrodingerPropagator_toLp_gaussian (E := E) pi_pos t] with x hx
  rw [hx, Real.norm_of_nonneg (by positivity)]

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
  rw [eLpNorm_schrodingerPropagator_toLp_gaussian_top pi_pos, ENNReal.toReal_ofReal (by positivity),
    Function.comp_apply, key]

/-- **The dispersive constant is sharp.** If `‖S(t) f‖_∞ ≤ A |t|^(-n/2) ‖f‖₁` for every `t > 0`
and every integrable `f ∈ L²`, then `A ≥ (4π)^(-n/2)`, the constant of
`TauCeti.eLpNorm_schrodingerPropagator_le`. The Gaussian `g_π` has `‖g_π‖₁ = 1` and
`‖S(t) g_π‖_∞ = (1 + 16π²t²)^(-n/4)`, which is `(4π|t|)^(-n/2)` to leading order as
`t → ∞`. -/
theorem four_mul_pi_rpow_le_of_eLpNorm_schrodingerPropagator_le {A : ℝ}
    (h : ∀ t : ℝ, 0 < t → ∀ f : Lp ℂ 2 (volume : Measure E), Integrable f volume →
      eLpNorm (schrodingerPropagator ℂ t f) ∞ volume ≤
        ENNReal.ofReal (A * |t| ^ (-(finrank ℝ E : ℝ) / 2)) * eLpNorm f 1 volume) :
    (4 * π) ^ (-(finrank ℝ E : ℝ) / 2) ≤ A := by
  set n : ℝ := (finrank ℝ E : ℝ)
  set g : 𝓢(E, ℂ) := SchwartzMap.gaussian (b := π) (by simpa using pi_pos)
  have hg : Integrable (g.toLp 2 (μ := volume)) volume :=
    (g.integrable (μ := volume)).congr (g.coeFn_toLp 2 volume).symm
  -- `g_π` has unit mass.
  have hg1 : eLpNorm (g.toLp 2 (μ := volume)) 1 volume = 1 := by
    rw [eLpNorm_congr_ae (g.coeFn_toLp 2 volume),
      SchwartzMap.eLpNorm_gaussian _ one_ne_zero ENNReal.one_ne_top]
    simp [pi_ne_zero]
  -- For `u > 0`, testing at `t = u⁻¹` gives `(u² + 16π²)^(-n/4) ≤ A`.
  have key : ∀ u : ℝ, 0 < u → (u ^ 2 + 16 * π ^ 2) ^ (-n / 4) ≤ A := fun u hu ↦ by
    have hu2 : 0 < u ^ 2 := by positivity
    have ht := h u⁻¹ (inv_pos.2 hu) _ hg
    rw [eLpNorm_schrodingerPropagator_toLp_gaussian_top pi_pos, hg1, mul_one,
      ENNReal.ofReal_le_ofReal_iff'] at ht
    have hlhs : (1 + 16 * π ^ 2 * u⁻¹ ^ 2) ^ (-n / 4) =
        (u ^ 2 + 16 * π ^ 2) ^ (-n / 4) * (u ^ 2) ^ (n / 4) := by
      rw [show 1 + 16 * π ^ 2 * u⁻¹ ^ 2 = (u ^ 2 + 16 * π ^ 2) * (u ^ 2)⁻¹ by
          field_simp,
        Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hu2.le, ← Real.rpow_neg hu2.le,
        neg_div, neg_neg]
    have hrhs : |u⁻¹| ^ (-n / 2) = (u ^ 2) ^ (n / 4) := by
      rw [abs_of_pos (inv_pos.2 hu), Real.inv_rpow hu.le, ← Real.rpow_neg hu.le,
        ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
      congr 1
      push_cast
      ring
    have hpos : 0 < (u ^ 2 + 16 * π ^ 2) ^ (-n / 4) * (u ^ 2) ^ (n / 4) := by positivity
    rcases ht with ht | ht
    · rw [hlhs, hrhs] at ht
      exact le_of_mul_le_mul_right ht (by positivity)
    · rw [hlhs] at ht
      exact absurd ht (not_le.2 hpos)
  -- Let `u → 0⁺`.
  have hcont : ContinuousAt (fun u : ℝ ↦ (u ^ 2 + 16 * π ^ 2) ^ (-n / 4)) 0 :=
    (continuousAt_id.pow 2 |>.add continuousAt_const).rpow_const
      (Or.inl (by positivity : (0 : ℝ) ^ 2 + 16 * π ^ 2 ≠ 0))
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hle := le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun u hu ↦ key u hu)
  have h0 : ((0 : ℝ) ^ 2 + 16 * π ^ 2) ^ (-n / 4) = (4 * π) ^ (-n / 2) := by
    rw [show -n / 2 = 2 * (-n / 4) by ring, Real.rpow_mul (by positivity), Real.rpow_two]
    congr 1
    ring
  rwa [h0] at hle

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
  · simp_rw [eLpNorm_schrodingerPropagator_toLp_gaussian_top pi_pos]
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

/-! ### Scaling forces admissibility -/

private theorem eLpNorm_profile_ne_zero (s : ℝ) {r : ℝ≥0∞} (hr : r ≠ 0) :
    eLpNorm (profile (E := E) s) r volume ≠ 0 := by
  rw [Ne, eLpNorm_eq_zero_iff hr]
  intro h0
  obtain ⟨y, hy⟩ := h0.exists
  exact profile_ne_zero s y hy

/-- The `L^q_t L^r_x` norm of the evolution of `g_c` is `c^(-n/(2r) - 1/q)` times that of the
profile. -/
private theorem eLpNorm_eLpNorm_schrodingerPropagator_toLp_gaussian {c : ℝ} (hc : 0 < c)
    {q : ℝ≥0∞} (hq : q ≠ 0) (r : ℝ≥0∞) :
    eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := c) (by simpa using hc) : 𝓢(E, ℂ)).toLp 2)) r volume) q
        volume =
      ENNReal.ofReal (c ^ (-((finrank ℝ E : ℝ) / r.toReal) / 2) * c ^ (-q.toReal⁻¹)) *
        eLpNorm (fun t ↦ eLpNorm (profile (E := E) t) r volume) q volume := by
  simp_rw [eLpNorm_schrodingerPropagator_toLp_gaussian_eq_profile hc _ r]
  rw [eLpNorm_const_mul_ennreal_of_pos (pos_iff_ne_zero.2 hq)]
  -- Dilate the time variable by `c`.
  have htime := Measure.eLpNorm_comp_inv_smul volume
    (fun t ↦ eLpNorm (profile (E := E) t) r volume) (inv_ne_zero hc.ne') q
  simp only [inv_inv, smul_eq_mul, finrank_self, Nat.cast_one] at htime
  -- The space dilation contributes `c^(-n/(2r))` and the time dilation `c^(-1/q)`.
  have hpow : (√c)⁻¹ ^ ((finrank ℝ E : ℝ) / r.toReal) * |c⁻¹| ^ (1 / q.toReal) =
      c ^ (-((finrank ℝ E : ℝ) / r.toReal) / 2) * c ^ (-q.toReal⁻¹) := by
    simp [Real.inv_sqrt_rpow_eq_rpow hc.le, abs_of_pos hc, Real.inv_rpow hc.le,
      Real.rpow_neg hc.le]
  rw [htime, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hpow]

/-- The `L²` norm of `g_c` is `c^(-n/4)` times that of `g_1`, the profile at time `0`. -/
private theorem eNorm_toLp_gaussian {c : ℝ} (hc : 0 < c) :
    ‖(SchwartzMap.gaussian (b := c) (by simpa using hc) : 𝓢(E, ℂ)).toLp 2 (μ := volume)‖ₑ =
      ENNReal.ofReal (c ^ (-((finrank ℝ E : ℝ) / 2) / 2)) *
        eLpNorm (profile (E := E) 0) 2 volume := by
  rw [Lp.eNorm_def, eLpNorm_congr_ae (SchwartzMap.coeFn_toLp _ 2 volume)]
  have hfun : ⇑(SchwartzMap.gaussian (b := c) (by simpa using hc) : 𝓢(E, ℂ)) =
      fun x ↦ profile (E := E) 0 ((√c)⁻¹⁻¹ • x) := funext fun x ↦ by
    rw [profile_zero, inv_inv, SchwartzMap.gaussian_apply, SchwartzMap.gaussian_apply,
      ofReal_norm_sqrt_smul_sq hc]
    congr 1
    ring
  rw [hfun, Measure.eLpNorm_comp_inv_smul volume _ (inv_ne_zero (Real.sqrt_pos.2 hc).ne'),
    abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hc)), Real.inv_sqrt_rpow_eq_rpow hc.le,
    ENNReal.toReal_ofNat]

/-- **Scaling forces admissibility.** If the homogeneous Strichartz estimate
`‖S(·) f‖_{L^q_t L^r_x} ≤ C ‖f‖₂` holds on the whole time line for every `f ∈ L²`, with
`q, r ≠ 0`, then `(q, r)` lies on the admissible line `2/q + n/r = n/2`. Testing the estimate on
the Gaussians `g_c`, the left side scales like `c^(-n/(2r) - 1/q)` and the right side like
`c^(-n/4)`, and the two powers must agree. -/
theorem two_mul_inv_add_finrank_mul_inv_eq_of_eLpNorm_schrodingerPropagator_le {q r : ℝ≥0∞}
    (hq : q ≠ 0) (hr : r ≠ 0) {C : ℝ≥0}
    (h : ∀ f : Lp ℂ 2 (volume : Measure E),
      eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ t f) r volume) q volume ≤ C * ‖f‖ₑ) :
    2 * (q⁻¹).toReal + finrank ℝ E * (r⁻¹).toReal = finrank ℝ E / 2 := by
  set n : ℝ := (finrank ℝ E : ℝ)
  set Φ : ℝ≥0∞ := eLpNorm (fun t ↦ eLpNorm (profile (E := E) t) r volume) q volume
  set Γ : ℝ≥0∞ := eLpNorm (profile (E := E) 0) 2 volume with hΓdef
  have hΦ0 : Φ ≠ 0 := by
    rw [Ne, eLpNorm_eq_zero_iff hq]
    intro h0
    obtain ⟨t, ht⟩ := h0.exists
    exact eLpNorm_profile_ne_zero t hr ht
  have hΓ : Γ ≠ ∞ := by
    rw [hΓdef, show profile (E := E) 0 = (SchwartzMap.gaussian (b := 1) (by simp) : 𝓢(E, ℂ))
      from funext profile_zero]
    exact (SchwartzMap.memLp _ 2 volume).eLpNorm_ne_top
  -- The estimate for `g_c`, as powers of `c` times `Φ` and `Γ`.
  have hscale : ∀ c : ℝ, 0 < c →
      ENNReal.ofReal (c ^ (-(n / r.toReal) / 2) * c ^ (-q.toReal⁻¹)) * Φ ≤
        C * (ENNReal.ofReal (c ^ (-(n / 2) / 2)) * Γ) := fun c hc ↦ by
    have hsp := h ((SchwartzMap.gaussian (b := c) (by simpa using hc) : 𝓢(E, ℂ)).toLp 2)
    rwa [eLpNorm_eLpNorm_schrodingerPropagator_toLp_gaussian hc hq, eNorm_toLp_gaussian hc] at hsp
  have hΦ : Φ ≠ ∞ := by
    intro hΦt
    have h1 := hscale 1 one_pos
    simp only [Real.one_rpow, mul_one, ENNReal.ofReal_one, one_mul, hΦt] at h1
    exact (ENNReal.mul_ne_top ENNReal.coe_ne_top hΓ) (top_le_iff.1 h1)
  have hΦr : 0 < Φ.toReal := ENNReal.toReal_pos hΦ0 hΦ
  -- In real terms: `c ^ e ≤ C Γ / Φ` with `e = n/4 - n/(2r) - 1/q`, so `e = 0`.
  have he := Real.eq_zero_of_forall_rpow_le (K := C * Γ.toReal / Φ.toReal)
    (e := n / 4 - n / r.toReal / 2 - q.toReal⁻¹) fun c hc ↦ by
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΓ))
      (hscale c hc)
    have h1 : 0 ≤ c ^ (-(n / r.toReal) / 2) * c ^ (-q.toReal⁻¹) := by positivity
    have h2 : 0 ≤ c ^ (-(n / 2) / 2) := by positivity
    simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal h1,
      ENNReal.toReal_ofReal h2] at hreal
    have hsplit : c ^ (-(n / r.toReal) / 2) * c ^ (-q.toReal⁻¹) =
        c ^ (-(n / 2) / 2) * c ^ (n / 4 - n / r.toReal / 2 - q.toReal⁻¹) := by
      rw [← Real.rpow_add hc, ← Real.rpow_add hc]
      congr 1
      ring
    rw [hsplit, mul_assoc, mul_left_comm (C : ℝ)] at hreal
    rw [le_div_iff₀ hΦr]
    exact le_of_mul_le_mul_left hreal (by positivity)
  rw [ENNReal.toReal_inv, ENNReal.toReal_inv]
  rw [div_eq_mul_inv n r.toReal] at he
  linarith

/-! ### The endpoint `r = ∞` -/

/-- **The `L^q_t L^∞_x` norm of the evolved Gaussian at the endpoint `r = ∞`.** On the line
`2/q = n/2`, that is `q n = 4`, the evolution of `g_c` has `∫ ‖S(t) g_c‖_∞^q dt = π / (4c)`.
In dimension one this is the admissible pair `(4, ∞)`. -/
theorem eLpNorm_eLpNorm_schrodingerPropagator_toLp_gaussian_top {c : ℝ} (hc : 0 < c)
    {q : ℝ≥0∞} (hq : q.toReal * finrank ℝ E = 4) :
    eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := c) (by simpa using hc) : 𝓢(E, ℂ)).toLp 2)) ∞ volume) q
        volume =
      ENNReal.ofReal ((π / (4 * c)) ^ q.toReal⁻¹) := by
  have hq0 : q.toReal ≠ 0 := fun h ↦ by simp [h] at hq
  have hqpos : 0 < q.toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hq0)
  simp_rw [eLpNorm_schrodingerPropagator_toLp_gaussian_top hc]
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦
      ENNReal.ofReal ((1 + 16 * c ^ 2 * t ^ 2) ^ (-(finrank ℝ E : ℝ) / 4))) volume :=
    (ENNReal.continuous_ofReal.comp (Continuous.rpow_const (by fun_prop)
      fun t ↦ Or.inl (by positivity))).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (fun h ↦ hq0 (by simp [h]))
    (fun h ↦ hq0 (by simp [h])) hmeas]
  -- The integrand is `(1 + (4ct)²)⁻¹`.
  have hint : ∀ t : ℝ, ‖ENNReal.ofReal ((1 + 16 * c ^ 2 * t ^ 2) ^ (-(finrank ℝ E : ℝ) / 4))‖ₑ ^
      q.toReal = ENNReal.ofReal (1 + (4 * c * t) ^ 2)⁻¹ := fun t ↦ by
    rw [eNorm_eq_self, ENNReal.ofReal_rpow_of_nonneg (by positivity) hqpos.le,
      ← Real.rpow_mul (by positivity), show -(finrank ℝ E : ℝ) / 4 * q.toReal = -1 by
        linarith, Real.rpow_neg_one]
    congr 2
    ring
  simp_rw [hint]
  have hI : Integrable (fun t : ℝ ↦ (1 + (4 * c * t) ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.comp_mul_left' (by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun t ↦ by positivity),
    Measure.integral_comp_mul_left (fun t : ℝ ↦ (1 + t ^ 2)⁻¹) (4 * c),
    integral_univ_inv_one_add_sq, smul_eq_mul, abs_of_pos (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div]
  congr 2
  field_simp

end TauCeti
