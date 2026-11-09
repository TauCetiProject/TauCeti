/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.SpectralGap
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Exp
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.MeasureTheory.Integral.MeanInequalities

/-!
# Weighted energy estimates for the plane-vortex adjoint

Multiplication by a real weight gives an exact localization identity for the gauge-fixed
vortex adjoint. Its error is the squared gradient of the weight, with coefficient one.
Combining this identity with exterior coercivity gives the weighted energy estimate for
`L_x L_x*`, with margin `a - c²` when the squared exterior mass is `a` and the logarithmic
weight has gradient bounded by `c`. In particular, exponential weights with rate below
`1/2` are allowed sufficiently far out on a vortex with unit-modulus end.

The second half of the file removes the exterior restriction. With `ρ = √(1 + |z|²)` and
`|c| < 1/2`, every compactly supported `C²` field `η` satisfies

`‖exp(c ρ) η‖₂ + ‖exp(c ρ) L_x* η‖₂ ≤ K ‖exp(c ρ) L_x L_x* η‖₂`,

with `K` depending only on the vortex and `c`
(`exists_integral_exp_mul_norm_sq_le_mul_integral_exp_mul_norm_sq_gaugeFixedOperator`,
`exists_integral_exp_mul_norm_sq_gaugeFixedAdjoint_le_mul_integral_exp_mul_norm_sq`).
For `f = L_x L_x* η` the field `L_x* η` is the value at `f` of the right inverse
`L_x* (L_x L_x*)⁻¹`, so this is the exponentially weighted output estimate for that inverse on
such inputs. The proof combines two coercivity statements by an IMS-type localization. On a
large disc the spectral gap of `L_x L_x*`
(`exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint`) controls the field,
provided the weight is nearly flat there; the weight `W = exp(c √(b + |z|²))` with `b` large is,
and it is comparable to `exp(c ρ)`. Outside the disc the exterior mass `a > c²` controls it. The two
pieces are `W cos θ` and `W sin θ` for an angle `θ` rising slowly from `0` to `π / 2`, so their
squares add up to `W²` and the localization identities for them add up exactly.

The coercivity statement behind these estimates allows every weight whose logarithmic gradient
is at most that of `W`, including the bounded weights `W / (1 + ε W)`
(`exists_pos_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator`). With
the weighted adjoint energy bound `integral_sq_mul_norm_sq_gaugeFixedAdjoint_le`, this is what
`TauCeti.Analysis.PDE.Vortex.RightInverse` uses to extend the weighted estimate from test fields to
the weak right inverse on all of `L²`.

All estimates here concern compactly supported classical test fields. They are not a
construction of a completed inverse or a uniform spectral gap over the noncompact vortex moduli
space.

## Main results

All in the namespace `TauCeti.Vortex`:

* `integral_norm_sq_gaugeFixedAdjoint_fun_smul`: the localization identity.
* `integral_sq_mul_norm_sq_gaugeFixedAdjoint_le`: the weighted energy of `L_x* η` is controlled
  by the weighted pairing with `L_x L_x*`.
* `exists_exterior_integral_exp_mul_norm_sq_le_integral_exp_mul_inner_gaugeFixedOperator`:
  the exterior weighted estimate.
* `exists_pos_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator`: the
  weighted coercivity of `L_x L_x*` for weights flat on a large disc.
* `exists_integral_exp_mul_norm_sq_le_mul_integral_exp_mul_norm_sq_gaugeFixedOperator` and
  `exists_integral_exp_mul_norm_sq_gaugeFixedAdjoint_le_mul_integral_exp_mul_norm_sq`:
  the global weighted estimates for `η` and `L_x* η` in terms of `L_x L_x* η`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Chapter III.
-/
public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter
open scoped Laplacian Topology RealInnerProductSpace Real

variable {x η : ℂ → EuclideanSpace ℝ (Fin 4)} {w : ℂ → ℝ}

/-- Exact localization of the squared adjoint norm. The zeroth-order vortex coefficients
cancel, and the principal symbol contributes precisely `|dw|² |η|²`. No equation for `x`
is needed. -/
theorem norm_sq_gaugeFixedAdjoint_fun_smul (x : ℂ → EuclideanSpace ℝ (Fin 4)) {z : ℂ}
    (hw : DifferentiableAt ℝ w z) (hη : DifferentiableAt ℝ η z) :
    ‖gaugeFixedAdjoint x (fun t ↦ w t • η t) z‖ ^ 2 =
      ⟪gaugeFixedAdjoint x (fun t ↦ w t ^ 2 • η t) z, gaugeFixedAdjoint x η z⟫ +
        ‖fderiv ℝ w z‖ ^ 2 * ‖η z‖ ^ 2 := by
  have hp : fderiv ℝ (fun t ↦ w t ^ 2) z = (2 * w z) • fderiv ℝ w z := by
    simpa using (hw.hasFDerivAt.pow 2).fderiv
  rw [gaugeFixedAdjoint_fun_smul x hw hη,
    gaugeFixedAdjoint_fun_smul x (hw.fun_pow 2) hη, hp, gaugeFixedAdjointSymbol_smul_left]
  simp only [norm_add_sq_real, inner_add_left, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, norm_sq_gaugeFixedAdjointSymbol, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm]
  ring

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure]

private theorem integrable_weightGradientError (hw : ContDiff ℝ 1 w)
    (hη : Continuous η) (hc : HasCompactSupport η) :
    Integrable (fun z ↦ ‖fderiv ℝ w z‖ ^ 2 * ‖η z‖ ^ 2) μ := by
  exact (by fun_prop : Continuous (fun z ↦
    ‖fderiv ℝ w z‖ ^ 2 * ‖η z‖ ^ 2)).integrable_of_hasCompactSupport
      (hc.mono fun z hz hzero ↦ hz (by simp [hzero]))

/-- The integrated localization identity: the weighted pairing with `L_x L_x*` equals
the localized adjoint energy minus the exact weight-gradient error. -/
theorem integral_norm_sq_gaugeFixedAdjoint_fun_smul
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η)
    (hw : ContDiff ℝ 1 w) :
    (∫ z, ‖gaugeFixedAdjoint x (fun t ↦ w t • η t) z‖ ^ 2 ∂μ) =
      (∫ z, w z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ) +
        ∫ z, ‖fderiv ℝ w z‖ ^ 2 * ‖η z‖ ^ 2 ∂μ := by
  have hη₁ : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hA := contDiff_gaugeFixedAdjoint hx hη
  have hAc := hasCompactSupport_gaugeFixedAdjoint (x := x) hc
  have hi : Integrable (fun z ↦
      ⟪gaugeFixedAdjoint x (fun t ↦ w t ^ 2 • η t) z, gaugeFixedAdjoint x η z⟫) μ :=
    ((continuous_gaugeFixedAdjoint hx.continuous ((hw.pow 2).smul hη₁)).inner
      hA.continuous).integrable_of_hasCompactSupport
        (hAc.mono fun z hz he ↦ hz (by simp [he]))
  have he := integrable_weightGradientError (μ := μ) hw hη.continuous hc
  simp_rw [norm_sq_gaugeFixedAdjoint_fun_smul x (hw.differentiable (by norm_num) _)
    (hη.differentiable (by norm_num) _)]
  rw [integral_add hi he]
  congr 1
  have hg := integral_inner_gaugeFixedOperator (μ := μ) (x := x) hA hAc
    ((hw.pow 2).smul hη₁)
  simpa only [Pi.smul_def', real_inner_smul_right, real_inner_comm] using hg.symm

/-- **Weighted adjoint energy.** If the weight `w` has logarithmic gradient at most `|c|`, the
weighted energy of `L_x* η` is controlled by the weighted pairing with `L_x L_x*`:
`∫ w² |L_x* η|² ≤ 2 ∫ w² ⟪L_x L_x* η, η⟫ + 4 c² ∫ w² |η|²`. No equation for `x` is needed. -/
theorem integral_sq_mul_norm_sq_gaugeFixedAdjoint_le
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η)
    (hw : ContDiff ℝ 1 w) {c : ℝ} (hdw : ∀ z, ‖fderiv ℝ w z‖ ^ 2 ≤ c ^ 2 * w z ^ 2) :
    ∫ z, w z ^ 2 * ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ ≤
      2 * (∫ z, w z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ) +
        4 * c ^ 2 * ∫ z, w z ^ 2 * ‖η z‖ ^ 2 ∂μ := by
  have hη₁ : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hA := contDiff_gaugeFixedAdjoint hx hη
  have hAs := hasCompactSupport_gaugeFixedAdjoint (x := x) hc
  have hwη : HasCompactSupport fun t ↦ w t • η t :=
    hc.mono fun z hz hzero ↦ hz (by simp [hzero])
  have hi {f : ℂ → ℝ} (hf : Continuous f) : Integrable (fun z ↦ f z * ‖η z‖ ^ 2) μ :=
    (hf.mul (hη.continuous.norm.pow 2)).integrable_of_hasCompactSupport
      (hc.mono fun z hz hzero ↦ hz (by simp [hzero]))
  have iA : Integrable (fun z ↦ w z ^ 2 * ‖gaugeFixedAdjoint x η z‖ ^ 2) μ :=
    ((hw.continuous.pow 2).mul (hA.continuous.norm.pow 2)).integrable_of_hasCompactSupport
      (hAs.mono fun z hz hzero ↦ hz (by simp [hzero]))
  have iS : Integrable (fun z ↦ ‖gaugeFixedAdjoint x (fun t ↦ w t • η t) z‖ ^ 2) μ := by
    have hS : Continuous fun z ↦ ‖gaugeFixedAdjoint x (fun t ↦ w t • η t) z‖ ^ 2 :=
      (continuous_gaugeFixedAdjoint hx.continuous (hw.smul hη₁)).norm.pow 2
    exact hS.integrable_of_hasCompactSupport
      ((hasCompactSupport_gaugeFixedAdjoint (x := x) hwη).mono fun z hz hzero ↦
        hz (by simp [hzero]))
  have hdc : Continuous fun z ↦ ‖fderiv ℝ w z‖ ^ 2 :=
    ((hw.continuous_fderiv (by simp)).norm).pow 2
  have iD := hi hdc
  -- Pointwise, `w L_x* η = L_x* (w η) - σ(dw) η`.
  have hpt := integral_mono iA ((iS.const_mul 2).add (iD.const_mul 2)) fun z ↦ by
    have hl := gaugeFixedAdjoint_fun_smul x ((hw.differentiable (by simp)) z)
      ((hη.differentiable (by simp)) z)
    have hs := norm_sq_gaugeFixedAdjointSymbol (fderiv ℝ w z) (η z)
    have he : w z • gaugeFixedAdjoint x η z = gaugeFixedAdjoint x (fun t ↦ w t • η t) z -
        gaugeFixedAdjointSymbol (fderiv ℝ w z) (η z) := by
      rw [hl, add_sub_cancel_right]
    have hn : ‖w z • gaugeFixedAdjoint x η z‖ ^ 2 = w z ^ 2 * ‖gaugeFixedAdjoint x η z‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h2 := norm_sub_sq_le_two_mul (gaugeFixedAdjoint x (fun t ↦ w t • η t) z)
      (gaugeFixedAdjointSymbol (fderiv ℝ w z) (η z)) 0
    rw [← he, hn, sub_zero, sub_zero] at h2
    simp only [Pi.add_apply]
    linarith
  rw [integral_add' (iS.const_mul 2) (iD.const_mul 2), integral_const_mul,
    integral_const_mul, integral_norm_sq_gaugeFixedAdjoint_fun_smul hx hη hc hw] at hpt
  have hD := integral_mono iD ((hi (f := fun z ↦ w z ^ 2) (hw.continuous.pow 2)).const_mul
    (c ^ 2)) fun z ↦ by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hdw z) (sq_nonneg ‖η z‖)
  rw [integral_const_mul] at hD
  linarith

/-- A real weight whose logarithmic gradient is bounded by `c` reduces the exterior
squared mass from `a` to `a - c²`. The pairing is with the actual second-order operator
`L_x L_x*`; no inverse or range assertion is assumed. -/
theorem mul_integral_mul_norm_sq_le_integral_mul_inner_gaugeFixedOperator
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η)
    (hw : ContDiff ℝ 2 w) (hsol : ∀ z, η z ≠ 0 → equation x z = 0)
    {a c : ℝ} (ha : a ≤ 1 / 4)
    (hP : ∀ z, η z ≠ 0 → a ≤ x z 2 ^ 2 + x z 3 ^ 2)
    (hdw : ∀ z, η z ≠ 0 →
      ‖fderiv ℝ w z‖ ^ 2 ≤ c ^ 2 * w z ^ 2) :
    (a - c ^ 2) * (∫ z, w z ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
      ∫ z, w z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ := by
  have hloc := mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ)
    hx (hw.smul hη) hc.smul_left (fun z hz ↦ hsol z (fun he ↦ hz (by simp [he]))) ha
    (fun z hz ↦ hP z (fun he ↦ hz (by simp [he])))
  simp only [Pi.smul_def'] at hloc
  rw [integral_norm_sq_gaugeFixedAdjoint_fun_smul hx hη hc (hw.of_le (by norm_num))] at hloc
  have hi : Integrable (fun z ↦ w z ^ 2 * ‖η z‖ ^ 2) μ :=
    ((hw.continuous.pow 2).mul (hη.continuous.norm.pow 2)).integrable_of_hasCompactSupport
      (hc.mono fun z hz hzero ↦ hz (by simp [hzero]))
  have he := integrable_weightGradientError (μ := μ)
    (hw.of_le (by norm_num)) hη.continuous hc
  have hb := integral_mono he (hi.const_mul (c ^ 2)) fun z ↦
    by
      by_cases hz : η z = 0
      · simp [hz]
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hdw z hz) (sq_nonneg ‖η z‖)
  rw [integral_const_mul] at hb
  have hn (z : ℂ) : ‖w z • η z‖ ^ 2 = w z ^ 2 * ‖η z‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp_rw [hn] at hloc
  nlinarith

/-- On a vortex with unit-modulus end, the smooth exponential weight
`exp(c √(1 + |z|²))` has exterior energy margin `a - c²` for every `a < 1/4`.
The margin is positive when `c² < a`. The same radius works for every compactly
supported `C²` test field vanishing on the indicated disc. -/
theorem exists_exterior_integral_exp_mul_norm_sq_le_integral_exp_mul_inner_gaugeFixedOperator
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {a c : ℝ} (ha : a < 1 / 4) :
    ∃ R > 0, ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η →
      HasCompactSupport η → (∀ z, ‖z‖ ≤ R → η z = 0) →
      (a - c ^ 2) *
          (∫ z, Real.exp (c * √(1 + ‖z‖ ^ 2)) ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
        ∫ z, Real.exp (c * √(1 + ‖z‖ ^ 2)) ^ 2 *
          ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ := by
  obtain ⟨R, hR₀, hR⟩ := exists_exterior_lt_mass hlim ha
  have hw : ContDiff ℝ 2 (fun z : ℂ ↦ Real.exp (c * √(1 + ‖z‖ ^ 2))) :=
    contDiff_exp_mul_sqrt_add_norm_sq c one_pos
  have hdw (z : ℂ) :
      ‖fderiv ℝ (fun t : ℂ ↦ Real.exp (c * √(1 + ‖t‖ ^ 2))) z‖ ^ 2 ≤
        c ^ 2 * Real.exp (c * √(1 + ‖z‖ ^ 2)) ^ 2 := by
    have hb := norm_fderiv_exp_mul_sqrt_add_norm_sq_le c one_pos z
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    simpa only [mul_pow, sq_abs] using hs
  refine ⟨R, hR₀, fun η hη hηc hzero ↦ ?_⟩
  have hP (z : ℂ) (hz : η z ≠ 0) : a ≤ x z 2 ^ 2 + x z 3 ^ 2 :=
    (hR z (lt_of_not_ge fun h ↦ hz (hzero z h))).le
  exact mul_integral_mul_norm_sq_le_integral_mul_inner_gaugeFixedOperator (μ := μ)
    hx hη hηc hw (fun z _ ↦ hsol z) ha.le hP (fun z _ ↦ hdw z)

/-! ### The global weighted estimate -/

/-- Splitting of the weighted pairing: for `v₁² + v₂² = W²`, the pairing
`W² ⟪L_x L_x* η, η⟫` is the sum of the two localized pairings. -/
private theorem integral_sq_mul_inner_gaugeFixedOperator_eq_add
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η)
    {v₁ v₂ W : ℂ → ℝ} (hv₁ : Continuous v₁) (hv₂ : Continuous v₂)
    (hW : ∀ z, W z ^ 2 = v₁ z ^ 2 + v₂ z ^ 2) :
    (∫ z, W z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ) =
      (∫ z, v₁ z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ) +
        ∫ z, v₂ z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ := by
  have hG : Continuous fun z ↦ ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ :=
    (continuous_gaugeFixedOperator hx.continuous (contDiff_gaugeFixedAdjoint hx hη)).inner
      hη.continuous
  have hi {v : ℂ → ℝ} (hv : Continuous v) : Integrable (fun z ↦
      v z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫) μ :=
    ((hv.pow 2).mul hG).integrable_of_hasCompactSupport
      (hc.mono fun z hz hzero ↦ hz (by simp [hzero]))
  rw [← integral_add (hi hv₁) (hi hv₂)]
  simp_rw [hW, add_mul]

/-- The pointwise margin on the disc: if the weight `W` and the angle `t` have small
gradients `A` and `e`, then the localized weights `W cos t`, `W sin t` with gradients `g₁`, `g₂`
keep half of the smaller of the two masses. -/
private theorem half_mul_le_of_norm_le {m c₀ a W A e t g₁ g₂ : ℝ} (hm₀ : m ≤ c₀) (hma : m ≤ a)
    (hA : 0 ≤ A) (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂)
    (hA2 : A ^ 2 ≤ m / 16 * W ^ 2) (he2 : e ^ 2 ≤ m / 16)
    (h₁ : g₁ ≤ W * e + |Real.cos t| * A) (h₂ : g₂ ≤ W * e + |Real.sin t| * A) :
    m / 2 * W ^ 2 ≤ c₀ * (W * Real.cos t) ^ 2 + a * (W * Real.sin t) ^ 2 - (g₁ ^ 2 + g₂ ^ 2) := by
  have h₁' : g₁ ≤ W * e + A := h₁.trans (by
    have := mul_le_of_le_one_left hA (Real.abs_cos_le_one t)
    linarith)
  have h₂' : g₂ ≤ W * e + A := h₂.trans (by
    have := mul_le_of_le_one_left hA (Real.abs_sin_le_one t)
    linarith)
  have hs : (W * e + A) ^ 2 ≤ m / 4 * W ^ 2 := by
    have := sq_nonneg (W * e - A)
    nlinarith [mul_le_mul_of_nonneg_left he2 (sq_nonneg W)]
  have hg : g₁ ^ 2 + g₂ ^ 2 ≤ m / 2 * W ^ 2 := by
    have := pow_le_pow_left₀ hg₁ h₁' 2
    have := pow_le_pow_left₀ hg₂ h₂' 2
    linarith
  have hcs : W ^ 2 = (W * Real.cos t) ^ 2 + (W * Real.sin t) ^ 2 := by
    rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  have hm₁ := mul_le_mul_of_nonneg_right hm₀ (sq_nonneg (W * Real.cos t))
  have hm₂ := mul_le_mul_of_nonneg_right hma (sq_nonneg (W * Real.sin t))
  rw [hcs] at hg ⊢
  linarith

/-- Integrating a pointwise margin: if `W² = v₁² + v₂²`, `v₂` is supported where the exterior
mass is at least `a`, and `δ W²` is bounded by `c₀ v₁² + a v₂²` minus the squared gradients of
`v₁` and `v₂`, then the spectral gap `c₀` for `v₁ η` and the exterior estimate for `v₂ η` give
`δ ∫ W² |η|² ≤ ∫ W² ⟪L_x L_x* η, η⟫`. -/
private theorem mul_integral_sq_mul_norm_sq_le_of_forall_le
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0) {c₀ : ℝ}
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c₀ * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ)
    {a δ : ℝ} (ha : a ≤ 1 / 4) {v₁ v₂ W : ℂ → ℝ} (hv₁ : ContDiff ℝ 2 v₁)
    (hv₂ : ContDiff ℝ 2 v₂) (hW : Continuous W) (hsq : ∀ z, W z ^ 2 = v₁ z ^ 2 + v₂ z ^ 2)
    (hP : ∀ z, v₂ z ≠ 0 → a ≤ x z 2 ^ 2 + x z 3 ^ 2)
    (hkey : ∀ z, δ * W z ^ 2 ≤
      c₀ * v₁ z ^ 2 + a * v₂ z ^ 2 - (‖fderiv ℝ v₁ z‖ ^ 2 + ‖fderiv ℝ v₂ z‖ ^ 2))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    δ * (∫ z, W z ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
      ∫ z, W z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ := by
  have hi {f : ℂ → ℝ} (hf : Continuous f) : Integrable (fun z ↦ f z * ‖η z‖ ^ 2) μ :=
    (hf.mul (hη.continuous.norm.pow 2)).integrable_of_hasCompactSupport
      (hηc.mono fun z hz hzero ↦ hz (by simp [hzero]))
  have hdc {v : ℂ → ℝ} (hv : ContDiff ℝ 2 v) : Continuous fun z ↦ ‖fderiv ℝ v z‖ ^ 2 :=
    ((hv.continuous_fderiv (by simp)).norm).pow 2
  have hn (v : ℂ → ℝ) (z : ℂ) : ‖v z • η z‖ ^ 2 = v z ^ 2 * ‖η z‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hcs (v : ℂ → ℝ) : HasCompactSupport fun t ↦ v t • η t :=
    hηc.mono fun z hz hzero ↦ hz (by simp [hzero])
  have h₁ := hgap (fun t ↦ v₁ t • η t) (hv₁.smul hη) (hcs v₁)
  rw [integral_norm_sq_gaugeFixedAdjoint_fun_smul hx hη hηc (hv₁.of_le (by norm_num))] at h₁
  have h₂ := mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) (a := a)
    (η := fun t ↦ v₂ t • η t) hx (hv₂.smul hη) (hcs v₂) (fun z _ ↦ hsol z) ha
    fun z hz ↦ hP z fun h ↦ hz (by simp [h])
  rw [integral_norm_sq_gaugeFixedAdjoint_fun_smul hx hη hηc (hv₂.of_le (by norm_num))] at h₂
  simp_rw [hn] at h₁ h₂
  rw [integral_sq_mul_inner_gaugeFixedOperator_eq_add hx hη hηc hv₁.continuous
    hv₂.continuous hsq]
  have i₀ := (hi (f := fun z ↦ W z ^ 2) (hW.pow 2)).const_mul δ
  have i₁ := (hi (f := fun z ↦ v₁ z ^ 2) (hv₁.continuous.pow 2)).const_mul c₀
  have i₂ := (hi (f := fun z ↦ v₂ z ^ 2) (hv₂.continuous.pow 2)).const_mul a
  have i₃ := hi (hdc hv₁)
  have i₄ := hi (hdc hv₂)
  have hmono := integral_mono i₀ ((i₁.add i₂).sub (i₃.add i₄))
    fun z ↦ by
      have := mul_le_mul_of_nonneg_right (hkey z) (sq_nonneg ‖η z‖)
      simp only [Pi.add_apply, Pi.sub_apply]
      convert this using 1 <;> ring
  rw [integral_const_mul, integral_sub' (i₁.add i₂) (i₃.add i₄), integral_add' i₁ i₂,
    integral_add' i₃ i₄, integral_const_mul, integral_const_mul] at hmono
  linarith

/-- **Weighted coercivity of `L_x L_x*` with a flattened weight.** At a vortex with
unit-modulus end and `|c| < 1/2`, there are `b ≥ 1` and `δ > 0` such that
`δ ∫ V² |η|² ≤ ∫ V² ⟪L_x L_x* η, η⟫` for every test field `η` and every nonnegative `C²` weight
`V` whose logarithmic gradient is at most that of `exp(c √(b + |z|²))`, namely
`|c| |z| / √(b + |z|²)`. That weight itself is allowed, and so are bounded weights such as
`W / (1 + ε W)` for `W = exp(c √(b + |z|²))` and `ε > 0`.

The weight is nearly flat on a large disc. There the spectral gap of `L_x L_x*` absorbs its
gradient, while outside the disc the exterior mass `a > c²` does. The two regions are joined
by the localization identity for the pair of weights `V cos θ`, `V sin θ`, with `θ` rising
slowly from `0` to `π / 2` across an annulus. -/
theorem exists_pos_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ b ≥ 1, ∃ δ > 0, ∀ V : ℂ → ℝ, ContDiff ℝ 2 V → (∀ z, 0 ≤ V z) →
      (∀ z, ‖fderiv ℝ V z‖ ≤ |c| * (‖z‖ / √(b + ‖z‖ ^ 2)) * V z) →
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      δ * (∫ z, V z ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
        ∫ z, V z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ := by
  have hc2 : c ^ 2 < 1 / 4 := by
    have := abs_nonneg c
    nlinarith [sq_abs c]
  set a : ℝ := (c ^ 2 + 1 / 4) / 2 with ha_def
  have ha : a < 1 / 4 := by linarith
  have hca : c ^ 2 < a := by linarith
  obtain ⟨c₀, hc₀, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) hx hsol hlim
  obtain ⟨R, hR₀, hR⟩ := exists_exterior_lt_mass hlim ha
  set m : ℝ := min c₀ a
  have hm : 0 < m := lt_min hc₀ (lt_of_le_of_lt (sq_nonneg c) hca)
  obtain ⟨R₂, _, θ, hθ, hθR, hθout, hθd⟩ := exists_contDiff_angle_cutoff (E := ℂ) hR₀.le
    (by positivity : 0 < √m / 4)
  set b : ℝ := 16 * c ^ 2 * R₂ ^ 2 / m + 1 with hb_def
  have hb : 1 ≤ b := by
    have : 0 ≤ 16 * c ^ 2 * R₂ ^ 2 / m := by positivity
    linarith
  set δ : ℝ := min (m / 2) (a - c ^ 2)
  have hδ : 0 < δ := lt_min (by positivity) (by linarith)
  refine ⟨b, hb, δ, hδ, fun V hV hV₀ hdV η hη hηc ↦ ?_⟩
  -- The logarithmic gradient of `V` is at most `|c|`, and at most `√m / 4` on the disc.
  have hWd (z : ℂ) : ‖fderiv ℝ V z‖ ^ 2 ≤ c ^ 2 * V z ^ 2 :=
    norm_fderiv_sq_le_of_norm_fderiv_le c (by linarith) (hV₀ z) (hdV z)
  have hWd₂ (z : ℂ) (hz : ‖z‖ ≤ R₂) : ‖fderiv ℝ V z‖ ^ 2 ≤ m / 16 * V z ^ 2 := by
    have hp : 0 < b + ‖z‖ ^ 2 := by positivity
    have hz2 : ‖z‖ ^ 2 ≤ R₂ ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
    have hmb : m / 16 * b = c ^ 2 * R₂ ^ 2 + m / 16 := by
      rw [hb_def]
      field_simp
    have : c ^ 2 * R₂ ^ 2 ≤ m / 16 * b := by
      rw [hmb]
      linarith
    have hfr : c ^ 2 * ‖z‖ ^ 2 ≤ m / 16 * (b + ‖z‖ ^ 2) := by
      nlinarith [sq_nonneg c, sq_nonneg ‖z‖, mul_le_mul_of_nonneg_left hz2 (sq_nonneg c)]
    have hq : (|c| * (‖z‖ / √(b + ‖z‖ ^ 2)) * V z) ^ 2 =
        c ^ 2 * ‖z‖ ^ 2 / (b + ‖z‖ ^ 2) * V z ^ 2 := by
      rw [mul_pow, mul_pow, div_pow, sq_abs, Real.sq_sqrt hp.le]
      ring
    refine (pow_le_pow_left₀ (norm_nonneg _) (hdV z) 2).trans ?_
    rw [hq]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hp).2 hfr) (sq_nonneg _)
  set v₁ : ℂ → ℝ := fun z ↦ V z * Real.cos (θ z)
  set v₂ : ℂ → ℝ := fun z ↦ V z * Real.sin (θ z)
  have hv₁ : ContDiff ℝ 2 v₁ := hV.mul (Real.contDiff_cos.comp (hθ.of_le (by simp)))
  have hv₂ : ContDiff ℝ 2 v₂ := hV.mul (Real.contDiff_sin.comp (hθ.of_le (by simp)))
  have hsq (z : ℂ) : V z ^ 2 = v₁ z ^ 2 + v₂ z ^ 2 := by
    simp only [v₁, v₂, mul_pow]
    rw [← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  have hθdiff (z : ℂ) : HasFDerivAt θ (fderiv ℝ θ z) z :=
    ((hθ.differentiable (by simp)) z).hasFDerivAt
  have hWdiff (z : ℂ) : HasFDerivAt V (fderiv ℝ V z) z :=
    ((hV.differentiable (by simp)) z).hasFDerivAt
  have hv₁d (z : ℂ) :
      ‖fderiv ℝ v₁ z‖ ≤ V z * ‖fderiv ℝ θ z‖ + |Real.cos (θ z)| * ‖fderiv ℝ V z‖ := by
    have hd : HasFDerivAt v₁
        (V z • (-Real.sin (θ z) • fderiv ℝ θ z) + Real.cos (θ z) • fderiv ℝ V z) z :=
      (hWdiff z).mul (hθdiff z).cos
    rw [hd.fderiv]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (hV₀ z)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)) (hV₀ z)
    · rw [norm_smul, Real.norm_eq_abs]
  have hv₂d (z : ℂ) :
      ‖fderiv ℝ v₂ z‖ ≤ V z * ‖fderiv ℝ θ z‖ + |Real.sin (θ z)| * ‖fderiv ℝ V z‖ := by
    have hd : HasFDerivAt v₂
        (V z • (Real.cos (θ z) • fderiv ℝ θ z) + Real.sin (θ z) • fderiv ℝ V z) z :=
      (hWdiff z).mul (hθdiff z).sin
    rw [hd.fderiv]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hV₀ z)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)) (hV₀ z)
    · rw [norm_smul, Real.norm_eq_abs]
  -- The pointwise margin.
  have hkey (z : ℂ) : δ * V z ^ 2 ≤
      c₀ * v₁ z ^ 2 + a * v₂ z ^ 2 - (‖fderiv ℝ v₁ z‖ ^ 2 + ‖fderiv ℝ v₂ z‖ ^ 2) := by
    by_cases hz : ‖z‖ ≤ R₂
    · have he2 : ‖fderiv ℝ θ z‖ ^ 2 ≤ m / 16 := by
        have := pow_le_pow_left₀ (norm_nonneg _) (hθd z) 2
        rw [div_pow, Real.sq_sqrt hm.le] at this
        linarith
      have := half_mul_le_of_norm_le (min_le_left c₀ a) (min_le_right c₀ a)
        (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hWd₂ z hz) he2
        (hv₁d z) (hv₂d z)
      exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans this
    · push Not at hz
      have hθz : θ z = π / 2 := (hθout z hz).self_of_nhds
      have h₀ : fderiv ℝ θ z = 0 := by rw [(hθout z hz).fderiv_eq, fderiv_const_apply]
      have h₁ : ‖fderiv ℝ v₁ z‖ = 0 := by
        have := hv₁d z
        rw [h₀, hθz, Real.cos_pi_div_two] at this
        simp only [norm_zero, mul_zero, abs_zero, zero_mul, add_zero] at this
        exact le_antisymm this (norm_nonneg _)
      have h₂ : ‖fderiv ℝ v₂ z‖ ≤ ‖fderiv ℝ V z‖ := by
        have := hv₂d z
        rwa [h₀, hθz, Real.sin_pi_div_two, norm_zero, mul_zero, abs_one, one_mul,
          zero_add] at this
      have hv₁z : v₁ z = 0 := by simp [v₁, hθz]
      have hv₂z : v₂ z = V z := by simp [v₂, hθz]
      have hδa : δ * V z ^ 2 ≤ (a - c ^ 2) * V z ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
      have := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
      rw [h₁, hv₁z, hv₂z]
      linarith [hWd z, show (a - c ^ 2) * V z ^ 2 = a * V z ^ 2 - c ^ 2 * V z ^ 2 by ring]
  refine mul_integral_sq_mul_norm_sq_le_of_forall_le hx hsol hgap ha.le hv₁ hv₂ hV.continuous
    hsq (fun z hz ↦ ?_) hkey hη hηc
  have hθz : θ z ≠ 0 := fun h ↦ hz (by simp [v₂, h])
  exact (hR z (lt_of_not_ge fun h ↦ hθz (hθR z h))).le

/-- **The exponentially weighted estimate for `L_x L_x*` at a plane vortex.** For an actual
vortex with unit-modulus end and `|c| < 1/2`, there is `K` such that every compactly supported
`C²` field `η` satisfies

`∫ exp(2c √(1 + |z|²)) |η|² ≤ K ∫ exp(2c √(1 + |z|²)) |L_x L_x* η|²`.

The constant depends only on the vortex and `c`. Unlike the exterior estimate
`exists_exterior_integral_exp_mul_norm_sq_le_integral_exp_mul_inner_gaugeFixedOperator`, the
field is not required to vanish on a large disc: there the spectral gap of `L_x L_x*` replaces
the exterior mass. -/
theorem exists_integral_exp_mul_norm_sq_le_mul_integral_exp_mul_norm_sq_gaugeFixedOperator
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K > 0, ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, Real.exp (c * √(1 + ‖z‖ ^ 2)) ^ 2 * ‖η z‖ ^ 2 ∂μ ≤
        K * ∫ z, Real.exp (c * √(1 + ‖z‖ ^ 2)) ^ 2 *
          ‖gaugeFixedOperator x (gaugeFixedAdjoint x η) z‖ ^ 2 ∂μ := by
  obtain ⟨b, hb, δ, hδ, hW⟩ :=
    exists_pos_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator (μ := μ)
      hx hsol hlim hc
  set E : ℝ := Real.exp (|c| * √|b - 1|) ^ 2
  have : 0 < E := by positivity
  refine ⟨E * E / δ ^ 2, by positivity, fun η hη hηc ↦ ?_⟩
  set w : ℂ → ℝ := fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2))
  set W : ℂ → ℝ := fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2))
  set G : ℂ → EuclideanSpace ℝ (Fin 4) := gaugeFixedOperator x (gaugeFixedAdjoint x η)
  have hGc : Continuous G :=
    continuous_gaugeFixedOperator hx.continuous (contDiff_gaugeFixedAdjoint hx hη)
  have hGs : HasCompactSupport G :=
    hasCompactSupport_gaugeFixedOperator (hasCompactSupport_gaugeFixedAdjoint hηc)
  have hw : Continuous w := (contDiff_exp_mul_sqrt_add_norm_sq (n := 0) c one_pos).continuous
  have hW₂ : ContDiff ℝ 2 W := contDiff_exp_mul_sqrt_add_norm_sq c (by linarith)
  have hWc : Continuous W := hW₂.continuous
  have hi {f : ℂ → ℝ} {g : ℂ → EuclideanSpace ℝ (Fin 4)} (hf : Continuous f)
      (hg : Continuous g) (hgs : HasCompactSupport g) :
      Integrable (fun z ↦ f z ^ 2 * ‖g z‖ ^ 2) μ :=
    ((hf.pow 2).mul (hg.norm.pow 2)).integrable_of_hasCompactSupport
      (hgs.mono fun z hz hzero ↦ hz (by simp [hzero]))
  have hamgm := integral_mul_inner_le (ν := μ) (w := fun z ↦ W z ^ 2) (fun z ↦ sq_nonneg _)
    (hi hWc hη.continuous hηc) (hi hWc hGc hGs) hδ
  have hWη := hW W hW₂ (fun z ↦ (Real.exp_pos _).le)
    (fun z ↦ (norm_fderiv_exp_mul_sqrt_add_norm_sq c (by linarith) z).trans_le (by
      rw [mul_right_comm])) η hη hηc
  have hflat : ∫ z, W z ^ 2 * ‖η z‖ ^ 2 ∂μ ≤ 1 / δ ^ 2 * ∫ z, W z ^ 2 * ‖G z‖ ^ 2 ∂μ := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    have : δ / 2 * ∫ z, W z ^ 2 * ‖η z‖ ^ 2 ∂μ ≤
        1 / (2 * δ) * ∫ z, W z ^ 2 * ‖G z‖ ^ 2 ∂μ := by linarith
    have h2 := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * δ)
    convert h2 using 1 <;> field_simp
  -- The two weights are comparable, since `√·` is `1/2`-Hölder.
  have h₁ := integral_mono (hi hw hη.continuous hηc) ((hi hWc hη.continuous hηc).const_mul E)
    fun z ↦ by
      simpa only [mul_assoc, abs_sub_comm 1 b] using mul_le_mul_of_nonneg_right
        (sq_exp_mul_sqrt_add_norm_sq_le c 1 b z) (sq_nonneg ‖η z‖)
  have h₂ := integral_mono (hi hWc hGc hGs) ((hi hw hGc hGs).const_mul E) fun z ↦ by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (sq_exp_mul_sqrt_add_norm_sq_le c b 1 z) (sq_nonneg ‖G z‖)
  rw [integral_const_mul] at h₁ h₂
  calc ∫ z, w z ^ 2 * ‖η z‖ ^ 2 ∂μ ≤ E * ∫ z, W z ^ 2 * ‖η z‖ ^ 2 ∂μ := h₁
    _ ≤ E * (1 / δ ^ 2 * (E * ∫ z, w z ^ 2 * ‖G z‖ ^ 2 ∂μ)) := by
      gcongr
      exact hflat.trans (by gcongr)
    _ = E * E / δ ^ 2 * ∫ z, w z ^ 2 * ‖G z‖ ^ 2 ∂μ := by ring

/-- **The exponentially weighted estimate for `L_x*` at a plane vortex.** For an actual vortex
with unit-modulus end and `|c| < 1/2`, there is `K` such that every compactly supported `C²`
field `η` satisfies

`∫ exp(2c √(1 + |z|²)) |L_x* η|² ≤ K ∫ exp(2c √(1 + |z|²)) |L_x L_x* η|²`.

With `f = L_x L_x* η`, the field `L_x* η = L_x* (L_x L_x*)⁻¹ f` is the value of the right
inverse of `L_x` at `f`. So this is the exponentially weighted `L²` estimate for the right
inverse, on inputs of this form. -/
theorem exists_integral_exp_mul_norm_sq_gaugeFixedAdjoint_le_mul_integral_exp_mul_norm_sq
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K > 0, ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, Real.exp (c * √(1 + ‖z‖ ^ 2)) ^ 2 * ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ ≤
        K * ∫ z, Real.exp (c * √(1 + ‖z‖ ^ 2)) ^ 2 *
          ‖gaugeFixedOperator x (gaugeFixedAdjoint x η) z‖ ^ 2 ∂μ := by
  obtain ⟨K₁, hK₁, hK⟩ :=
    exists_integral_exp_mul_norm_sq_le_mul_integral_exp_mul_norm_sq_gaugeFixedOperator
      (μ := μ) hx hsol hlim hc
  refine ⟨(1 + 4 * c ^ 2) * K₁ + 1, by positivity, fun η hη hηc ↦ ?_⟩
  set w : ℂ → ℝ := fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2))
  set G : ℂ → EuclideanSpace ℝ (Fin 4) := gaugeFixedOperator x (gaugeFixedAdjoint x η)
  have hw : ContDiff ℝ 2 w := contDiff_exp_mul_sqrt_add_norm_sq c one_pos
  have hGc : Continuous G :=
    continuous_gaugeFixedOperator hx.continuous (contDiff_gaugeFixedAdjoint hx hη)
  have hGs : HasCompactSupport G :=
    hasCompactSupport_gaugeFixedOperator (hasCompactSupport_gaugeFixedAdjoint hηc)
  have hdw (z : ℂ) : ‖fderiv ℝ w z‖ ^ 2 ≤ c ^ 2 * w z ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _)
      (norm_fderiv_exp_mul_sqrt_add_norm_sq_le c one_pos z) 2
    simpa only [mul_pow, sq_abs] using this
  have hi {f : ℂ → ℝ} {g : ℂ → EuclideanSpace ℝ (Fin 4)} (hf : Continuous f)
      (hg : Continuous g) (hgs : HasCompactSupport g) :
      Integrable (fun z ↦ f z ^ 2 * ‖g z‖ ^ 2) μ :=
    ((hf.pow 2).mul (hg.norm.pow 2)).integrable_of_hasCompactSupport
      (hgs.mono fun z hz hzero ↦ hz (by simp [hzero]))
  have hA := integral_sq_mul_norm_sq_gaugeFixedAdjoint_le (μ := μ) hx hη hηc
    (hw.of_le (by norm_num)) hdw
  have hP := integral_mul_inner_le (ν := μ) (w := fun z ↦ w z ^ 2) (fun z ↦ sq_nonneg _)
    (hi hw.continuous hη.continuous hηc) (hi hw.continuous hGc hGs) one_pos
  have h1 := hK η hη hηc
  have : 0 ≤ ∫ z, w z ^ 2 * ‖G z‖ ^ 2 ∂μ := integral_nonneg fun z ↦ by positivity
  have : 0 ≤ c ^ 2 := sq_nonneg c
  have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 + 4 * c ^ 2)
  nlinarith

end TauCeti.Vortex
