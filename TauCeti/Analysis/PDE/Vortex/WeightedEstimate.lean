/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.SpectralGap
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Exp
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.SoftMin
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.MeanInequalities

/-!
# Weighted energy estimates for the plane-vortex adjoint

Multiplication by a real weight gives an exact localization identity for the gauge-fixed
vortex adjoint. Its error is the squared gradient of the weight, with coefficient one.
Combining this identity with exterior coercivity gives the weighted energy estimate for
`L_x L_x*`, with margin `a - c²` when the squared exterior mass is `a` and the logarithmic
weight has gradient bounded by `c`. In particular, exponential weights with rate below
`1/2` are allowed sufficiently far out on a vortex with unit-modulus end.

The next part of the file removes the exterior restriction. With `ρ = √(1 + |z|²)` and
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
(`exists_pos_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator`). Its
constants depend on the vortex only through the spectral gap of `L_x L_x*` and a radius beyond
which the squared mass exceeds a fixed `a > c²`
(`exists_pos_forall_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator`), so
it is uniform over any family of vortices sharing these two inputs. With
the weighted adjoint energy bound `integral_sq_mul_norm_sq_gaugeFixedAdjoint_le`, this is what
`TauCeti.Analysis.PDE.Vortex.RightInverse` uses to extend the weighted estimate from test fields to
the weak right inverse on all of `L²`.

The constants of these `exp(c ρ)` estimates depend on the vortex `x`. Because the weight is
centred at the origin, the uniform versions in `TauCeti.Analysis.PDE.Vortex.RightInverse` and
`TauCeti.Analysis.PDE.Vortex.WindowEstimate` hold only over compact windows of divisors: a zero far
from the origin sits where that weight is large. The next part of the file centres the weight on
the zeros instead. With `d_D(z)` the distance from `z` to the zeros
of a vortex with divisor `D` of degree `m` and `|c| < 1/2`,

`‖exp(c d_D) η‖₂ + ‖exp(c d_D) L_x* η‖₂ ≤ K ‖exp(c d_D) L_x L_x* η‖₂`

with `K` depending only on `m` and `c`, uniformly over the whole noncompact moduli space,
including clusters of zeros that collide, separate or move off to infinity
(`exists_integral_exp_mul_infDist_sq_mul_norm_sq_le_mul_integral_gaugeFixedOperator`,
`exists_integral_exp_mul_infDist_sq_mul_norm_sq_gaugeFixedAdjoint_le_mul_integral`). The same
localization applies, now with three inputs uniform over the moduli space: the spectral gap of
`L_x L_x*` (`exists_pos_forall_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint`), the
mass near one at a fixed distance from every zero (`one_sub_lt_normSq_of_forall_le_norm_sub`),
and a smooth substitute `Φ` for `d_D`, the soft minimum of the regularized distances
`√(b + |z - a|²)` to the zeros (`TauCeti.softMinDist`). For `b` large, `Φ` is nearly flat where it
is small, which covers a neighbourhood of every zero of fixed size, and the localization angle is
taken to be a function of `Φ`.

The last part of the file gains one derivative. A weighted form of the Gårding inequality,
`∫ G(w y) ≤ 2 ∫ w² |L_x y|² + (2 c² + K) ∫ w² |y|²` for weights with `|dw| ≤ |c| w`, where `G` is
the covariant gradient density, follows from the Leibniz rule for `L_x` and the Gårding
inequality at the vortex. Applied to `y = L_x* η` with the weight `exp(c ρ)`, together with the
weighted `L²` estimate above, it bounds `exp(c ρ) L_x* η` in the covariant `H¹` norm, and in the
ordinary `H¹` norm when the connection coefficients of the vortex are bounded, by
`‖exp(c ρ) L_x L_x* η‖₂`.

All estimates here concern compactly supported classical test fields. They are not a
construction of a completed inverse.

## Main results

All in the namespace `TauCeti.Vortex`:

* `integral_norm_sq_gaugeFixedAdjoint_fun_smul`: the localization identity.
* `integral_sq_mul_norm_sq_gaugeFixedAdjoint_le`: the weighted energy of `L_x* η` is controlled
  by the weighted pairing with `L_x L_x*`.
* `exists_exterior_integral_exp_mul_norm_sq_le_integral_exp_mul_inner_gaugeFixedOperator`:
  the exterior weighted estimate.
* `exists_pos_forall_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator`:
  the weighted coercivity of `L_x L_x*` for weights flat on a large disc, with constants depending
  only on a spectral gap and an exterior mass.
* `exists_pos_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator`: the
  weighted coercivity of `L_x L_x*` at a vortex with unit-modulus end.
* `exists_integral_exp_mul_norm_sq_le_mul_integral_exp_mul_norm_sq_gaugeFixedOperator` and
  `exists_integral_exp_mul_norm_sq_gaugeFixedAdjoint_le_mul_integral_exp_mul_norm_sq`:
  the global weighted estimates for `η` and `L_x* η` in terms of `L_x L_x* η`.
* `exists_pos_forall_mul_integral_exp_mul_softMinDist_sq_mul_norm_sq_le_gaugeFixedOperator`:
  weighted coercivity `δ ∫ V² |η|² ≤ ∫ V² ⟪L_x L_x* η, η⟫` for the smooth weight `V = exp(c Φ)`
  centred on the zeros, with `b`, `δ` depending only on the degree `m` and `c`.
* `exists_integral_exp_mul_infDist_sq_mul_norm_sq_le_mul_integral_gaugeFixedOperator` and
  `exists_integral_exp_mul_infDist_sq_mul_norm_sq_gaugeFixedAdjoint_le_mul_integral`: the same
  estimates with weights `exp(c d_D)` centred on the zeros, with constants depending only on `m`
  and `c`, uniformly over the moduli space.
* `exists_integral_gaugeFixedGradientDensity_fun_smul_le`: the weighted Gårding inequality.
* `exists_integral_gaugeFixedGradientDensity_exp_smul_gaugeFixedAdjoint_le` and
  `exists_integral_norm_fderiv_sq_exp_smul_gaugeFixedAdjoint_le`: the weighted covariant and
  ordinary gradient estimates for `exp(c ρ) L_x* η` in terms of `L_x L_x* η`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Chapter III.
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/
public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter
open scoped ContDiff Laplacian Topology RealInnerProductSpace Real

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
  have he := (hw.continuous_fderiv one_ne_zero).norm.integrable_sq_mul_norm_sq_of_hasCompactSupport
    (μ := μ) hη.continuous hc
  simp_rw [norm_sq_gaugeFixedAdjoint_fun_smul x (hw.differentiable (by norm_num) _)
    (hη.differentiable (by norm_num) _)]
  rw [integral_add hi he]
  congr 1
  have hg := integral_inner_gaugeFixedOperator (μ := μ) (x := x) hA ((hw.pow 2).smul hη₁) (.inl hAc)
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
  have hi := hw.continuous.integrable_sq_mul_norm_sq_of_hasCompactSupport (μ := μ)
    hη.continuous hc
  have he := Continuous.integrable_sq_mul_norm_sq_of_hasCompactSupport (μ := μ)
    (hw.continuous_fderiv (by norm_num)).norm hη.continuous hc
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

/-- A gradient bound `t ≤ √m / 4` squares to `t² ≤ m / 16`. -/
private theorem sq_le_div_sixteen_of_le_sqrt_div_four {t m : ℝ} (ht : 0 ≤ t) (hm : 0 ≤ m)
    (h : t ≤ √m / 4) : t ^ 2 ≤ m / 16 := by
  have := pow_le_pow_left₀ ht h 2
  rw [div_pow, Real.sq_sqrt hm] at this
  linarith

/-- The pointwise margin of the localization by the pair of weights `V cos θ`, `V sin θ`. Let
`m = min c₀ a`. If `V` has logarithmic gradient at most `|c|` everywhere and at most `√m / 4` on
a set `S`, and the angle `θ` has gradient at most `√m / 4` and equals `π / 2` near every point
outside `S`, then the pair keeps the margin `min (m / 2) (a - c²)`. -/
private theorem min_mul_sq_le_sub_norm_fderiv_sq {c₀ a c : ℝ} {S : Set ℂ} {V θ : ℂ → ℝ}
    (hV : Differentiable ℝ V) (hθ : Differentiable ℝ θ) (hV₀ : ∀ z, 0 ≤ V z)
    (hdV : ∀ z, ‖fderiv ℝ V z‖ ^ 2 ≤ c ^ 2 * V z ^ 2)
    (hdV₂ : ∀ z ∈ S, ‖fderiv ℝ V z‖ ^ 2 ≤ min c₀ a / 16 * V z ^ 2)
    (hθout : ∀ z ∉ S, θ =ᶠ[𝓝 z] fun _ ↦ π / 2)
    (hθd : ∀ z, ‖fderiv ℝ θ z‖ ≤ √(min c₀ a) / 4) (hm : 0 ≤ min c₀ a) (z : ℂ) :
    min (min c₀ a / 2) (a - c ^ 2) * V z ^ 2 ≤
      c₀ * (V z * Real.cos (θ z)) ^ 2 + a * (V z * Real.sin (θ z)) ^ 2 -
        (‖fderiv ℝ (fun t ↦ V t * Real.cos (θ t)) z‖ ^ 2 +
          ‖fderiv ℝ (fun t ↦ V t * Real.sin (θ t)) z‖ ^ 2) := by
  -- `‖d(V · g(θ))‖ ≤ V ‖dθ‖ + |g(θ)| ‖dV‖` for `g = cos` and `g = sin`.
  have hgd {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, |g' t| ≤ 1) :
      ‖fderiv ℝ (fun t ↦ V t * g (θ t)) z‖ ≤
        V z * ‖fderiv ℝ θ z‖ + |g (θ z)| * ‖fderiv ℝ V z‖ := by
    have hd : HasFDerivAt (fun t ↦ V t * g (θ t))
        (V z • (g' (θ z) • fderiv ℝ θ z) + g (θ z) • fderiv ℝ V z) z :=
      (hV z).hasFDerivAt.mul ((hg (θ z)).comp_hasFDerivAt z (hθ z).hasFDerivAt)
    rw [hd.fderiv]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hV₀ z)]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) (hg' _)) (hV₀ z)
    · rw [norm_smul, Real.norm_eq_abs]
  have hv₁d := hgd Real.hasDerivAt_cos
    fun t ↦ (abs_neg (Real.sin t)).trans_le (Real.abs_sin_le_one t)
  have hv₂d := hgd Real.hasDerivAt_sin Real.abs_cos_le_one
  by_cases hz : z ∈ S
  · -- On `S` both gradients are small, and half of `m` survives.
    have he2 : ‖fderiv ℝ θ z‖ ^ 2 ≤ min c₀ a / 16 :=
      sq_le_div_sixteen_of_le_sqrt_div_four (norm_nonneg _) hm (hθd z)
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
      (half_mul_le_of_norm_le (min_le_left c₀ a) (min_le_right c₀ a) (norm_nonneg _)
        (norm_nonneg _) (norm_nonneg _) (hdV₂ z hz) he2 hv₁d hv₂d)
  · -- Outside `S` only `V sin θ = V` remains, and the exterior mass `a > c²` absorbs it.
    have hθz : θ z = π / 2 := (hθout z hz).self_of_nhds
    have h₀ : fderiv ℝ θ z = 0 := by rw [(hθout z hz).fderiv_eq, fderiv_const_apply]
    have h₁ : fderiv ℝ (fun t ↦ V t * Real.cos (θ t)) z = 0 := by simpa [h₀, hθz] using hv₁d
    have h₂ : ‖fderiv ℝ (fun t ↦ V t * Real.sin (θ t)) z‖ ≤ ‖fderiv ℝ V z‖ := by
      simpa [h₀, hθz] using hv₂d
    have := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
    have hδa : min (min c₀ a / 2) (a - c ^ 2) * V z ^ 2 ≤ (a - c ^ 2) * V z ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
    simp only [hθz, h₁, Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, norm_zero]
    linarith [hdV z]

/-- **Weighted coercivity of `L_x L_x*` from a spectral gap and an exterior mass.** Let
`c₀ > 0`, `c² < a ≤ 1/4` and `R` be real numbers. There are `b ≥ 1` and `δ > 0`, depending only
on `c₀`, `a`, `c` and `R`, with the following property. Let `x` be a `C¹` vortex whose adjoint
has spectral gap `c₀`, `c₀ ∫ |η|² ≤ ∫ |L_x* η|²` on test fields, and whose squared mass
`|α|² / 4` is at least `a` outside the disc of radius `R`. Then
`δ ∫ V² |η|² ≤ ∫ V² ⟪L_x L_x* η, η⟫` for every test field `η` and every nonnegative `C²` weight
`V` whose logarithmic gradient is at most that of `exp(c √(b + |z|²))`, namely
`|c| |z| / √(b + |z|²)`. That weight itself is allowed, and so are bounded weights such as
`W / (1 + ε W)` for `W = exp(c √(b + |z|²))` and `ε > 0`.

Since `b` and `δ` do not depend on `x`, the estimate is uniform over every family of vortices
with a common spectral gap and a common radius beyond which the mass exceeds `a`.

The weight is nearly flat on a large disc. There the spectral gap of `L_x L_x*` absorbs its
gradient, while outside the disc the exterior mass `a > c²` does. The two regions are joined
by the localization identity for the pair of weights `V cos θ`, `V sin θ`, with `θ` rising
slowly from `0` to `π / 2` across an annulus. -/
theorem exists_pos_forall_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator
    {c₀ a c : ℝ} (hc₀ : 0 < c₀) (ha : a ≤ 1 / 4) (hca : c ^ 2 < a) (R : ℝ) :
    ∃ b ≥ 1, ∃ δ > 0, ∀ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 1 x →
      (∀ z, equation x z = 0) →
      (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
        c₀ * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ) →
      (∀ z, R < ‖z‖ → a ≤ x z 2 ^ 2 + x z 3 ^ 2) →
      ∀ V : ℂ → ℝ, ContDiff ℝ 2 V → (∀ z, 0 ≤ V z) →
      (∀ z, ‖fderiv ℝ V z‖ ≤ |c| * (‖z‖ / √(b + ‖z‖ ^ 2)) * V z) →
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      δ * (∫ z, V z ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
        ∫ z, V z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ := by
  have hm : 0 < min c₀ a := lt_min hc₀ (lt_of_le_of_lt (sq_nonneg c) hca)
  obtain ⟨R₂, -, θ, hθ, hθR, hθout, hθd⟩ := exists_contDiff_angle_cutoff (E := ℂ)
    (le_max_right R 0) (by positivity : 0 < √(min c₀ a) / 4)
  set b : ℝ := 16 * c ^ 2 * R₂ ^ 2 / min c₀ a + 1
  have hb₀ : 0 < b := by positivity
  have hb : c ^ 2 * R₂ ^ 2 ≤ min c₀ a / 16 * b := by
    have : min c₀ a / 16 * b = c ^ 2 * R₂ ^ 2 + min c₀ a / 16 := by
      simp only [b]
      field_simp
    linarith
  refine ⟨b, le_add_of_nonneg_left (by positivity), min (min c₀ a / 2) (a - c ^ 2),
    lt_min (by positivity) (by linarith), fun x hx hsol hgap hR V hV hV₀ hdV η hη hηc ↦ ?_⟩
  -- On the disc of radius `R₂` the logarithmic gradient of `V` is at most `√m / 4`.
  have hdV₂ (z : ℂ) (hz : ‖z‖ ≤ R₂) : ‖fderiv ℝ V z‖ ^ 2 ≤ min c₀ a / 16 * V z ^ 2 := by
    have hp : 0 < b + ‖z‖ ^ 2 := by positivity
    have hz2 : ‖z‖ ^ 2 ≤ R₂ ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
    have hfr : c ^ 2 * ‖z‖ ^ 2 ≤ min c₀ a / 16 * (b + ‖z‖ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hz2 (sq_nonneg c), sq_nonneg ‖z‖]
    have hq : (|c| * (‖z‖ / √(b + ‖z‖ ^ 2)) * V z) ^ 2 =
        c ^ 2 * ‖z‖ ^ 2 / (b + ‖z‖ ^ 2) * V z ^ 2 := by
      rw [mul_pow, mul_pow, div_pow, sq_abs, Real.sq_sqrt hp.le]
      ring
    refine (pow_le_pow_left₀ (norm_nonneg _) (hdV z) 2).trans ?_
    rw [hq]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hp).2 hfr) (sq_nonneg _)
  refine mul_integral_sq_mul_norm_sq_le_of_forall_le hx hsol hgap ha
    (v₁ := fun t ↦ V t * Real.cos (θ t)) (v₂ := fun t ↦ V t * Real.sin (θ t))
    (hV.mul (Real.contDiff_cos.comp (hθ.of_le (by simp))))
    (hV.mul (Real.contDiff_sin.comp (hθ.of_le (by simp)))) hV.continuous
    (fun z ↦ by simp only [mul_pow]; rw [← mul_add, Real.cos_sq_add_sin_sq, mul_one])
    (fun z hz ↦ ?_)
    (min_mul_sq_le_sub_norm_fderiv_sq (hV.differentiable (by simp)) (hθ.differentiable (by simp))
      hV₀ (fun z ↦ norm_fderiv_sq_le_of_norm_fderiv_le c hb₀.le (hV₀ z) (hdV z))
      (S := {z | ‖z‖ ≤ R₂}) hdV₂ (fun z hz ↦ hθout z (lt_of_not_ge hz)) hθd hm.le) hη hηc
  -- The weight `V sin θ` vanishes on the disc of radius `max R 0`.
  have hθz : θ z ≠ 0 := fun h ↦ hz (by simp [h])
  exact hR z ((le_max_left R 0).trans_lt (lt_of_not_ge fun h ↦ hθz (hθR z h)))

/-- **Weighted coercivity of `L_x L_x*` with a flattened weight.** At a vortex with
unit-modulus end and `|c| < 1/2`, there are `b ≥ 1` and `δ > 0` such that
`δ ∫ V² |η|² ≤ ∫ V² ⟪L_x L_x* η, η⟫` for every test field `η` and every nonnegative `C²` weight
`V` whose logarithmic gradient is at most that of `exp(c √(b + |z|²))`, namely
`|c| |z| / √(b + |z|²)`. This is
`exists_pos_forall_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator` with
the spectral gap of the vortex and an exterior mass `a` strictly between `c²` and `1 / 4`. -/
theorem exists_pos_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ b ≥ 1, ∃ δ > 0, ∀ V : ℂ → ℝ, ContDiff ℝ 2 V → (∀ z, 0 ≤ V z) →
      (∀ z, ‖fderiv ℝ V z‖ ≤ |c| * (‖z‖ / √(b + ‖z‖ ^ 2)) * V z) →
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      δ * (∫ z, V z ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
        ∫ z, V z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ := by
  have hc2 : c ^ 2 < 1 / 4 := by nlinarith [sq_abs c, abs_nonneg c]
  obtain ⟨c₀, hc₀, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) hx hsol hlim
  obtain ⟨R, -, hR⟩ := exists_exterior_lt_mass hlim (a := (c ^ 2 + 1 / 4) / 2) (by linarith)
  obtain ⟨b, hb, δ, hδ, h⟩ :=
    exists_pos_forall_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator
      (μ := μ) (a := (c ^ 2 + 1 / 4) / 2) (c := c) hc₀ (by linarith) (by linarith) R
  exact ⟨b, hb, δ, hδ, h x hx hsol hgap fun z hz ↦ (hR z hz).le⟩

/-- **The adjoint step of the weighted estimates.** For a `C¹` weight `W` with
`‖dW‖² ≤ c² W²`, `∫ W² |L_x* η|² ≤ ∫ W² |L_x L_x* η|² + (1 + 4 c²) ∫ W² |η|²`. -/
private theorem integral_sq_mul_norm_sq_gaugeFixedAdjoint_le_add (hx : ContDiff ℝ 1 x)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) {W : ℂ → ℝ} (hW : ContDiff ℝ 1 W) {c : ℝ}
    (hdW : ∀ z, ‖fderiv ℝ W z‖ ^ 2 ≤ c ^ 2 * W z ^ 2) :
    ∫ z, W z ^ 2 * ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ ≤
      ∫ z, W z ^ 2 * ‖gaugeFixedOperator x (gaugeFixedAdjoint x η) z‖ ^ 2 ∂μ +
        (1 + 4 * c ^ 2) * ∫ z, W z ^ 2 * ‖η z‖ ^ 2 ∂μ := by
  have hA := integral_sq_mul_norm_sq_gaugeFixedAdjoint_le (μ := μ) hx hη hηc hW hdW
  have hP := integral_mul_inner_le (ν := μ) (w := fun z ↦ W z ^ 2) (fun z ↦ sq_nonneg _)
    (hW.continuous.integrable_sq_mul_norm_sq_of_hasCompactSupport hη.continuous hηc)
    (hW.continuous.integrable_sq_mul_norm_sq_of_hasCompactSupport
      (continuous_gaugeFixedOperator hx.continuous (contDiff_gaugeFixedAdjoint hx hη))
      (hasCompactSupport_gaugeFixedOperator (hasCompactSupport_gaugeFixedAdjoint hηc))) one_pos
  norm_num at hP
  linarith

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
  refine ⟨E * E / δ ^ 2, by positivity, fun η hη hηc ↦ ?_⟩
  have hW₂ : ContDiff ℝ 2 fun z : ℂ ↦ Real.exp (c * √(b + ‖z‖ ^ 2)) :=
    contDiff_exp_mul_sqrt_add_norm_sq c (by linarith)
  -- The two weights are comparable, since `√·` is `1/2`-Hölder.
  have hGc := continuous_gaugeFixedOperator hx.continuous (contDiff_gaugeFixedAdjoint hx hη)
  have hGs := hasCompactSupport_gaugeFixedOperator (x := x)
    (hasCompactSupport_gaugeFixedAdjoint (x := x) hηc)
  refine integral_mul_norm_sq_le_of_mul_le_integral_mul_inner_of_le hδ (by positivity)
    (fun z ↦ sq_nonneg _) (fun z ↦ sq_nonneg _)
    (fun z ↦ by simpa only [abs_sub_comm 1 b] using sq_exp_mul_sqrt_add_norm_sq_le c 1 b z)
    (fun z ↦ sq_exp_mul_sqrt_add_norm_sq_le c b 1 z)
    (hW₂.continuous.integrable_sq_mul_norm_sq_of_hasCompactSupport hη.continuous hηc)
    (hW₂.continuous.integrable_sq_mul_norm_sq_of_hasCompactSupport hGc hGs)
    ((continuous_exp_mul_sqrt_add_norm_sq c).integrable_sq_mul_norm_sq_of_hasCompactSupport hGc
      hGs) ?_
  exact hW _ hW₂ (fun z ↦ (Real.exp_pos _).le)
    (fun z ↦ (norm_fderiv_exp_mul_sqrt_add_norm_sq c (by linarith) z).trans_le (by
      rw [mul_right_comm])) η hη hηc

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
  have hA := integral_sq_mul_norm_sq_gaugeFixedAdjoint_le_add (μ := μ) hx hη hηc
    (contDiff_exp_mul_sqrt_add_norm_sq c one_pos) fun z ↦
      norm_fderiv_sq_le_of_norm_fderiv_le c zero_le_one (Real.exp_pos _).le
        ((norm_fderiv_exp_mul_sqrt_add_norm_sq c one_pos z).trans (mul_right_comm _ _ _)).le
  have : 0 ≤ ∫ z, Real.exp (c * √(1 + ‖z‖ ^ 2)) ^ 2 *
      ‖gaugeFixedOperator x (gaugeFixedAdjoint x η) z‖ ^ 2 ∂μ :=
    integral_nonneg fun z ↦ by positivity
  have := mul_le_mul_of_nonneg_left (hK η hη hηc) (by positivity : (0 : ℝ) ≤ 1 + 4 * c ^ 2)
  nlinarith

/-! ### Weights centred on the zeros, uniformly over the moduli space -/

/-- A vortex with the degree-`m` end framing has at most `m` distinct zeros. -/
private theorem card_toFinset_le_of_tendsto {m : ℕ} {D : Multiset ℂ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z)) : D.toFinset.card ≤ m :=
  (Multiset.toFinset_card_le D).trans (hD.card_eq_of_tendsto_mul_inv_pow hframe).le

/-- At a vortex with the degree-`m` end framing and zero divisor `D`, let `16 m < C`, `a < 1 / 4`
and `ρ = √(m C / (1 - 4a))`. Wherever the soft distance to the zeros differs from `√b + ρ` by more
than `ρ + log m`, every zero is at distance at least `ρ` and the mass `|α|² / 4` is at least `a`. -/
private theorem le_mass_of_lt_abs_softMinDist_sub (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0) {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z)) {C a b : ℝ}
    (hC : 16 * (m : ℝ) < C) (ha : 0 < 1 - 4 * a) {z : ℂ}
    (hz : √(m * C / (1 - 4 * a)) + Real.log m <
      |softMinDist b D.toFinset z - (√b + √(m * C / (1 - 4 * a)))|) :
    a ≤ x z 2 ^ 2 + x z 3 ^ 2 := by
  have := one_sub_lt_normSq_of_forall_le_norm_sub hx hsol hframe hD hC ha (z := z) fun a' ha' ↦ by
    have hs : D.toFinset.Nonempty := ⟨a', Multiset.mem_toFinset.2 ha'⟩
    -- The soft distance is at least `√b - log m`, so it exceeds `√b + ρ`.
    have h₁ := sqrt_sub_log_card_le_softMinDist (b := b) (z := z) hs
    have hk : Real.log D.toFinset.card ≤ Real.log m := Real.log_le_log
      (by exact_mod_cast hs.card_pos) (by exact_mod_cast card_toFinset_le_of_tendsto hframe hD)
    refine le_norm_sub_of_sqrt_add_le_softMinDist (b := b) ?_ (Multiset.mem_toFinset.2 ha')
    rcases lt_abs.1 hz with h | h <;>
      linarith [Real.sqrt_nonneg (m * C / (1 - 4 * a)), Real.log_natCast_nonneg m]
  linarith

/-- **Weighted coercivity of `L_x L_x*` with weights centred on the zeros.** For every degree `m`
and `|c| < 1/2` there are `b > 0` and `δ > 0` such that every smooth vortex `x` with the
degree-`m` end framing and zero divisor `D` satisfies `δ ∫ V² |η|² ≤ ∫ V² ⟪L_x L_x* η, η⟫` for
every test field `η`, where `V = exp (c Φ)` and `Φ = softMinDist b D.toFinset` is the smooth
distance to the zeros. The constants do not depend on the vortex. -/
theorem exists_pos_forall_mul_integral_exp_mul_softMinDist_sq_mul_norm_sq_le_gaugeFixedOperator
    (m : ℕ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ b > 0, ∃ δ > 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ),
      ContDiff ℝ ∞ x → (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      δ * (∫ z, Real.exp (c * softMinDist b D.toFinset z) ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
        ∫ z, Real.exp (c * softMinDist b D.toFinset z) ^ 2 *
          ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ := by
  -- The weight is nearly flat near every zero, where the uniform spectral gap absorbs its
  -- gradient. Where the angle `θ₀ (Φ - s₀)` is nonzero, the exterior mass `a > c²` absorbs it.
  have hc2 : c ^ 2 < 1 / 4 := by nlinarith [sq_abs c, abs_nonneg c]
  set a : ℝ := (c ^ 2 + 1 / 4) / 2
  have hca : c ^ 2 < a := by simp only [a]; linarith
  obtain ⟨c₀, hc₀, hgap⟩ :=
    exists_pos_forall_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) m
  set mm : ℝ := min c₀ a
  have hm : 0 < mm := lt_min hc₀ (lt_of_le_of_lt (sq_nonneg c) hca)
  set ε : ℝ := √mm / 4
  have hε : 0 < ε := by positivity
  -- Points at distance at least `ρ` from every zero have mass more than `a`.
  set C : ℝ := 16 * m + 1
  set ρ : ℝ := √(m * C / (1 - 4 * a))
  have hlm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  set r₁ : ℝ := ρ + Real.log m
  obtain ⟨R₂, -, θ₀, hθ₀, hθ₀R, hθ₀out, hθ₀d⟩ :=
    exists_contDiff_angle_cutoff (E := ℝ) (by positivity : 0 ≤ r₁) hε
  obtain ⟨b, hb, hflat⟩ := exists_pos_forall_norm_fderiv_softMinDist_le (E := ℂ) m (r₁ + R₂) hε
  refine ⟨b, hb, min (mm / 2) (a - c ^ 2), lt_min (by positivity) (by linarith),
    fun x D hx hsol hframe hD η hη hηc ↦ ?_⟩
  set Φ : ℂ → ℝ := softMinDist b D.toFinset
  have hΦ : ContDiff ℝ ∞ Φ := contDiff_softMinDist hb _
  set s₀ : ℝ := √b + ρ
  set V : ℂ → ℝ := fun z ↦ Real.exp (c * Φ z)
  set θ : ℂ → ℝ := fun z ↦ θ₀ (Φ z - s₀)
  have hV : ContDiff ℝ 2 V := (contDiff_const.mul (hΦ.of_le (by simp))).exp
  have hθ : ContDiff ℝ 2 θ := (hθ₀.of_le (by simp)).comp ((hΦ.of_le (by simp)).sub contDiff_const)
  -- The angle has gradient at most `ε` and is `π / 2` near every point with `R₂ < Φ - s₀`.
  obtain ⟨hθd, hθout⟩ := norm_fderiv_comp_sub_le_and_eventuallyEq s₀ (hθ₀.differentiable (by simp))
    (hΦ.differentiable (by simp)) hθ₀out hθ₀d (norm_fderiv_softMinDist_le_one hb _)
  refine mul_integral_sq_mul_norm_sq_le_of_forall_le (hx.of_le (by simp)) hsol
    (hgap x D hx hsol hframe hD) (by simp only [a]; linarith) (v₁ := fun t ↦ V t * Real.cos (θ t))
    (v₂ := fun t ↦ V t * Real.sin (θ t)) (hV.mul (Real.contDiff_cos.comp hθ))
    (hV.mul (Real.contDiff_sin.comp hθ)) hV.continuous
    (fun z ↦ by simp only [mul_pow]; rw [← mul_add, Real.cos_sq_add_sin_sq, mul_one])
    (fun z hz ↦ le_mass_of_lt_abs_softMinDist_sub hx hsol hframe hD (C := C) (b := b)
      (by simp only [C]; linarith) (by simp only [a]; linarith)
      (lt_of_not_ge fun h ↦ hz (by simp [θ, hθ₀R (Φ z - s₀) h])))
    (min_mul_sq_le_sub_norm_fderiv_sq (S := {z | Φ z - s₀ ≤ R₂}) (hV.differentiable (by simp))
      (hθ.differentiable (by simp)) (fun z ↦ (Real.exp_pos _).le) (fun z ↦ ?_) (fun z hz ↦ ?_)
      (fun z hz ↦ hθout z (lt_of_not_ge hz)) hθd hm.le) hη hηc
  · exact norm_fderiv_exp_mul_softMinDist_sq_le hb _ c z
  · -- Where `θ` is not `π / 2`, `Φ ≤ √b + r₁ + R₂` and the gradient of `Φ` is at most `ε`.
    have hΦS : ‖fderiv ℝ Φ z‖ ≤ ε := hflat _ (card_toFinset_le_of_tendsto hframe hD) z (by
      simp only [Set.mem_ofPred_eq, s₀, r₁] at hz ⊢; linarith)
    rw [norm_fderiv_exp_mul_softMinDist hb, mul_pow, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right ((mul_le_of_le_one_left (sq_nonneg _) (by linarith)).trans
      (sq_le_div_sixteen_of_le_sqrt_div_four (norm_nonneg _) hm.le hΦS)) (sq_nonneg _)

/-- **The weighted estimate for `L_x L_x*` with weights centred on the zeros, uniformly over the
moduli space.** For every degree `m` and `|c| < 1/2` there is `K` such that every smooth plane
vortex `x` with the degree-`m` end framing and zero divisor `D`, and every compactly supported
`C²` field `η`, satisfy

`∫ exp(2c d_D(z)) |η|² ≤ K ∫ exp(2c d_D(z)) |L_x L_x* η|²`,

where `d_D(z)` is the distance from `z` to the zeros. The constant depends only on `m` and `c`.

Unlike the weight `exp(c √(1 + |z|²))` of
`exists_integral_exp_mul_norm_sq_le_mul_integral_exp_mul_norm_sq_gaugeFixedOperator`, whose
constant depends on `x`, and of its window-uniform version
`exists_forall_eLpNorm_exp_mul_smul_le_of_forall_mem_norm_le`, which is centred at the origin
and holds only over compact windows of divisors, this weight follows the zeros: it applies to
clusters of zeros that move apart or off to infinity, where the compact-window hypotheses fail. -/
theorem exists_integral_exp_mul_infDist_sq_mul_norm_sq_le_mul_integral_gaugeFixedOperator
    (m : ℕ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K > 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, Real.exp (c * Metric.infDist z (D.toFinset : Set ℂ)) ^ 2 * ‖η z‖ ^ 2 ∂μ ≤
        K * ∫ z, Real.exp (c * Metric.infDist z (D.toFinset : Set ℂ)) ^ 2 *
          ‖gaugeFixedOperator x (gaugeFixedAdjoint x η) z‖ ^ 2 ∂μ := by
  obtain ⟨b, hb, δ, hδ, hW⟩ :=
    exists_pos_forall_mul_integral_exp_mul_softMinDist_sq_mul_norm_sq_le_gaugeFixedOperator
      (μ := μ) m hc
  set E : ℝ := Real.exp (|c| * (√b + Real.log m)) ^ 2
  refine ⟨E * E / δ ^ 2, by positivity, fun x D hx hsol hframe hD η hη hηc ↦ ?_⟩
  have hx₁ : ContDiff ℝ 1 x := hx.of_le (by simp)
  -- The two weights are comparable, since the soft minimum is within `√b + log m` of the
  -- distance to the zeros.
  have hcmp := abs_softMinDist_sub_infDist_le hb.le (card_toFinset_le_of_tendsto hframe hD)
  have hw : Continuous fun z ↦ Real.exp (c * Metric.infDist z (D.toFinset : Set ℂ)) :=
    (continuous_const.mul (Metric.continuous_infDist_pt _)).rexp
  have hV : Continuous fun z ↦ Real.exp (c * softMinDist b D.toFinset z) :=
    (continuous_const.mul (contDiff_softMinDist (n := 0) hb D.toFinset).continuous).rexp
  have hGc := continuous_gaugeFixedOperator hx₁.continuous (contDiff_gaugeFixedAdjoint hx₁ hη)
  have hGs := hasCompactSupport_gaugeFixedOperator (x := x)
    (hasCompactSupport_gaugeFixedAdjoint (x := x) hηc)
  exact integral_mul_norm_sq_le_of_mul_le_integral_mul_inner_of_le hδ (by positivity)
    (fun z ↦ sq_nonneg _) (fun z ↦ sq_nonneg _)
    (fun z ↦ sq_exp_mul_le_of_abs_sub_le ((abs_sub_comm _ _).trans_le (hcmp z)))
    (fun z ↦ sq_exp_mul_le_of_abs_sub_le (hcmp z))
    (hV.integrable_sq_mul_norm_sq_of_hasCompactSupport hη.continuous hηc)
    (hV.integrable_sq_mul_norm_sq_of_hasCompactSupport hGc hGs)
    (hw.integrable_sq_mul_norm_sq_of_hasCompactSupport hGc hGs)
    (hW x D hx hsol hframe hD η hη hηc)

/-- **The weighted estimate for `L_x*` with weights centred on the zeros, uniformly over the
moduli space.** For every degree `m` and `|c| < 1/2` there is `K` such that every smooth plane
vortex `x` with the degree-`m` end framing and zero divisor `D`, and every compactly supported
`C²` field `η`, satisfy

`∫ exp(2c d_D(z)) |L_x* η|² ≤ K ∫ exp(2c d_D(z)) |L_x L_x* η|²`,

where `d_D(z)` is the distance from `z` to the zeros. With `f = L_x L_x* η`, the field `L_x* η` is
the value at `f` of the right inverse `L_x* (L_x L_x*)⁻¹` of `L_x`, so this is the weighted output
estimate for that inverse on such inputs, with weights that follow the zeros and a constant
depending only on `m` and `c`. -/
theorem exists_integral_exp_mul_infDist_sq_mul_norm_sq_gaugeFixedAdjoint_le_mul_integral
    (m : ℕ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K > 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) →
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, Real.exp (c * Metric.infDist z (D.toFinset : Set ℂ)) ^ 2 *
          ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ ≤
        K * ∫ z, Real.exp (c * Metric.infDist z (D.toFinset : Set ℂ)) ^ 2 *
          ‖gaugeFixedOperator x (gaugeFixedAdjoint x η) z‖ ^ 2 ∂μ := by
  obtain ⟨K₁, hK₁, hK⟩ :=
    exists_integral_exp_mul_infDist_sq_mul_norm_sq_le_mul_integral_gaugeFixedOperator
      (μ := μ) m hc
  -- The weight `exp (c d_D)` is only Lipschitz; the localization uses the smooth weight
  -- `exp (c Φ)` with the soft minimum `Φ` of the regularized distances, which is comparable.
  set E : ℝ := Real.exp (|c| * (1 + Real.log m)) ^ 2
  refine ⟨E * ((2 + 4 * c ^ 2) * E * K₁ + E), by positivity,
    fun x D hx hsol hframe hD η hη hηc ↦ ?_⟩
  set w : ℂ → ℝ := fun z ↦ Real.exp (c * Metric.infDist z (D.toFinset : Set ℂ))
  set W : ℂ → ℝ := fun z ↦ Real.exp (c * softMinDist 1 D.toFinset z)
  set G : ℂ → EuclideanSpace ℝ (Fin 4) := gaugeFixedOperator x (gaugeFixedAdjoint x η)
  have hx₁ : ContDiff ℝ 1 x := hx.of_le (by simp)
  have hW : ContDiff ℝ 1 W := (contDiff_const.mul (contDiff_softMinDist one_pos _)).exp
  have hw : Continuous w := (continuous_const.mul (Metric.continuous_infDist_pt _)).rexp
  -- `∫ W² |L_x* η|² ≤ ∫ W² |G|² + (1 + 4 c²) ∫ W² |η|²`.
  have hA := integral_sq_mul_norm_sq_gaugeFixedAdjoint_le_add (μ := μ) hx₁ hη hηc hW
    (norm_fderiv_exp_mul_softMinDist_sq_le one_pos _ c)
  -- The comparison of the weights.
  have hcmp := abs_softMinDist_sub_infDist_le zero_le_one (card_toFinset_le_of_tendsto hframe hD)
  rw [Real.sqrt_one] at hcmp
  have hle {F : ℂ → EuclideanSpace ℝ (Fin 4)} (hF : Continuous F) (hFs : HasCompactSupport F) :=
    integral_mul_norm_sq_le_mul_of_le (ν := μ) (w := fun z ↦ W z ^ 2) (fun z ↦ sq_nonneg _)
      (fun z ↦ sq_exp_mul_le_of_abs_sub_le (hcmp z))
      (hw.integrable_sq_mul_norm_sq_of_hasCompactSupport hF hFs)
  have h₁ := integral_mul_norm_sq_le_mul_of_le (ν := μ) (w := fun z ↦ w z ^ 2)
    (fun z ↦ sq_nonneg _)
    (fun z ↦ sq_exp_mul_le_of_abs_sub_le ((abs_sub_comm _ _).trans_le (hcmp z)))
    (hW.continuous.integrable_sq_mul_norm_sq_of_hasCompactSupport
      (contDiff_gaugeFixedAdjoint hx₁ hη).continuous (hasCompactSupport_gaugeFixedAdjoint hηc))
  have h₂ := hle hη.continuous hηc
  have h₃ := hle (continuous_gaugeFixedOperator hx₁.continuous (contDiff_gaugeFixedAdjoint hx₁ hη))
    (hasCompactSupport_gaugeFixedOperator (hasCompactSupport_gaugeFixedAdjoint hηc))
  have h₄ := hK x D hx hsol hframe hD η hη hηc
  set IG := ∫ z, w z ^ 2 * ‖G z‖ ^ 2 ∂μ
  have hIG : 0 ≤ IG := integral_nonneg fun z ↦ by positivity
  -- `∫ W² |L_x* η|² ≤ E IG + (1 + 4 c²) E K₁ IG`.
  have hWA : ∫ z, W z ^ 2 * ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ ≤
      ((2 + 4 * c ^ 2) * E * K₁ + E) * IG := by
    have hWη : ∫ z, W z ^ 2 * ‖η z‖ ^ 2 ∂μ ≤ E * (K₁ * IG) := h₂.trans (by gcongr)
    calc ∫ z, W z ^ 2 * ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ
        ≤ E * IG + (1 + 4 * c ^ 2) * (E * (K₁ * IG)) :=
          hA.trans (add_le_add h₃ (mul_le_mul_of_nonneg_left hWη (by positivity)))
      _ ≤ ((2 + 4 * c ^ 2) * E * K₁ + E) * IG := by nlinarith [mul_nonneg hK₁.le hIG]
  calc ∫ z, w z ^ 2 * ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ
      ≤ E * ∫ z, W z ^ 2 * ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ := h₁
    _ ≤ E * (((2 + 4 * c ^ 2) * E * K₁ + E) * IG) := by gcongr
    _ = E * ((2 + 4 * c ^ 2) * E * K₁ + E) * IG := by ring

/-! ### Weighted gradient estimates -/

/-- **The weighted Gårding inequality at a plane vortex.** Let `x` be a `C¹` solution of the
vortex equation with `|α| → 1` and `∇₁ α → 0` at infinity. There is a constant `K ≥ 0`,
depending only on the vortex, such that for every `C²` weight `w` with `|dw| ≤ |c| |w|` and every
compactly supported `C²` variation `y`,

`∫ G(w y) ≤ 2 ∫ w² |L_x y|² + (2 c² + K) ∫ w² |y|²`,

where `G(w y) = |∇b|² + |∇_a ψ|²` is the covariant gradient density of `w y`
(`gaugeFixedGradientDensity`). -/
theorem exists_integral_gaugeFixedGradientDensity_fun_smul_le
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0)) :
    ∃ K ≥ 0, ∀ (w : ℂ → ℝ) (c : ℝ), ContDiff ℝ 2 w →
      (∀ z, ‖fderiv ℝ w z‖ ^ 2 ≤ c ^ 2 * w z ^ 2) →
      ∀ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 y → HasCompactSupport y →
        ∫ z, gaugeFixedGradientDensity x (fun t ↦ w t • y t) z ∂μ ≤
          2 * ∫ z, w z ^ 2 * ‖gaugeFixedOperator x y z‖ ^ 2 ∂μ +
            (2 * c ^ 2 + K) * ∫ z, w z ^ 2 * ‖y z‖ ^ 2 ∂μ := by
  obtain ⟨R, -, K, hK⟩ := exists_integral_gaugeFixedGradientDensity_add_mul_integral_norm_sq_le
    (μ := μ) hx hsol hlim hcov (a := 0) (by norm_num)
  refine ⟨max K 0, le_max_right _ _, fun w c hw hdw y hy hyc ↦ ?_⟩
  set v : ℂ → EuclideanSpace ℝ (Fin 4) := fun t ↦ w t • y t
  have hv : ContDiff ℝ 2 v := hw.smul hy
  have hvc : HasCompactSupport v := hyc.smul_left (f := w)
  have hLy : Continuous (gaugeFixedOperator x y) :=
    continuous_gaugeFixedOperator hx.continuous (hy.of_le (by norm_num))
  have hLyc : HasCompactSupport (gaugeFixedOperator x y) := hasCompactSupport_gaugeFixedOperator hyc
  have hnv (z : ℂ) : ‖v z‖ ^ 2 = w z ^ 2 * ‖y z‖ ^ 2 := by
    simp [v, norm_smul, mul_pow]
  -- Pointwise, `|L_x (w y)|² ≤ 2 w² |L_x y|² + 2 c² w² |y|²` by the Leibniz rule.
  have hpt (z : ℂ) : ‖gaugeFixedOperator x v z‖ ^ 2 ≤
      2 * (w z ^ 2 * ‖gaugeFixedOperator x y z‖ ^ 2) + 2 * c ^ 2 * (w z ^ 2 * ‖y z‖ ^ 2) := by
    refine (norm_sq_gaugeFixedOperator_fun_smul_le x (hw.differentiable (by norm_num) z)
      (hy.differentiable (by norm_num) z)).trans ?_
    have := mul_le_mul_of_nonneg_right (hdw z) (sq_nonneg ‖y z‖)
    nlinarith
  have hwy := hw.continuous.integrable_sq_mul_norm_sq_of_hasCompactSupport (μ := μ)
    hy.continuous hyc
  have hwL := hw.continuous.integrable_sq_mul_norm_sq_of_hasCompactSupport (μ := μ) hLy hLyc
  have hL : ∫ z, ‖gaugeFixedOperator x v z‖ ^ 2 ∂μ ≤
      2 * ∫ z, w z ^ 2 * ‖gaugeFixedOperator x y z‖ ^ 2 ∂μ +
        2 * c ^ 2 * ∫ z, w z ^ 2 * ‖y z‖ ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hwL.const_mul _)
      (hwy.const_mul _)]
    refine integral_mono ?_ ((hwL.const_mul _).add (hwy.const_mul _)) hpt
    exact (continuous_gaugeFixedOperator hx.continuous
      (hv.of_le (by norm_num))).integrable_norm_sq_of_hasCompactSupport
        (hasCompactSupport_gaugeFixedOperator hvc)
  -- The mass of `w y` on the disc is at most its total mass.
  have hB : K * ∫ z in Metric.closedBall 0 R, ‖v z‖ ^ 2 ∂μ ≤
      max K 0 * ∫ z, w z ^ 2 * ‖y z‖ ^ 2 ∂μ := by
    have hv2 : Integrable (fun z ↦ ‖v z‖ ^ 2) μ := by simpa only [hnv] using hwy
    have h₀ : 0 ≤ ∫ z in Metric.closedBall 0 R, ‖v z‖ ^ 2 ∂μ :=
      setIntegral_nonneg Metric.isClosed_closedBall.measurableSet fun z _ ↦ sq_nonneg _
    have h₁ : ∫ z in Metric.closedBall 0 R, ‖v z‖ ^ 2 ∂μ ≤ ∫ z, w z ^ 2 * ‖y z‖ ^ 2 ∂μ := by
      simp_rw [← hnv]
      exact setIntegral_le_integral hv2 (ae_of_all _ fun z ↦ sq_nonneg _)
    calc K * ∫ z in Metric.closedBall 0 R, ‖v z‖ ^ 2 ∂μ
        ≤ max K 0 * ∫ z in Metric.closedBall 0 R, ‖v z‖ ^ 2 ∂μ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h₀
      _ ≤ max K 0 * ∫ z, w z ^ 2 * ‖y z‖ ^ 2 ∂μ :=
          mul_le_mul_of_nonneg_left h₁ (le_max_right _ _)
  have h := hK v hv hvc
  rw [zero_mul, add_zero] at h
  linarith

/-- **The exponentially weighted covariant `H¹` estimate for `L_x*` at a plane vortex.** Let `x`
be a `C²` solution of the vortex equation with `|α| → 1` at infinity, let `ρ(z) = √(1 + |z|²)`
and `|c| < 1/2`. There is `K`, depending only on the vortex and `c`, such
that every compactly supported `C³` field `η` satisfies

`∫ G(exp(c ρ) L_x* η) ≤ K ∫ exp(2 c ρ) |L_x L_x* η|²`,

where `G` is the covariant gradient density (`gaugeFixedGradientDensity`). With
`f = L_x L_x* η`, the field `L_x* η` is the value at `f` of the right inverse
`L_x* (L_x L_x*)⁻¹`. Together with
`exists_integral_exp_mul_norm_sq_gaugeFixedAdjoint_le_mul_integral_exp_mul_norm_sq` this bounds
`exp(c ρ) L_x* η` in the covariant `H¹` norm by `exp(c ρ) f` in `L²`, on inputs of this form. -/
theorem exists_integral_gaugeFixedGradientDensity_exp_smul_gaugeFixedAdjoint_le
    (hx : ContDiff ℝ 2 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K > 0, ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 3 η → HasCompactSupport η →
      ∫ z, gaugeFixedGradientDensity x
          (fun t ↦ Real.exp (c * √(1 + ‖t‖ ^ 2)) • gaugeFixedAdjoint x η t) z ∂μ ≤
        K * ∫ z, Real.exp (c * √(1 + ‖z‖ ^ 2)) ^ 2 *
          ‖gaugeFixedOperator x (gaugeFixedAdjoint x η) z‖ ^ 2 ∂μ := by
  have hx₁ : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  have hcov := tendsto_covariantDerivative_cocompact (contDiff_euclidean.1 hx 0).continuous
    (contDiff_euclidean.1 hx 2) (contDiff_euclidean.1 hx 3) hsol hlim 1
  obtain ⟨K₁, hK₁, hG⟩ :=
    exists_integral_gaugeFixedGradientDensity_fun_smul_le (μ := μ) hx₁ hsol hlim hcov
  obtain ⟨K₂, hK₂, hA⟩ :=
    exists_integral_exp_mul_norm_sq_gaugeFixedAdjoint_le_mul_integral_exp_mul_norm_sq (μ := μ)
      hx₁ hsol hlim hc
  refine ⟨2 + (2 * c ^ 2 + K₁) * K₂, by positivity, fun η hη hηc ↦ ?_⟩
  set w : ℂ → ℝ := fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2))
  have hw : ContDiff ℝ 2 w := contDiff_exp_mul_sqrt_add_norm_sq c one_pos
  have hdw (z : ℂ) : ‖fderiv ℝ w z‖ ^ 2 ≤ c ^ 2 * w z ^ 2 :=
    norm_fderiv_sq_le_of_norm_fderiv_le c zero_le_one (Real.exp_pos _).le
      ((norm_fderiv_exp_mul_sqrt_add_norm_sq c one_pos z).trans (mul_right_comm _ _ _)).le
  have hu : ContDiff ℝ 2 (gaugeFixedAdjoint x η) :=
    contDiff_gaugeFixedAdjoint hx (hη.of_le (by norm_num))
  have h₁ := hG w c hw hdw _ hu (hasCompactSupport_gaugeFixedAdjoint hηc)
  have h₂ := hA η (hη.of_le (by norm_num)) hηc
  have : 0 ≤ 2 * c ^ 2 + K₁ := by positivity
  have := mul_le_mul_of_nonneg_left h₂ this
  linarith

/-- **The exponentially weighted `H¹` estimate for `L_x*` at a plane vortex.** Under the
hypotheses of `exists_integral_gaugeFixedGradientDensity_exp_smul_gaugeFixedAdjoint_le`, if
moreover the connection coefficients of `x` are bounded, `A₁² + A₂² ≤ M` for
`a = i (A₁ ds + A₂ dt)`, then there is `K` such that every compactly supported `C³` field `η`
satisfies

`∫ |D(exp(c ρ) L_x* η)|² ≤ K ∫ exp(2 c ρ) |L_x L_x* η|²`.

With `exists_integral_exp_mul_norm_sq_gaugeFixedAdjoint_le_mul_integral_exp_mul_norm_sq`, this
bounds `‖exp(c ρ) L_x* η‖_{H¹}` by `‖exp(c ρ) L_x L_x* η‖₂`: the exponentially weighted output
estimate for the right inverse `L_x* (L_x L_x*)⁻¹`, from `L²` to `H¹`, on inputs of this form. -/
theorem exists_integral_norm_fderiv_sq_exp_smul_gaugeFixedAdjoint_le
    (hx : ContDiff ℝ 2 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {M : ℝ} (hM : ∀ z, x z 0 ^ 2 + x z 1 ^ 2 ≤ M) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K > 0, ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 3 η → HasCompactSupport η →
      ∫ z, ‖fderiv ℝ
          (fun t ↦ Real.exp (c * √(1 + ‖t‖ ^ 2)) • gaugeFixedAdjoint x η t) z‖ ^ 2 ∂μ ≤
        K * ∫ z, Real.exp (c * √(1 + ‖z‖ ^ 2)) ^ 2 *
          ‖gaugeFixedOperator x (gaugeFixedAdjoint x η) z‖ ^ 2 ∂μ := by
  have hx₁ : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  obtain ⟨K₁, hK₁, hG⟩ :=
    exists_integral_gaugeFixedGradientDensity_exp_smul_gaugeFixedAdjoint_le (μ := μ) hx hsol
      hlim hc
  obtain ⟨K₂, hK₂, hA⟩ :=
    exists_integral_exp_mul_norm_sq_gaugeFixedAdjoint_le_mul_integral_exp_mul_norm_sq (μ := μ)
      hx₁ hsol hlim hc
  have hM₀ : 0 ≤ M := (add_nonneg (sq_nonneg _) (sq_nonneg _)).trans (hM 0)
  refine ⟨4 * K₁ + 4 * M * K₂, by positivity, fun η hη hηc ↦ ?_⟩
  set w : ℂ → ℝ := fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2))
  set v : ℂ → EuclideanSpace ℝ (Fin 4) := fun t ↦ w t • gaugeFixedAdjoint x η t
  have hw : ContDiff ℝ 2 w := contDiff_exp_mul_sqrt_add_norm_sq c one_pos
  have hu : ContDiff ℝ 2 (gaugeFixedAdjoint x η) :=
    contDiff_gaugeFixedAdjoint hx (hη.of_le (by norm_num))
  have hv : ContDiff ℝ 2 v := hw.smul hu
  have hvc : HasCompactSupport v := (hasCompactSupport_gaugeFixedAdjoint hηc).smul_left (f := w)
  have h := integral_norm_fderiv_sq_le_gaugeFixedGradientDensity_add (μ := μ) (y := v)
    hx.continuous (hv.of_le (by norm_num)) hvc (M := M) fun z _ ↦ hM z
  have hnv : ∫ z, ‖v z‖ ^ 2 ∂μ = ∫ z, w z ^ 2 * ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ := by
    congr 1 with z
    simp [v, norm_smul, mul_pow]
  have h₁ := hG η hη hηc
  have h₂ := hA η (hη.of_le (by norm_num)) hηc
  rw [hnv] at h
  have := mul_le_mul_of_nonneg_left h₂ (by positivity : (0 : ℝ) ≤ 4 * M)
  nlinarith

end TauCeti.Vortex
