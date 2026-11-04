/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.PDE.Vortex.Decay
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.MeasureTheory.Constructions.HaarToSphere
import TauCeti.MeasureTheory.Integral.DivergenceTheorem.CompactSupport

/-!
# The flux of a plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has connection
`a = i (b₁ ds + b₂ dt)`, curvature `F_a = i (∂₁ b₂ - ∂₂ b₁) ds ∧ dt` and section
`α = 2 (p + i q)`. Suppose `x` solves the vortex equation on the whole plane and its section has
the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Then the curvature is integrable
(`TauCeti.Vortex.integrable_curvature`), and its flux is the winding number:

  `(2π)⁻¹ ∫ i F_a = m`, that is, `∫ (∂₁ b₂ - ∂₂ b₁) = -2π m`.

Since `*iF_a = (1 - |α|²) / 8` at a vortex, equivalently `∫ (1 - |α|²) = 16 π m`. Integrals are
with respect to Lebesgue measure on `ℂ`.

The proof integrates the curvature against radial cutoffs `χ_R`. Off the zeros of `α`, the
holomorphicity rows `∂bar_a α = 0` express the connection as
`b = (-∂₂ u, ∂₁ u) - ∇φ - m dθ`, where `u = log |α|` and `φ` is the phase of `α z⁻ᵐ`, a
single-valued function near infinity because of the framing. Integrating by parts against `χ_R`,
the gradient `∇φ` contributes nothing, `dθ` contributes exactly `2π`, and the term in `u` is
bounded by `sup_{|z| ≥ R} |u|` times the dilation-invariant `L¹` norm of `Δχ_R`. Since `u → 0`
at infinity, letting `R → ∞` gives the flux. No decay of the connection, the phase or any
derivative is assumed, and the connection need only be differentiable.

## Main results

* `TauCeti.Vortex.integral_curvature_eq_neg_two_pi_mul`: `∫ (∂₁ b₂ - ∂₂ b₁) = -2π m`.
* `TauCeti.Vortex.integral_one_sub_normSq_eq_sixteen_pi_mul`: `∫ (1 - |α|²) = 16 π m`.
* `TauCeti.Vortex.integral_curvature_eq_neg_two_pi_mul_of_mem_framedFieldSpace`: the flux
  identity for vortices in the affine field space `A_m^s`, `s > 1`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter InnerProductSpace Metric MeasureTheory Topology Laplacian
open scoped ContDiff

/-! ### Radial cutoffs -/

/-- The radial cutoff `χ_R(z) = σ(2 - |z / R|²)`, for Mathlib's smooth transition `σ`. It equals
one on the disc of radius `R` and vanishes outside the disc of radius `√2 R`. Unlike the cutoffs
of `TauCeti.exists_forall_contDiff_cutoff_ball_norm_laplacian_le`, it is explicitly radial, which
the computation of the winding term needs. -/
private def fluxCutoff (R : ℝ) (z : ℂ) : ℝ := Real.smoothTransition (2 - ‖R⁻¹ • z‖ ^ 2)

private theorem contDiff_fluxCutoff (R : ℝ) : ContDiff ℝ ∞ (fluxCutoff R) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub
    ((contDiff_norm_sq ℝ).comp (contDiff_const_smul R⁻¹)))

private theorem fluxCutoff_mem_Icc (R : ℝ) (z : ℂ) : fluxCutoff R z ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem fluxCutoff_eventuallyEq_one {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ < R) :
    fluxCutoff R =ᶠ[𝓝 z] fun _ ↦ 1 := by
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
  refine Real.smoothTransition.one_of_one_le ?_
  have : ‖R⁻¹ • w‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, inv_mul_lt_one₀ hR]
    exact mem_ball_zero_iff.1 hw
  nlinarith [norm_nonneg (R⁻¹ • w)]

private theorem fluxCutoff_eventuallyEq_zero {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : 2 * R < ‖z‖) :
    fluxCutoff R =ᶠ[𝓝 z] fun _ ↦ 0 := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
  refine Real.smoothTransition.zero_of_nonpos ?_
  have : 2 < ‖R⁻¹ • w‖ := by
    have hw' : 2 * R < ‖w‖ := hw
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, lt_inv_mul_iff₀ hR]
    linarith
  nlinarith

private theorem fderiv_fluxCutoff_eq_zero_of_norm_lt {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : ‖z‖ < R) : fderiv ℝ (fluxCutoff R) z = 0 := by
  rw [(fluxCutoff_eventuallyEq_one hR hz).fderiv_eq, fderiv_fun_const, Pi.zero_apply]

private theorem fderiv_fluxCutoff_eq_zero_of_lt_norm {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : 2 * R < ‖z‖) : fderiv ℝ (fluxCutoff R) z = 0 := by
  rw [(fluxCutoff_eventuallyEq_zero hR hz).fderiv_eq, fderiv_fun_const, Pi.zero_apply]

private theorem laplacian_fluxCutoff_eventuallyEq_zero {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : ‖z‖ < R) : Δ (fluxCutoff R) =ᶠ[𝓝 z] 0 := by
  filter_upwards [laplacian_congr_nhds (fluxCutoff_eventuallyEq_one hR hz)] with w hw
  rw [hw]
  simp

private theorem hasCompactSupport_fluxCutoff {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (fluxCutoff R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * R)) fun _ hz ↦
    (fluxCutoff_eventuallyEq_zero hR (by simpa using hz)).self_of_nhds

private theorem fderiv_fluxCutoff_apply (R : ℝ) (z v : ℂ) :
    fderiv ℝ (fluxCutoff R) z v =
      -(2 * (R⁻¹) ^ 2 * deriv Real.smoothTransition (2 - ‖R⁻¹ • z‖ ^ 2) *
        (z.re * v.re + z.im * v.im)) := by
  have h1 : HasFDerivAt (fun w : ℂ ↦ ‖R⁻¹ • w‖ ^ 2)
      ((2 • innerSL ℝ (R⁻¹ • z)).comp (R⁻¹ • ContinuousLinearMap.id ℝ ℂ)) z :=
    (hasStrictFDerivAt_norm_sq (R⁻¹ • z)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).const_smul R⁻¹)
  have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (2 - ‖R⁻¹ • z‖ ^ 2))
      (2 - ‖R⁻¹ • z‖ ^ 2) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have h4 := h2.comp_hasFDerivAt z ((hasFDerivAt_const (2 : ℝ) z).fun_sub h1)
  -- `fluxCutoff R` is by definition this composition.
  rw [HasFDerivAt.fderiv (f := fluxCutoff R) h4]
  simp [Complex.inner]
  ring

/-- The `L¹` norm of `Δχ_R` does not depend on `R`. -/
private theorem integral_abs_laplacian_fluxCutoff {R : ℝ} (hR : 0 < R) :
    ∫ z, |Δ (fluxCutoff R) z| = ∫ z, |Δ (fluxCutoff 1) z| := by
  have h : fluxCutoff R = fun z ↦ fluxCutoff 1 (R⁻¹ • z) := by
    ext z
    simp [fluxCutoff]
  rw [h, laplacian_comp_smul_right]
  simp only [smul_eq_mul, abs_mul, abs_pow, abs_inv, abs_of_pos hR]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun z ↦ |Δ (fluxCutoff 1) z|) hR.le, finrank_real_complex, smul_eq_mul, ← mul_assoc,
    inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hR.ne'), one_mul]

/-! ### The winding term -/

/-- The radial profile `2 R⁻² σ'(2 - (r / R)²)` of the winding term of `χ_R`. -/
private def fluxProfile (R r : ℝ) : ℝ :=
  2 * (R⁻¹) ^ 2 * deriv Real.smoothTransition (2 - (R⁻¹ * r) ^ 2)

/-- Pairing `dθ = Im (dz / z)` with the rotated gradient of `χ_R` gives a radial function. -/
private theorem winding_eq_fluxProfile (R : ℝ) (z : ℂ) :
    (1 / z).im * fderiv ℝ (fluxCutoff R) z I - (I / z).im * fderiv ℝ (fluxCutoff R) z 1 =
      fluxProfile R ‖z‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [fluxProfile, Real.smoothTransition.deriv_of_one_lt (by norm_num : (1 : ℝ) < 2)]
  have hn : normSq z ≠ 0 := normSq_eq_zero.not.2 hz
  have hnorm : ‖R⁻¹ • z‖ ^ 2 = (R⁻¹ * ‖z‖) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_pow]
  rw [fderiv_fluxCutoff_apply, fderiv_fluxCutoff_apply, fluxProfile, hnorm]
  generalize deriv Real.smoothTransition (2 - (R⁻¹ * ‖z‖) ^ 2) = τ
  simp only [div_im, one_re, one_im, I_re, I_im, zero_mul, mul_zero, sub_zero, zero_sub, one_mul,
    zero_div, mul_one, add_zero, zero_add]
  field_simp
  rw [normSq_apply]
  ring

private theorem continuous_fluxProfile (R : ℝ) : Continuous (fluxProfile R) :=
  continuous_const.mul ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl |>.comp
    (continuous_const.sub ((continuous_const.mul continuous_id).pow 2)))

private theorem fluxProfile_eq_zero_of_lt {R r : ℝ} (hR : 0 < R) (hr : r < R) (hr₀ : 0 ≤ r) :
    fluxProfile R r = 0 := by
  have h₁ : R⁻¹ * r < 1 := by rwa [inv_mul_lt_one₀ hR]
  have h₀ : 0 ≤ R⁻¹ * r := mul_nonneg (inv_nonneg.2 hR.le) hr₀
  rw [fluxProfile, Real.smoothTransition.deriv_of_one_lt (by nlinarith), mul_zero]

private theorem hasCompactSupport_fluxProfile {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (fun z : ℂ ↦ fluxProfile R ‖z‖) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * R)) fun z hz ↦ ?_
  have hz' : 2 * R < ‖z‖ := by simpa using hz
  have h2 : 2 < R⁻¹ * ‖z‖ := by rw [lt_inv_mul_iff₀ hR]; linarith
  rw [fluxProfile, Real.smoothTransition.deriv_of_neg (by nlinarith), mul_zero]

/-- The winding term integrates to `2π`, independently of `R`. -/
private theorem integral_fluxProfile {R : ℝ} (hR : 0 < R) :
    ∫ z : ℂ, fluxProfile R ‖z‖ = 2 * Real.pi := by
  have hrad := integral_norm_rpow_neg_finrank_mul_fderiv_apply_self (μ := (volume : Measure ℂ))
    ((contDiff_fluxCutoff R).of_le (by norm_num)) (hasCompactSupport_fluxCutoff hR)
  have hball : volume.real (ball (0 : ℂ) 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have h0 : fluxCutoff R 0 = 1 := Real.smoothTransition.one_of_one_le (by simp)
  rw [finrank_real_complex, hball, h0] at hrad
  -- The radial derivative of `χ_R`, weighted by `‖z‖⁻²`, is minus the winding profile.
  have hint (z : ℂ) : ‖z‖ ^ (-((2 : ℕ) : ℝ)) * fderiv ℝ (fluxCutoff R) z z =
      -fluxProfile R ‖z‖ := by
    rcases eq_or_ne z 0 with rfl | hz
    · simp [fluxProfile, Real.smoothTransition.deriv_of_one_lt (by norm_num : (1 : ℝ) < 2)]
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    have hsq : z.re * z.re + z.im * z.im = ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, normSq_apply]
    rw [fderiv_fluxCutoff_apply, hsq, fluxProfile, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      Nat.cast_ofNat, Real.rpow_neg (norm_nonneg z), Real.rpow_two]
    field_simp
  simp only [hint, integral_neg] at hrad
  push_cast at hrad
  linarith

/-! ### The phase near infinity -/

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The phase `Im log (α z⁻ᵐ)` of the section relative to the winding `zᵐ` is differentiable
where `α z⁻ᵐ` lies in the slit plane, and its derivative along `v` is the phase current
`(p ∂ᵥ q - q ∂ᵥ p) / (p² + q²)` of `α` minus `m Im (v / z) = m dθ(v)`. -/
private theorem hasFDerivAt_phase {m : ℕ} {z : ℂ} (hz : z ≠ 0)
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hT : sectionValue x z * (z ^ m)⁻¹ ∈ slitPlane) :
    DifferentiableAt ℝ (fun w ↦ (log (sectionValue x w * (w ^ m)⁻¹)).im) z ∧
      ∀ v : ℂ, fderiv ℝ (fun w ↦ (log (sectionValue x w * (w ^ m)⁻¹)).im) z v =
        (x z 2 * fderiv ℝ (fun w ↦ x w 3) z v - x z 3 * fderiv ℝ (fun w ↦ x w 2) z v) /
          (x z 2 ^ 2 + x z 3 ^ 2) - m * (v / z).im := by
  have hzm : z ^ m ≠ 0 := pow_ne_zero _ hz
  have hS : sectionValue x z ≠ 0 := by
    intro h; rw [h, zero_mul] at hT; exact slitPlane_ne_zero hT rfl
  have hinv : HasDerivAt (fun w : ℂ ↦ (w ^ m)⁻¹) (-(m * z ^ (m - 1)) / (z ^ m) ^ 2) z :=
    (hasDerivAt_pow m z).fun_inv hzm
  have hT' := (hasFDerivAt_sectionValue hp hq).mul (hinv.hasFDerivAt.restrictScalars ℝ)
  have hL : HasFDerivAt (fun w ↦ log (sectionValue x w * (w ^ m)⁻¹)) _ z :=
    (hasStrictDerivAt_log hT).hasDerivAt.comp_hasFDerivAt
      (f := fun w ↦ sectionValue x w * (w ^ m)⁻¹) z hT'
  have hI := imCLM.hasFDerivAt.comp z hL
  refine ⟨hI.differentiableAt, fun v ↦ ?_⟩
  -- `Complex.imCLM` applies `Complex.im`.
  rw [HasFDerivAt.fderiv (f := fun w ↦ (log (sectionValue x w * (w ^ m)⁻¹)).im) hI]
  set A := fderiv ℝ (fun w ↦ x w 2) z v
  set B := fderiv ℝ (fun w ↦ x w 3) z v
  set P := x z 2
  set Q := x z 3
  have hPQ : (P : ℂ) + Q * I ≠ 0 := by
    intro h; apply hS; rw [sectionValue_apply, h, mul_zero]
  have hpow : (m : ℂ) * z ^ (m - 1) = m * z ^ m / z := by
    rcases m with _ | k
    · simp
    · rw [Nat.add_sub_cancel, pow_succ, mul_div_assoc, mul_div_cancel_right₀ _ hz]
  -- The logarithmic derivative of `α z⁻ᵐ` is `∂ᵥ α / α - m v / z`.
  have key : (sectionValue x z * (z ^ m)⁻¹)⁻¹ * (sectionValue x z * (v *
      (-(m * z ^ (m - 1)) / (z ^ m) ^ 2)) + (z ^ m)⁻¹ * (2 * ((A : ℂ) + I * B))) =
      ((A : ℂ) + B * I) / (P + Q * I) - m * (v / z) := by
    rw [hpow, show sectionValue x z = 2 * ((P : ℂ) + Q * I) from sectionValue_apply x z]
    field_simp
    ring
  simp only [ContinuousLinearMap.comp_apply, imCLM_apply, smul_apply, add_apply, smul_eq_mul,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    ofRealCLM_apply]
  rw [key, sub_im, div_im]
  simp only [normSq_apply, ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im,
    natCast_re, natCast_im]
  rw [← sub_div]
  ring

/-- Where `α z⁻ᵐ` lies in the slit plane, the section does not vanish. -/
private theorem sq_add_sq_ne_zero_of_mem_slitPlane {m : ℕ} {z : ℂ}
    (hT : sectionValue x z * (z ^ m)⁻¹ ∈ slitPlane) : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := by
  intro h
  have hS : sectionValue x z = 0 := by
    have := sq_norm_sectionValue x z
    rwa [h, mul_zero, sq_eq_zero_iff, norm_eq_zero] at this
  rw [hS, zero_mul] at hT
  exact slitPlane_ne_zero hT rfl

/-! ### The divergence identity at a fixed radius -/

/-- The first component of `χ_R (b₂, -b₁) - u ∇χ_R - φ (∂₂ χ_R, -∂₁ χ_R)`, where
`u = log |α| = log |α|² / 2` and `φ = Im log (α z⁻ᵐ)`. -/
private def fluxFieldFst (x : ℂ → EuclideanSpace ℝ (Fin 4)) (m : ℕ) (R : ℝ) (w : ℂ) : ℝ :=
  fluxCutoff R w * x w 1 -
    Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) / 2 * fderiv ℝ (fluxCutoff R) w 1 -
      (log (sectionValue x w * (w ^ m)⁻¹)).im * fderiv ℝ (fluxCutoff R) w I

/-- The second component of `χ_R (b₂, -b₁) - u ∇χ_R - φ (∂₂ χ_R, -∂₁ χ_R)`. -/
private def fluxFieldSnd (x : ℂ → EuclideanSpace ℝ (Fin 4)) (m : ℕ) (R : ℝ) (w : ℂ) : ℝ :=
  -(fluxCutoff R w * x w 0) -
    Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) / 2 * fderiv ℝ (fluxCutoff R) w I +
      (log (sectionValue x w * (w ^ m)⁻¹)).im * fderiv ℝ (fluxCutoff R) w 1

private theorem differentiable_fderiv_fluxCutoff_apply (R : ℝ) (v : ℂ) :
    Differentiable ℝ (fun w ↦ fderiv ℝ (fluxCutoff R) w v) :=
  (((contDiff_fluxCutoff R).fderiv_right (m := 1) (by simp)).clm_apply
    contDiff_const).differentiable (by simp)

/-- Inside the disc of radius `R` the field is the rotated connection `(b₂, -b₁)`, and its
divergence is the curvature. -/
private theorem fluxField_of_norm_lt {m : ℕ} {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ < R)
    (hb₁ : DifferentiableAt ℝ (fun w ↦ x w 0) z) (hb₂ : DifferentiableAt ℝ (fun w ↦ x w 1) z) :
    DifferentiableAt ℝ (fluxFieldFst x m R) z ∧ DifferentiableAt ℝ (fluxFieldSnd x m R) z ∧
      fderiv ℝ (fluxFieldFst x m R) z 1 + fderiv ℝ (fluxFieldSnd x m R) z I =
        fluxCutoff R z * (fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) -
          Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 2 * Δ (fluxCutoff R) z +
            m * fluxProfile R ‖z‖ := by
  have h := (fluxCutoff_eventuallyEq_one hR hz).and
    (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz))
  have hf : fluxFieldFst x m R =ᶠ[𝓝 z] fun w ↦ x w 1 := h.mono fun w ⟨hw, hw'⟩ ↦ by
    simp [fluxFieldFst, hw, fderiv_fluxCutoff_eq_zero_of_norm_lt hR (mem_ball_zero_iff.1 hw')]
  have hg : fluxFieldSnd x m R =ᶠ[𝓝 z] fun w ↦ -x w 0 := h.mono fun w ⟨hw, hw'⟩ ↦ by
    simp [fluxFieldSnd, hw, fderiv_fluxCutoff_eq_zero_of_norm_lt hR (mem_ball_zero_iff.1 hw')]
  refine ⟨hb₂.congr_of_eventuallyEq hf, hb₁.neg.congr_of_eventuallyEq hg, ?_⟩
  rw [hf.fderiv_eq, hg.fderiv_eq, fderiv_fun_neg, h.self_of_nhds.1,
    (laplacian_fluxCutoff_eventuallyEq_zero hR hz).self_of_nhds,
    fluxProfile_eq_zero_of_lt hR hz (norm_nonneg z)]
  simp only [neg_apply, Pi.zero_apply, mul_zero, one_mul, add_zero]
  ring

/-- Where `α z⁻ᵐ` lies in the slit plane and the holomorphicity rows hold, the divergence of the
field is `χ_R F - u Δχ_R + m ⟨dθ, ⋆dχ_R⟩`, with `F = ∂₁ b₂ - ∂₂ b₁`. The rows express the
connection through `u` and the phase current of `α`, which is `∇φ + m dθ`, so every first-order
term cancels. -/
private theorem fluxField_of_mem_slitPlane {m : ℕ} (R : ℝ) {z : ℂ} (hz : z ≠ 0)
    (hT : sectionValue x z * (z ^ m)⁻¹ ∈ slitPlane)
    (hb₁ : DifferentiableAt ℝ (fun w ↦ x w 0) z) (hb₂ : DifferentiableAt ℝ (fun w ↦ x w 1) z)
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0) :
    DifferentiableAt ℝ (fluxFieldFst x m R) z ∧ DifferentiableAt ℝ (fluxFieldSnd x m R) z ∧
      fderiv ℝ (fluxFieldFst x m R) z 1 + fderiv ℝ (fluxFieldSnd x m R) z I =
        fluxCutoff R z * (fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) -
          Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 2 * Δ (fluxCutoff R) z +
            m * fluxProfile R ‖z‖ := by
  set ℓ : ℂ → ℝ := fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))
  set φ : ℂ → ℝ := fun w ↦ (log (sectionValue x w * (w ^ m)⁻¹)).im
  have hχs := contDiff_fluxCutoff R
  have hχd : DifferentiableAt ℝ (fluxCutoff R) z := hχs.differentiable (by simp) z
  have hdχ := differentiable_fderiv_fluxCutoff_apply R
  have hρ := sq_add_sq_ne_zero_of_mem_slitPlane hT
  have hℓd : DifferentiableAt ℝ ℓ z :=
    ((differentiableAt_const _).mul ((hp.pow 2).add (hq.pow 2))).log
      (mul_ne_zero four_ne_zero hρ)
  obtain ⟨hφd, hφ'⟩ := hasFDerivAt_phase hz hp hq hT
  have hu : HasFDerivAt (fun w ↦ ℓ w / 2) ((2 : ℝ)⁻¹ • fderiv ℝ ℓ z) z := by
    simpa only [div_eq_inv_mul] using hℓd.hasFDerivAt.const_mul (2 : ℝ)⁻¹
  have hfD := ((hχd.hasFDerivAt.fun_mul hb₂.hasFDerivAt).fun_sub
    (hu.fun_mul (hdχ 1 z).hasFDerivAt)).fun_sub (hφd.hasFDerivAt.fun_mul (hdχ I z).hasFDerivAt)
  have hgD := ((hχd.hasFDerivAt.fun_mul hb₁.hasFDerivAt).fun_neg.fun_sub
    (hu.fun_mul (hdχ I z).hasFDerivAt)).fun_add (hφd.hasFDerivAt.fun_mul (hdχ 1 z).hasFDerivAt)
  refine ⟨hfD.differentiableAt, hgD.differentiableAt, ?_⟩
  -- The holomorphicity rows give the derivatives of `log |α|²`; the phase derivatives
  -- differ from the phase current of `α` by `m dθ`.
  have hℓ1 : fderiv ℝ ℓ z 1 = _ := fderiv_log_normSq_apply_one hp hq hρ h₁ h₂
  have hℓI : fderiv ℝ ℓ z I = _ := fderiv_log_normSq_apply_I hp hq hρ h₁ h₂
  have hφ1 := hφ' 1
  have hφI := hφ' I
  -- Second derivatives of the cutoff: the Laplacian and the symmetry of mixed partials.
  have hdd : DifferentiableAt ℝ (fderiv ℝ (fluxCutoff R)) z :=
    (hχs.fderiv_right (m := 1) (by simp)).differentiable (by simp) z
  have hΔ : Δ (fluxCutoff R) z = fderiv ℝ (fun w ↦ fderiv ℝ (fluxCutoff R) w 1) z 1 +
      fderiv ℝ (fun w ↦ fderiv ℝ (fluxCutoff R) w I) z I := by
    rw [TauCeti.laplacian_eq_sum_fderiv_fderiv_apply orthonormalBasisOneI hdd, Fin.sum_univ_two]
    simp
  have hsym : fderiv ℝ (fun w ↦ fderiv ℝ (fluxCutoff R) w I) z 1 =
      fderiv ℝ (fun w ↦ fderiv ℝ (fluxCutoff R) w 1) z I := by
    rw [fderiv_clm_apply hdd (differentiableAt_const _),
      fderiv_clm_apply hdd (differentiableAt_const _)]
    simpa using ((hχs.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)).eq 1 I
  have hwind := winding_eq_fluxProfile R z
  -- `hfD` and `hgD` differentiate the defining formulas of the two components.
  rw [HasFDerivAt.fderiv (f := fluxFieldFst x m R) hfD,
    HasFDerivAt.fderiv (f := fluxFieldSnd x m R) hgD]
  simp only [add_apply, sub_apply, neg_apply, smul_apply, smul_eq_mul]
  linear_combination (-fderiv ℝ (fluxCutoff R) z 1 / 2) * hℓ1 +
    (-fderiv ℝ (fluxCutoff R) z I / 2) * hℓI + (-fderiv ℝ (fluxCutoff R) z I) * hφ1 +
    fderiv ℝ (fluxCutoff R) z 1 * hφI + (ℓ z / 2) * hΔ + (-φ z) * hsym + (m : ℝ) * hwind

private theorem hasCompactSupport_fluxField {m : ℕ} {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (fluxFieldFst x m R) ∧ HasCompactSupport (fluxFieldSnd x m R) := by
  have hzero {z : ℂ} (hz : z ∉ closedBall (0 : ℂ) (2 * R)) :
      fluxCutoff R z = 0 ∧ fderiv ℝ (fluxCutoff R) z = 0 := by
    have hz' : 2 * R < ‖z‖ := by simpa using hz
    exact ⟨(fluxCutoff_eventuallyEq_zero hR hz').self_of_nhds,
      fderiv_fluxCutoff_eq_zero_of_lt_norm hR hz'⟩
  exact ⟨.intro (isCompact_closedBall (0 : ℂ) (2 * R)) fun z hz ↦ by
      simp [fluxFieldFst, hzero hz],
    .intro (isCompact_closedBall (0 : ℂ) (2 * R)) fun z hz ↦ by simp [fluxFieldSnd, hzero hz]⟩

/-- The flux identity at a fixed cutoff radius: if `α z⁻ᵐ` lies in the slit plane off the disc
of radius `R₀ < R`, then `∫ χ_R F = ∫ (log |α|² / 2) Δχ_R - 2π m`, where `F = ∂₁ b₂ - ∂₂ b₁`. -/
private theorem integral_fluxCutoff_mul_curvature {m : ℕ} {R₀ R : ℝ} (hR : 0 < R) (hR₀ : R₀ < R)
    (hV : ∀ z : ℂ, R₀ < ‖z‖ → z ≠ 0 ∧ sectionValue x z * (z ^ m)⁻¹ ∈ slitPlane)
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hcurv : Integrable fun z ↦ fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) :
    ∫ z, fluxCutoff R z * (fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) =
      (∫ z, Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 2 * Δ (fluxCutoff R) z) -
        2 * Real.pi * m := by
  -- Every point lies inside the disc of radius `R` or in the region where `α z⁻ᵐ` is in the
  -- slit plane, and the divergence of the field has the same formula in both.
  have hfield (z : ℂ) :
      DifferentiableAt ℝ (fluxFieldFst x m R) z ∧ DifferentiableAt ℝ (fluxFieldSnd x m R) z ∧
        fderiv ℝ (fluxFieldFst x m R) z 1 + fderiv ℝ (fluxFieldSnd x m R) z I =
          fluxCutoff R z * (fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) -
            Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 2 * Δ (fluxCutoff R) z +
              m * fluxProfile R ‖z‖ := by
    rcases lt_or_ge ‖z‖ R with hz | hz
    · exact fluxField_of_norm_lt hR hz (hb₁ z) (hb₂ z)
    · obtain ⟨hz0, hT⟩ := hV z (hR₀.trans_le hz)
      have h := hsol z
      exact fluxField_of_mem_slitPlane R hz0 hT (hb₁ z) (hb₂ z) (hp z) (hq z)
        (by rw [h]; rfl) (by rw [h]; rfl)
  obtain ⟨hfc, hgc⟩ := hasCompactSupport_fluxField (x := x) (m := m) hR
  have hχs := contDiff_fluxCutoff R
  -- Integrability of the three terms of the divergence.
  have hI₁ : Integrable fun z ↦
      fluxCutoff R z * (fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) :=
    hcurv.bdd_mul (c := 1) hχs.continuous.aestronglyMeasurable (ae_of_all _ fun z ↦ by
      rw [Real.norm_of_nonneg (fluxCutoff_mem_Icc R z).1]; exact (fluxCutoff_mem_Icc R z).2)
  have hI₂ : Integrable fun z ↦ Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 2 *
      Δ (fluxCutoff R) z := by
    refine Continuous.integrable_of_hasCompactSupport (continuous_iff_continuousAt.2 fun z ↦ ?_)
      (hasCompactSupport_fluxCutoff hR).laplacian.mul_left
    rcases lt_or_ge ‖z‖ R with hz | hz
    · refine continuousAt_const (y := (0 : ℝ)).congr ?_
      filter_upwards [laplacian_fluxCutoff_eventuallyEq_zero hR hz] with w hw
      simp [hw]
    · have hρ := sq_add_sq_ne_zero_of_mem_slitPlane (hV z (hR₀.trans_le hz)).2
      exact ((((continuous_const.mul (((hp.continuous.pow 2).add
        (hq.continuous.pow 2)))).continuousAt.log (mul_ne_zero four_ne_zero hρ)).div_const 2).mul
          (hχs.of_le (by simp)).continuous_laplacian.continuousAt)
  have hI₃ : Integrable fun z : ℂ ↦ (m : ℝ) * fluxProfile R ‖z‖ :=
    (((continuous_fluxProfile R).comp continuous_norm).integrable_of_hasCompactSupport
      (hasCompactSupport_fluxProfile hR)).const_mul _
  have hI₁₂ : Integrable fun z ↦
      fluxCutoff R z * (fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) -
        Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 2 * Δ (fluxCutoff R) z := hI₁.sub hI₂
  -- The divergence integrates to zero; the winding term contributes `2π m`.
  have h0 := integral_fderiv_one_add_fderiv_I_eq_zero (fun z ↦ (hfield z).1)
    (fun z ↦ (hfield z).2.1) hfc hgc
    ((hI₁₂.add hI₃).congr (ae_of_all _ fun z ↦ (hfield z).2.2.symm))
  simp_rw [fun z ↦ (hfield z).2.2] at h0
  rw [integral_add hI₁₂ hI₃, integral_sub hI₁ hI₂, integral_const_mul,
    integral_fluxProfile hR] at h0
  linear_combination h0

/-! ### Passage to the limit -/

/-- The cutoff integrals `∫ χ_R F` of an integrable function converge to `∫ F`. -/
private theorem tendsto_integral_fluxCutoff_mul {F : ℂ → ℝ} (hF : Integrable F) :
    Tendsto (fun R : ℝ ↦ ∫ z, fluxCutoff R z * F z) atTop (𝓝 (∫ z, F z)) := by
  refine tendsto_integral_filter_of_dominated_convergence _
    (.of_forall fun R ↦ (contDiff_fluxCutoff R).continuous.aestronglyMeasurable.mul
      hF.aestronglyMeasurable)
    (.of_forall fun R ↦ ae_of_all _ fun z ↦ ?_) hF.norm (ae_of_all _ fun z ↦ ?_)
  · rw [norm_mul, Real.norm_of_nonneg (fluxCutoff_mem_Icc R z).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (fluxCutoff_mem_Icc R z).2
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (max ‖z‖ 0)] with R hR
    rw [(fluxCutoff_eventuallyEq_one (lt_of_le_of_lt (le_max_right _ _) hR)
      (lt_of_le_of_lt (le_max_left _ _) hR)).self_of_nhds, one_mul]

/-- If `u → 0` at infinity, then `∫ u Δχ_R → 0`: the Laplacian `Δχ_R` is supported where
`|z| ≥ R`, and its `L¹` norm does not depend on `R`. -/
private theorem tendsto_integral_mul_laplacian_fluxCutoff {u : ℂ → ℝ}
    (hu : Tendsto u (cocompact ℂ) (𝓝 0)) :
    Tendsto (fun R : ℝ ↦ ∫ z, u z * Δ (fluxCutoff R) z) atTop (𝓝 0) := by
  set A := ∫ z, |Δ (fluxCutoff 1) z|
  have hA₀ : 0 ≤ A := integral_nonneg fun _ ↦ abs_nonneg _
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  have hδ : 0 < ε / (A + 1) := div_pos hε (by linarith)
  obtain ⟨R₂, -, hR₂⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ hu.eventually (Metric.ball_mem_nhds 0 hδ))
  refine ⟨max R₂ 1, fun R hR ↦ ?_⟩
  have hR₁ : 0 < R := zero_lt_one.trans_le ((le_max_right _ _).trans hR)
  have hΔi : Integrable fun z ↦ |Δ (fluxCutoff R) z| :=
    ((contDiff_fluxCutoff R).of_le (by simp)).continuous_laplacian.abs
      |>.integrable_of_hasCompactSupport (hasCompactSupport_fluxCutoff hR₁).laplacian.abs
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hΔi.const_mul (ε / (A + 1)))
    (ae_of_all _ fun z ↦ ?_)).trans_lt ?_
  · rw [norm_mul, Real.norm_eq_abs (Δ (fluxCutoff R) z)]
    rcases lt_or_ge ‖z‖ R with hz | hz
    · simp [(laplacian_fluxCutoff_eventuallyEq_zero hR₁ hz).self_of_nhds]
    · have h := hR₂ ((le_max_left _ _).trans (hR.trans hz))
      rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs] at h
      exact mul_le_mul_of_nonneg_right h.le (abs_nonneg _)
  · rw [integral_const_mul, integral_abs_laplacian_fluxCutoff hR₁, div_mul_eq_mul_div,
      div_lt_iff₀ (by linarith)]
    nlinarith

/-- Near infinity the framing makes `α z⁻ᵐ` a positive multiple of `α (z / |z|)⁻ᵐ`, which has
positive real part. -/
private theorem exists_forall_mem_slitPlane {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ R₀ : ℝ, ∀ z : ℂ, R₀ < ‖z‖ → z ≠ 0 ∧ sectionValue x z * (z ^ m)⁻¹ ∈ slitPlane := by
  have hT : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 ∧ sectionValue x z * (z ^ m)⁻¹ ∈ slitPlane := by
    filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact,
      hframe.eventually ((isOpen_lt continuous_const continuous_re).mem_nhds
        (by simp : (0 : ℝ) < (1 : ℂ).re))] with z hz hre
    refine ⟨hz, mem_slitPlane_iff.2 (Or.inl ?_)⟩
    have hn : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
    have he : sectionValue x z * (z ^ m)⁻¹ =
        sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹ * ((‖z‖ ^ m : ℝ) : ℂ)⁻¹ := by
      rw [div_pow, inv_div, ofReal_pow]
      field_simp
    rw [he, ← ofReal_inv, re_mul_ofReal]
    exact mul_pos hre (inv_pos.2 (pow_pos (norm_pos_iff.2 hz) m))
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ hT)
  exact ⟨R₀, fun z hz ↦ hR₀ hz.le⟩

/-! ### The flux identity -/

/-- **The flux identity for plane vortices.** A vortex on the whole plane whose section has the
degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1` has `∫ (∂₁ b₂ - ∂₂ b₁) = -2π m`; that is,
`(2π)⁻¹ ∫ i F_a = m`. -/
theorem integral_curvature_eq_neg_two_pi_mul {m : ℕ}
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∫ z, (fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) = -(2 * Real.pi * m) := by
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe
  have hcurv := integrable_curvature volume hb₁ hb₂ hp hq hsol hlim
  have hu : Tendsto (fun z ↦ Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 2) (cocompact ℂ) (𝓝 0) := by
    simpa [Function.comp_def] using
      ((Real.continuousAt_log one_ne_zero).tendsto.comp hlim).div_const 2
  obtain ⟨R₀, hR₀⟩ := exists_forall_mem_slitPlane hframe
  -- For large `R` the cutoff flux is the logarithmic error term minus `2π m`.
  have hcore : ∀ᶠ R in atTop,
      (∫ z, Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 2 * Δ (fluxCutoff R) z) -
        2 * Real.pi * m =
      ∫ z, fluxCutoff R z * (fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) := by
    filter_upwards [eventually_gt_atTop (max R₀ 0)] with R hR
    exact (integral_fluxCutoff_mul_curvature (lt_of_le_of_lt (le_max_right _ _) hR)
      (lt_of_le_of_lt (le_max_left _ _) hR) hR₀ hb₁ hb₂
      (hp.differentiable (by norm_num)) (hq.differentiable (by norm_num)) hsol hcurv).symm
  have hC := ((tendsto_integral_mul_laplacian_fluxCutoff hu).sub_const
    (2 * Real.pi * m)).congr' hcore
  rw [tendsto_nhds_unique (tendsto_integral_fluxCutoff_mul hcurv) hC, zero_sub]

/-- **The flux identity in terms of the modulus.** A vortex on the whole plane whose section has
the degree-`m` end framing has `∫ (1 - |α|²) = 16 π m`. -/
theorem integral_one_sub_normSq_eq_sixteen_pi_mul {m : ℕ}
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∫ z, (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) = 16 * Real.pi * m := by
  have h := integral_curvature_eq_neg_two_pi_mul hb₁ hb₂ hp hq hsol hframe
  have he : ∫ z, (fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) =
      -(1 / 8) * ∫ z, (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    simp only [curvature_eq_of_equation_eq_zero (hsol z)]
    ring
  linarith

/-- **The flux identity in the affine field space.** For `s > 1`, a vortex in `A_m^s` with
differentiable connection and `C²` section has `∫ (∂₁ b₂ - ∂₂ b₁) = -2π m`. -/
theorem integral_curvature_eq_neg_two_pi_mul_of_mem_framedFieldSpace
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ}
    (hs : 1 < s) (hx : x ∈ framedFieldSpace f m s)
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) :
    ∫ z, (fderiv ℝ (fun w ↦ x w 1) z 1 - fderiv ℝ (fun w ↦ x w 0) z I) = -(2 * Real.pi * m) := by
  have hcont : Continuous x := by
    refine contDiff_zero.1 (contDiff_euclidean.2 fun i ↦ contDiff_zero.2 ?_)
    fin_cases i
    exacts [hb₁.continuous, hb₂.continuous, hp.continuous, hq.continuous]
  exact integral_curvature_eq_neg_two_pi_mul hb₁ hb₂ hp hq hsol
    (tendsto_sectionValue_mul_inv_pow hs hx hcont)

end TauCeti.Vortex
