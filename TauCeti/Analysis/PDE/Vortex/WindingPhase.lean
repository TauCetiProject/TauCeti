/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Plane vortices in the winding end trivialization

The winding phase `(z / |z|)^m` (`TauCeti.Vortex.windingPhase`) is a smooth circle-valued map
off the origin, with logarithmic derivative `m dθ`, where `dθ_z(v) = Im (v / z)`
(`TauCeti.Vortex.gaugeForm_windingPhase`). The gauge transformation by its inverse is the
**winding-`m` end trivialization**: away from the origin it is an actual charge-one gauge
transformation, but it is not a framed gauge on the whole plane. Outside the cutoff disc it takes
the reference field `(-i m dθ, (z / |z|)^m)` of the affine field space `A_m^s` to the vacuum
`(0, 1)` (`TauCeti.Vortex.gaugeTransform_inv_windingPhase_referenceField`).

A plane vortex is normalized at its end when, outside a disc, its section is `|α|` times the
winding phase, so that its end trivialization has a positive real section. For such a vortex,
the holomorphicity rows `∂bar_a α = 0` make the covariant derivative of the real section `|α|`
complex linear, which determines the connection coefficients in the end trivialization outside a
disc as `(-(1 / 2) ∂_t log |α|², (1 / 2) ∂_s log |α|²)`
(`TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_zero_of_equation_eq_zero`,
`TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_one_of_equation_eq_zero`), and correspondingly
determines `x - x_ref` (`TauCeti.Vortex.sub_referenceField_apply_eq`).

Every smooth field with the degree-`m` end framing `α (z / |z|)^(-m) → 1` is equivalent under the
smooth framed gauge group to one normalized at its end
(`TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq`): the smooth framed gauge making
`g = α (z / |z|)^(-m)` positive near infinity (`TauCeti.Vortex.exists_framedGaugeGroup_mul_eq_norm`)
does this, without choosing a logarithm of the phase. All-order exponential derivative decay for
such vortices and the resulting framed gauge representatives in `A_m^s` are proved in
`TauCeti.Analysis.PDE.Vortex.FramedGauge.DerivativeDecay` and
`TauCeti.Analysis.PDE.Vortex.FramedGauge.Moduli`.

## Main definitions

* `TauCeti.Vortex.windingPhase m`: the winding phase `(z / |z|)^m` as a map `ℂ → Circle`.

## Main results

* `TauCeti.Vortex.gaugeForm_windingPhase`: the logarithmic derivative of the winding phase.
* `TauCeti.Vortex.gaugeTransform_inv_windingPhase_referenceField`: the end trivialization takes
  the reference field to the vacuum outside the cutoff disc.
* `TauCeti.Vortex.sub_referenceField_apply_eq`: outside the cutoff disc, `x - x_ref` is the end
  trivialization of `x` minus the vacuum, with its section part rotated by the winding phase.
* `TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_zero_of_equation_eq_zero`,
  `TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_one_of_equation_eq_zero`: the end
  trivialization of a vortex normalized at its end has connection `(i / 2) ⋆ d log |α|²`.
* `TauCeti.Vortex.sub_referenceField_apply_zero_of_equation_eq_zero`,
  `TauCeti.Vortex.sub_referenceField_apply_one_of_equation_eq_zero`: its connection is
  `a_ref + (i / 2) ⋆ d log |α|²` outside the cutoff disc.
* `TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq`: framed gauge normalization of the
  end phase.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex ComplexConjugate Filter Metric
open scoped Topology ContDiff

/-! ### The winding phase -/

/-- The winding phase `(z / |z|)^m` as a circle-valued map on the plane. At the origin, where it
has no continuous extension for `m ≠ 0`, its value is `1`. -/
def windingPhase (m : ℕ) (z : ℂ) : Circle :=
  Circle.exp (m * arg z)

/-- The winding phase of degree zero is `1`. -/
@[simp]
theorem windingPhase_zero_left (z : ℂ) : windingPhase 0 z = 1 := by
  simp [windingPhase]

/-- The winding phase is `1` at the origin. -/
@[simp]
theorem windingPhase_zero_right (m : ℕ) : windingPhase m 0 = 1 := by
  simp [windingPhase]

/-- Off the origin, the winding phase is `(z / |z|)^m`. -/
theorem coe_windingPhase (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    (windingPhase m z : ℂ) = (z / (‖z‖ : ℂ)) ^ m := by
  rw [windingPhase, Circle.exp_natCast_mul, Circle.coe_pow, Circle.coe_exp, exp_arg_mul_I hz]

/-- The winding phase is smooth off the origin. -/
theorem contDiffAt_windingPhase (m : ℕ) {z : ℂ} (hz : z ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun w ↦ (windingPhase m w : ℂ)) z := by
  refine ((contDiffOn_div_norm_pow m).contDiffAt (isOpen_compl_singleton.mem_nhds hz))
    |>.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
  exact coe_windingPhase m hw

/-- The winding phase is differentiable off the origin. -/
theorem differentiableAt_windingPhase (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℝ (fun w ↦ (windingPhase m w : ℂ)) z :=
  (contDiffAt_windingPhase m hz (n := 1)).differentiableAt one_ne_zero

/-- Off the origin, the winding phase is its value at `z` times the exponential of the real
phase `m Im (log (w / z))`, which is smooth near `w = z`. -/
private theorem windingPhase_eq_mul_exp (m : ℕ) {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    windingPhase m w = windingPhase m z * Circle.exp (m * (log (w / z)).im) := by
  apply Circle.ext
  rw [Circle.exp_natCast_mul, Circle.coe_mul, Circle.coe_pow, Circle.coe_exp, log_im,
    exp_arg_mul_I (div_ne_zero hw hz), coe_windingPhase m hw, coe_windingPhase m hz, ← mul_pow,
    norm_div, ofReal_div]
  have hz' : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have hw' : (‖w‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hw)
  congr 1
  field_simp

/-- The logarithmic derivative of the winding phase is `m dθ`, where `dθ_z(v) = Im (v / z)`. -/
theorem gaugeForm_windingPhase (m : ℕ) {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    gaugeForm (windingPhase m) z v = m * (v / z).im := by
  set φ : ℂ → ℝ := fun w ↦ m * (log (w / z)).im
  -- The complex derivative of `log (w / z)` at `w = z` is `1 / z`.
  have hlog : HasDerivAt (fun w ↦ log (w / z)) ((1 / z) / (z / z)) z :=
    ((hasDerivAt_id z).div_const z).clog (by simp [hz])
  have hφ : HasFDerivAt φ ((m : ℝ) • (imCLM ∘L
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((1 / z) / (z / z))).restrictScalars ℝ)))
      z :=
    (imCLM.hasFDerivAt.comp z (hlog.hasFDerivAt.restrictScalars ℝ)).const_mul (m : ℝ)
  set U : ℂ → Circle := (fun _ ↦ windingPhase m z) * fun w ↦ Circle.exp (φ w)
  have heq : (fun w ↦ (windingPhase m w : ℂ)) =ᶠ[𝓝 z] fun w ↦ (U w : ℂ) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    simp only [windingPhase_eq_mul_exp m hz hw, U, φ, Pi.mul_apply]
  have hconst : DifferentiableAt ℝ (fun _ : ℂ ↦ (windingPhase m z : ℂ)) z :=
    differentiableAt_const _
  have hexp : DifferentiableAt ℝ (fun w ↦ (Circle.exp (φ w) : ℂ)) z := by
    have h := ((ofRealCLM.hasFDerivAt.comp z hφ).mul_const I).cexp.differentiableAt
    simp only [Function.comp_def, ofRealCLM_apply] at h
    simpa only [Circle.coe_exp] using h
  have hform : gaugeForm (windingPhase m) z = gaugeForm U z := by
    ext a
    simp only [gaugeForm_apply, heq.fderiv_eq, heq.eq_of_nhds]
  rw [hform, gaugeForm_mul hconst hexp, gaugeForm_exp hφ.differentiableAt, hφ.fderiv]
  simp [div_self hz, div_eq_mul_inv, mul_comm]

/-- Off the origin, the derivative of the winding phase has norm at most `m / |z|`. -/
theorem norm_fderiv_windingPhase_le (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ‖fderiv ℝ (fun w ↦ (windingPhase m w : ℂ)) z‖ ≤ m / ‖z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [fderiv_coe_eq_mul_gaugeForm, gaugeForm_windingPhase m hz, norm_mul, norm_mul,
    Circle.norm_coe, norm_I, one_mul, one_mul, norm_real, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  calc (m : ℝ) * |(v / z).im| ≤ m * (‖v‖ / ‖z‖) := by
        gcongr
        exact (abs_im_le_norm _).trans (norm_div v z).le
    _ = m / ‖z‖ * ‖v‖ := by ring

/-! ### The end trivialization of the reference field -/

/-- **The end trivialization of the reference field is the vacuum.** Outside the cutoff disc,
the gauge transformation by the inverse winding phase takes the reference field
`(-i m dθ, (z / |z|)^m)` to the vacuum `(0, 1)`. -/
theorem gaugeTransform_inv_windingPhase_referenceField (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    {z : ℂ} (hz : f.rOut ≤ ‖z‖ ^ 2) :
    gaugeTransform (windingPhase m)⁻¹ (referenceField f m) z = vacuumField z := by
  have hz₀ := ne_zero_of_rOut_le_norm_sq f hz
  have hn := Circle.re_sq_add_im_sq (windingPhase m z)
  have hsec : referenceSection f m z = windingPhase m z := by
    rw [referenceSection_eq_phase f m hz, coe_windingPhase m hz₀]
  have hform := gaugeForm_inv (differentiableAt_windingPhase m hz₀)
  rw [gaugeTransform_apply, referenceField_apply, hsec, vacuumField_apply]
  ext i
  fin_cases i
  · simp [referenceConnection_eq_angular f m hz, hform, gaugeForm_windingPhase m hz₀]
  · simp [referenceConnection_eq_angular f m hz, hform, gaugeForm_windingPhase m hz₀]
  · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, Pi.inv_apply, Circle.coe_inv,
      inv_re, inv_im, Circle.normSq_coe, div_one]
    linear_combination hn / 2
  · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, Pi.inv_apply, Circle.coe_inv,
      inv_re, inv_im, Circle.normSq_coe, div_one]
    ring

/-! ### Exponential convergence to the reference field -/

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}

/-- If the section of `x` is `|α|` times the winding phase at `z`, then the first section
coordinate of its end trivialization is `|α| / 2` there. -/
theorem gaugeTransform_inv_windingPhase_apply_two {z : ℂ}
    (hphase : sectionValue x z = ‖sectionValue x z‖ * windingPhase m z) :
    gaugeTransform (windingPhase m)⁻¹ x z 2 = ‖sectionValue x z‖ / 2 := by
  simpa only [ofReal_re] using (sectionValue_eq_iff.1 (sectionValue_gaugeTransform_inv_eq hphase)).1

/-- If the section of `x` is `|α|` times the winding phase at `z`, then the second section
coordinate of its end trivialization vanishes there. -/
theorem gaugeTransform_inv_windingPhase_apply_three {z : ℂ}
    (hphase : sectionValue x z = ‖sectionValue x z‖ * windingPhase m z) :
    gaugeTransform (windingPhase m)⁻¹ x z 3 = 0 := by
  simpa only [ofReal_im, zero_div] using
    (sectionValue_eq_iff.1 (sectionValue_gaugeTransform_inv_eq hphase)).2

/-! ### The connection of an end-normalized vortex -/

/-- The connection coefficients of the end trivialization of `x` at a point `z ≠ 0` near which the
section of `x` is `|α|` times the winding phase, with `α (z) ≠ 0` and `∂bar_a α = 0` at `z`. The
section of the end trivialization is the positive real function `|α|`, and its covariant derivative
is complex linear, so its real and imaginary parts give `∂_t |α| = -b'₁ |α|` and
`∂_s |α| = b'₂ |α|`. -/
private theorem gaugeTransform_inv_windingPhase_apply_zero_one {z : ℂ} (hz : z ≠ 0)
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hα : sectionValue x z ≠ 0) :
    gaugeTransform (windingPhase m)⁻¹ x z 0 =
        -(fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z I / 2) ∧
      gaugeTransform (windingPhase m)⁻¹ x z 1 =
        fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z 1 / 2 := by
  set y := gaugeTransform (windingPhase m)⁻¹ x
  set N : ℂ → ℝ := fun w ↦ ‖sectionValue x w‖ with hN
  have hu := Circle.differentiableAt_coe_inv (differentiableAt_windingPhase m hz)
  -- `|α|` is differentiable at `z`, and `log |α|² = 2 log |α|`.
  have hNz : 0 < N z := norm_pos_iff.mpr hα
  have hNd : DifferentiableAt ℝ N z := (hasFDerivAt_norm_sectionValue hp hq hα).differentiableAt
  have hℓ (v : ℂ) : fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z v =
      2 * fderiv ℝ N z v / N z := by
    have heq : (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) =
        fun w ↦ Real.log (N w ^ 2) := funext fun w ↦ by rw [hN, sq_norm_sectionValue]
    rw [heq, ((hNd.hasFDerivAt.pow 2).log (by positivity)).fderiv]
    simp only [smul_apply, smul_eq_mul, Nat.add_one_sub_one, pow_one,
      nsmul_eq_mul, Nat.cast_ofNat]
    field_simp
  -- The section of the end trivialization is `|α|` near `z`, so its derivative is real.
  have hσ : sectionValue y =ᶠ[𝓝 z] fun w ↦ ofRealCLM (N w) :=
    hphase.mono fun w hw ↦ sectionValue_gaugeTransform_inv_eq hw
  have hcov (v : ℂ) : covariantDerivative y z v =
      (fderiv ℝ N z v : ℂ) + I * ((y z 0 * v.re + y z 1 * v.im : ℝ) : ℂ) * N z := by
    have hd : HasFDerivAt (fun w ↦ ofRealCLM (N w)) (ofRealCLM.comp (fderiv ℝ N z)) z :=
      ofRealCLM.hasFDerivAt.comp z hNd.hasFDerivAt
    rw [covariantDerivative_apply, hσ.fderiv_eq, hσ.self_of_nhds, hd.fderiv]
    simp
  -- The covariant derivative of the end trivialization is complex linear, like that of `x`.
  have hlin : covariantDerivative y z I = I * covariantDerivative y z 1 := by
    rw [covariantDerivative_gaugeTransform hu hp hq, covariantDerivative_gaugeTransform hu hp hq,
      covariantDerivative_eq_mul_of_equation_eq_zero hp hq h₁ h₂ I]
    ring
  rw [hcov, hcov] at hlin
  have hre := congrArg Complex.re hlin
  have him := congrArg Complex.im hlin
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, one_re, one_im]
    at hre him
  constructor
  · rw [hℓ I]
    field_simp
    nlinarith
  · rw [hℓ 1]
    field_simp
    nlinarith

/-- **The connection of an end-normalized vortex.** At a point `z ≠ 0` near which the section of
`x` is `|α|` times the winding phase, where `α (z) ≠ 0` and `∂bar_a α = 0`, the first connection
coefficient of the end trivialization of `x` is `-(1 / 2) ∂_t log |α|²`. -/
theorem gaugeTransform_inv_windingPhase_apply_zero_of_equation_eq_zero {z : ℂ} (hz : z ≠ 0)
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hα : sectionValue x z ≠ 0) :
    gaugeTransform (windingPhase m)⁻¹ x z 0 =
      -(fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z I / 2) :=
  (gaugeTransform_inv_windingPhase_apply_zero_one hz hp hq h₁ h₂ hphase hα).1

/-- **The connection of an end-normalized vortex.** At a point `z ≠ 0` near which the section of
`x` is `|α|` times the winding phase, where `α (z) ≠ 0` and `∂bar_a α = 0`, the second connection
coefficient of the end trivialization of `x` is `(1 / 2) ∂_s log |α|²`. -/
theorem gaugeTransform_inv_windingPhase_apply_one_of_equation_eq_zero {z : ℂ} (hz : z ≠ 0)
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hα : sectionValue x z ≠ 0) :
    gaugeTransform (windingPhase m)⁻¹ x z 1 =
      fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z 1 / 2 :=
  (gaugeTransform_inv_windingPhase_apply_zero_one hz hp hq h₁ h₂ hphase hα).2

/-- **`x - x_ref` outside the cutoff disc.** Since the end trivialization of the reference field
is the vacuum, outside the cutoff disc `x - x_ref` is `g = u⁻¹ · x - vacuum` with its section part
rotated by the winding phase `u`, which there equals the reference section `s`: its connection
coefficients are those of `g`, and its section is `s` times the section of `g`. -/
theorem sub_referenceField_apply_eq (f : ContDiffBump (0 : ℝ)) {z : ℂ}
    (hrOut : f.rOut ≤ ‖z‖ ^ 2) {g : EuclideanSpace ℝ (Fin 4)}
    (hg : gaugeTransform (windingPhase m)⁻¹ x z - vacuumField z = g) :
    (x - referenceField f m) z =
      !₂[g 0, g 1, (referenceSection f m z).re * g 2 - (referenceSection f m z).im * g 3,
        (referenceSection f m z).im * g 2 + (referenceSection f m z).re * g 3] := by
  have hsub : x - referenceField f m = gaugeLinearAction (windingPhase m)
      (gaugeTransform (windingPhase m)⁻¹ x - gaugeTransform (windingPhase m)⁻¹ (referenceField f m))
      := by
    rw [gaugeTransform_sub_gaugeTransform, gaugeLinearAction_gaugeLinearAction_inv]
  have hs : referenceSection f m z = windingPhase m z := by
    rw [referenceSection_eq_phase f m hrOut,
      coe_windingPhase m (ne_zero_of_rOut_le_norm_sq f hrOut)]
  rw [hsub, gaugeLinearAction_apply, Pi.sub_apply,
    gaugeTransform_inv_windingPhase_referenceField f m hrOut, hg, hs]

/-- Outside the cutoff disc, the connection coefficients of `x - x_ref` are those of the end
trivialization of `x`, since the end trivialization of the reference field is the vacuum. -/
private theorem sub_referenceField_apply_eq_gaugeTransform_inv_windingPhase_apply
    (f : ContDiffBump (0 : ℝ)) {z : ℂ} (hrOut : f.rOut ≤ ‖z‖ ^ 2) {i : Fin 4}
    (hi : i = 0 ∨ i = 1) :
    (x - referenceField f m) z i = gaugeTransform (windingPhase m)⁻¹ x z i := by
  rw [sub_referenceField_apply_eq f hrOut rfl]
  rcases hi with rfl | rfl <;> simp [vacuumField_apply]

/-- **The connection of an end-normalized vortex.** At a point `z` outside the cutoff disc near
which the section of `x` is `|α|` times the winding phase, where `α (z) ≠ 0` and `∂bar_a α = 0`,
the first connection coefficient of `x` differs from that of the reference field by
`-(1 / 2) ∂_t log |α|²`. Together with `sub_referenceField_apply_one_of_equation_eq_zero`, the
connection of `x` is `a_ref + (i / 2) ⋆ d log |α|²` there. -/
theorem sub_referenceField_apply_zero_of_equation_eq_zero (f : ContDiffBump (0 : ℝ)) {z : ℂ}
    (hrOut : f.rOut ≤ ‖z‖ ^ 2) (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z) (h₁ : equation x z 1 = 0)
    (h₂ : equation x z 2 = 0)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hα : sectionValue x z ≠ 0) :
    (x - referenceField f m) z 0 =
      -(fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z I / 2) := by
  rw [sub_referenceField_apply_eq_gaugeTransform_inv_windingPhase_apply f hrOut (.inl rfl)]
  exact gaugeTransform_inv_windingPhase_apply_zero_of_equation_eq_zero
    (ne_zero_of_rOut_le_norm_sq f hrOut) hp hq h₁ h₂ hphase hα

/-- **The connection of an end-normalized vortex.** At a point `z` outside the cutoff disc near
which the section of `x` is `|α|` times the winding phase, where `α (z) ≠ 0` and `∂bar_a α = 0`,
the second connection coefficient of `x` differs from that of the reference field by
`(1 / 2) ∂_s log |α|²`. -/
theorem sub_referenceField_apply_one_of_equation_eq_zero (f : ContDiffBump (0 : ℝ)) {z : ℂ}
    (hrOut : f.rOut ≤ ‖z‖ ^ 2) (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z) (h₁ : equation x z 1 = 0)
    (h₂ : equation x z 2 = 0)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hα : sectionValue x z ≠ 0) :
    (x - referenceField f m) z 1 =
      fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z 1 / 2 := by
  rw [sub_referenceField_apply_eq_gaugeTransform_inv_windingPhase_apply f hrOut (.inr rfl)]
  exact gaugeTransform_inv_windingPhase_apply_one_of_equation_eq_zero
    (ne_zero_of_rOut_le_norm_sq f hrOut) hp hq h₁ h₂ hphase hα

/-! ### Framed gauge normalization of the end phase -/

/-- **Normalization of the end phase by a smooth framed gauge.** A smooth field whose section
has the degree-`m` end framing `α (z / |z|)^(-m) → 1` is equivalent under the smooth framed gauge
group to a field whose section is `|α|` times the winding phase outside a compact set. -/
theorem exists_framedGaugeGroup_sectionValue_smul_eq (hx : ContDiff ℝ ∞ x)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup, ∀ᶠ z in cocompact ℂ,
      sectionValue (u • x) z = ‖sectionValue (u • x) z‖ * windingPhase m z := by
  have hs := contDiff_sectionValue (contDiff_euclidean.1 hx 2) (contDiff_euclidean.1 hx 3)
  have hconj (z : ℂ) : conj (windingPhase m z : ℂ) * (windingPhase m z : ℂ) = 1 := by
    rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  -- The end-trivialized section `α conj (z / |z|)^m` is smooth off the origin and tends to one.
  have hz₀ : ∀ᶠ z in cocompact ℂ, z ≠ 0 :=
    (tendsto_norm_cocompact_atTop.eventually_gt_atTop 0).mono fun z hz ↦ norm_pos_iff.1 hz
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_mul_eq_norm
    (g := fun z ↦ sectionValue x z * conj (windingPhase m z : ℂ))
    (hz₀.mono fun z hz ↦ hs.contDiffAt.mul
      (conjCLE.contDiff.contDiffAt.comp z (contDiffAt_windingPhase m hz)))
    (hframe.congr' (hz₀.mono fun z hz ↦ by
      dsimp only
      rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, coe_windingPhase m hz]))
  refine ⟨u, hu.mono fun z hz ↦ ?_⟩
  have hnorm : ‖sectionValue x z * conj (windingPhase m z : ℂ)‖ = ‖sectionValue x z‖ := by
    rw [norm_mul, Complex.norm_conj, Circle.norm_coe, mul_one]
  rw [hnorm] at hz
  rw [framedGaugeGroup_smul, sectionValue_gaugeTransform, norm_mul, Circle.norm_coe, one_mul,
    ← hz, mul_assoc, mul_assoc, hconj, mul_one]

end TauCeti.Vortex
