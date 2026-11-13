/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

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
winding phase, so that its end trivialization has a positive real section. For such a vortex with
`|α| → 1` the end-trivialized field tends to the vacuum exponentially at every rate `c < 1 / 2`:
equivalently, the field tends to the reference field,

`‖x(z) - x_ref(z)‖ ≤ K exp (-c |z|)`

(`TauCeti.Vortex.exists_norm_sub_referenceField_le_mul_exp`). In the end trivialization the
section is `|α|`, so its distance to `1` is at most `1 - |α|²`, which decays by
`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp`. The connection is read off from the imaginary
part of the covariant derivative of the real section: `Im (∇_v α') = b'(v) |α|`, and the covariant
derivative decays by `TauCeti.Vortex.exists_norm_covariantDerivative_le_mul_exp`.

Every smooth field with the degree-`m` end framing `α (z / |z|)^(-m) → 1` is equivalent under the
smooth framed gauge group to one normalized at its end
(`TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq`): the smooth framed gauge making
`g = α (z / |z|)^(-m)` positive near infinity (`TauCeti.Vortex.exists_framedGaugeGroup_mul_eq_norm`)
does this, without choosing a logarithm of the phase. Hence every smooth framed vortex has a
framed-gauge representative which converges exponentially to the reference field
(`TauCeti.Vortex.exists_framedGaugeGroup_norm_smul_sub_referenceField_le_mul_exp`).

The first derivatives decay at the same rates. For a vortex normalized at its end, the section of
the end trivialization is the positive function `|α|`, and its covariant derivative is complex
linear because `∂bar_a α = 0`. This determines its connection: outside a disc, the end
trivialization has connection coefficients `(-(1 / 2) ∂_t log |α|², (1 / 2) ∂_s log |α|²)`
(`TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_zero_of_equation_eq_zero`,
`TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_one_of_equation_eq_zero`), and so does
`x - x_ref`, whose section is `(|α| - 1) (z / |z|)^m`. The second derivatives of `log |α|²` decay
(`TauCeti.Vortex.isBigO_iteratedFDeriv_log_normSq`), as do the gradient of `|α|²` and the modulus
defect. Hence outside a compact set the derivatives of both the end trivialization and of
`x - x_ref` are at most `K exp (-c |z|)`
(`TauCeti.Vortex.exists_eventually_norm_fderiv_gaugeTransform_inv_windingPhase_le_mul_exp`,
`TauCeti.Vortex.exists_eventually_norm_fderiv_sub_referenceField_le_mul_exp`). Higher derivatives
are not treated here.

## Main definitions

* `TauCeti.Vortex.windingPhase m`: the winding phase `(z / |z|)^m` as a map `ℂ → Circle`.

## Main results

* `TauCeti.Vortex.gaugeForm_windingPhase`: the logarithmic derivative of the winding phase.
* `TauCeti.Vortex.gaugeTransform_inv_windingPhase_referenceField`: the end trivialization takes
  the reference field to the vacuum outside the cutoff disc.
* `TauCeti.Vortex.exists_norm_sub_referenceField_le_mul_exp`: a vortex normalized at its end
  converges exponentially to the reference field.
* `TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_zero_of_equation_eq_zero`,
  `TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_one_of_equation_eq_zero`: the end
  trivialization of a vortex normalized at its end has connection `(i / 2) ⋆ d log |α|²`.
* `TauCeti.Vortex.sub_referenceField_apply_zero_of_equation_eq_zero`,
  `TauCeti.Vortex.sub_referenceField_apply_one_of_equation_eq_zero`: its connection is
  `a_ref + (i / 2) ⋆ d log |α|²` outside the cutoff disc.
* `TauCeti.Vortex.exists_eventually_norm_fderiv_gaugeTransform_inv_windingPhase_le_mul_exp`,
  `TauCeti.Vortex.exists_eventually_norm_fderiv_sub_referenceField_le_mul_exp`: the first
  derivatives of the end trivialization and of `x - x_ref` decay exponentially.
* `TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq`: framed gauge normalization of the
  end phase.
* `TauCeti.Vortex.exists_framedGaugeGroup_norm_smul_sub_referenceField_le_mul_exp`: every smooth
  framed vortex has a framed-gauge representative converging exponentially to the reference field.

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

/-- If the section of `x` is `|α|` times the winding phase at `z`, then its end
trivialization has the real section `|α|` there. -/
theorem sectionValue_gaugeTransform_inv_windingPhase {z : ℂ}
    (hphase : sectionValue x z = ‖sectionValue x z‖ * windingPhase m z) :
    sectionValue (gaugeTransform (windingPhase m)⁻¹ x) z = ‖sectionValue x z‖ := by
  have h1 : ((windingPhase m z)⁻¹ : Circle) * (windingPhase m z : ℂ) = 1 := by
    rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  rw [sectionValue_gaugeTransform, Pi.inv_apply]
  nth_rw 1 [hphase]
  rw [mul_left_comm, h1, mul_one]

/-- If the section of `x` is `|α|` times the winding phase at `z`, then the first section
coordinate of its end trivialization is `|α| / 2` there. -/
theorem gaugeTransform_inv_windingPhase_apply_two {z : ℂ}
    (hphase : sectionValue x z = ‖sectionValue x z‖ * windingPhase m z) :
    gaugeTransform (windingPhase m)⁻¹ x z 2 = ‖sectionValue x z‖ / 2 := by
  have hsec := sectionValue_gaugeTransform_inv_windingPhase hphase
  rw [sectionValue_apply] at hsec
  have h := congrArg Complex.re hsec
  simp only [mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at h
  linarith

/-- If the section of `x` is `|α|` times the winding phase at `z`, then the second section
coordinate of its end trivialization vanishes there. -/
theorem gaugeTransform_inv_windingPhase_apply_three {z : ℂ}
    (hphase : sectionValue x z = ‖sectionValue x z‖ * windingPhase m z) :
    gaugeTransform (windingPhase m)⁻¹ x z 3 = 0 := by
  have hsec := sectionValue_gaugeTransform_inv_windingPhase hphase
  rw [sectionValue_apply] at hsec
  have h := congrArg Complex.im hsec
  simp only [mul_im, add_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at h
  linarith

/-- **The connection in the end trivialization.** If the section of `x` is `|α|` times the
winding phase near `z ≠ 0`, the connection coefficient `b'(v)` of the end trivialization of `x`
satisfies `|b'(v)| |α| ≤ |∇_v α|`: it is the imaginary part of the covariant derivative of the
real section `|α|`. -/
private theorem abs_mul_norm_le_norm_covariantDerivative {z : ℂ} (hz : z ≠ 0)
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w) (v : ℂ) :
    |gaugeTransform (windingPhase m)⁻¹ x z 0 * v.re +
        gaugeTransform (windingPhase m)⁻¹ x z 1 * v.im| * ‖sectionValue x z‖ ≤
      ‖covariantDerivative x z v‖ := by
  have hu := Circle.differentiableAt_coe_inv (differentiableAt_windingPhase m hz)
  have hsx := differentiableAt_sectionValue hp hq
  have hsy : DifferentiableAt ℝ (sectionValue (gaugeTransform (windingPhase m)⁻¹ x)) z := by
    rw [funext (sectionValue_gaugeTransform _ x)]
    exact hu.mul hsx
  -- The section of the end trivialization is real near `z`, so its derivative is real at `z`.
  have him : (fderiv ℝ (sectionValue (gaugeTransform (windingPhase m)⁻¹ x)) z v).im = 0 := by
    have hconst : (fun w ↦ (sectionValue (gaugeTransform (windingPhase m)⁻¹ x) w).im) =ᶠ[𝓝 z]
        fun _ ↦ (0 : ℝ) := by
      filter_upwards [hphase] with w hw
      rw [sectionValue_gaugeTransform_inv_windingPhase hw, ofReal_im]
    have h := (imCLM.hasFDerivAt.comp z hsy.hasFDerivAt).fderiv
    have h' := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L v) (hconst.fderiv_eq.symm.trans h)
    simpa using h'.symm
  have hcov := covariantDerivative_gaugeTransform hu hp hq v
  rw [covariantDerivative_apply, sectionValue_gaugeTransform_inv_windingPhase hphase.self_of_nhds]
    at hcov
  have hval := congrArg Complex.im hcov
  simp only [add_im, him, mul_im, I_re, I_im, ofReal_re, ofReal_im, one_mul, mul_zero,
    zero_add] at hval
  calc _ = |((((windingPhase m)⁻¹ z : Circle) : ℂ) * covariantDerivative x z v).im| := by
        rw [mul_im, ← hval, abs_mul, abs_norm]
    _ ≤ ‖covariantDerivative x z v‖ := by
        simpa only [norm_mul, Circle.norm_coe, one_mul] using
          abs_im_le_norm ((((windingPhase m)⁻¹ z : Circle) : ℂ) * covariantDerivative x z v)

/-- **The pointwise distance to the reference field.** At a point `z` outside the cutoff disc
near which the section of `x` is `|α|` times the winding phase, with `1 / 2 ≤ |α(z)| ≤ 1`, the
distance from `x` to the reference field is controlled by the covariant derivative and the modulus
defect: `‖x(z) - x_ref(z)‖ ≤ 2 |∇₁ α| + 2 |∇₂ α| + (1 - |α|²) / 2`. -/
private theorem norm_sub_referenceField_le (f : ContDiffBump (0 : ℝ)) {z : ℂ}
    (hrOut : f.rOut ≤ ‖z‖ ^ 2) (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hs_half : 1 / 2 ≤ ‖sectionValue x z‖) (hs_one : ‖sectionValue x z‖ ≤ 1) :
    ‖x z - referenceField f m z‖ ≤ 2 * ‖covariantDerivative x z 1‖ +
      2 * ‖covariantDerivative x z I‖ + (1 - ‖sectionValue x z‖ ^ 2) / 2 := by
  have hz := ne_zero_of_rOut_le_norm_sq f hrOut
  set y := gaugeTransform (windingPhase m)⁻¹ x
  set s := ‖sectionValue x z‖
  -- The section coordinates of the end trivialization are `(|α| / 2, 0)`.
  have hy2 : y z 2 = s / 2 := gaugeTransform_inv_windingPhase_apply_two hphase.self_of_nhds
  have hy3 : y z 3 = 0 := gaugeTransform_inv_windingPhase_apply_three hphase.self_of_nhds
  -- The connection coordinates of the end trivialization.
  have hy0 : |y z 0| ≤ 2 * ‖covariantDerivative x z 1‖ := by
    have h := abs_mul_norm_le_norm_covariantDerivative hz hp hq hphase 1
    simp only [one_re, one_im, mul_one, mul_zero, add_zero] at h
    nlinarith [abs_nonneg (y z 0)]
  have hy1 : |y z 1| ≤ 2 * ‖covariantDerivative x z I‖ := by
    have h := abs_mul_norm_le_norm_covariantDerivative hz hp hq hphase I
    simp only [I_re, I_im, mul_one, mul_zero, zero_add] at h
    nlinarith [abs_nonneg (y z 1)]
  have hy2' : |y z 2 - 1 / 2| ≤ (1 - s ^ 2) / 2 := by
    rw [hy2, abs_of_nonpos (by linarith)]
    nlinarith
  -- The end trivialization is a pointwise isometry taking the reference field to the vacuum.
  have hiso : ‖x z - referenceField f m z‖ = ‖y z - vacuumField z‖ := by
    rw [← gaugeTransform_inv_windingPhase_referenceField f m hrOut, ← Pi.sub_apply y,
      gaugeTransform_sub_gaugeTransform, norm_gaugeLinearAction, Pi.sub_apply]
  have hsq : ‖y z - vacuumField z‖ ^ 2 ≤ (|y z 0| + |y z 1| + |y z 2 - 1 / 2|) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
    simp only [PiLp.sub_apply, vacuumField_apply, hy3]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, sub_zero]
    nlinarith [sq_abs (y z 0), sq_abs (y z 1), sq_abs (y z 2 - 1 / 2),
      mul_nonneg (abs_nonneg (y z 0)) (abs_nonneg (y z 1)),
      mul_nonneg (abs_nonneg (y z 0)) (abs_nonneg (y z 2 - 1 / 2)),
      mul_nonneg (abs_nonneg (y z 1)) (abs_nonneg (y z 2 - 1 / 2))]
  rw [hiso]
  calc ‖y z - vacuumField z‖ ≤ |y z 0| + |y z 1| + |y z 2 - 1 / 2| :=
        (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
    _ ≤ _ := by linarith

/-- **Exponential convergence of an end-normalized vortex to the reference field.** Let `x` be a
plane vortex with `|α| → 1` at infinity whose section is `|α|` times the winding phase
`(z / |z|)^m` outside a compact set. Then for every `c < 1 / 2` the field converges to the
reference field of `A_m^s` at rate `c`: `‖x(z) - x_ref(z)‖ ≤ K exp (-c |z|)`. Equivalently, its
winding-`m` end trivialization converges to the vacuum at that rate. -/
theorem exists_norm_sub_referenceField_le_mul_exp
    (hb₁ : Continuous (fun w ↦ x w 0)) (hb₂ : Continuous (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ z, ‖x z - referenceField f m z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K₁, hK₁⟩ := exists_norm_covariantDerivative_le_mul_exp hb₁ hp hq hsol hlim hc
  obtain ⟨K₂, hK₂⟩ := exists_one_sub_normSq_le_mul_exp hp hq hsol hlim hc
  obtain ⟨R, -, hR⟩ :=
    hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸ hphase)
  have hcont : Continuous fun z ↦ ‖x z - referenceField f m z‖ := by
    have hx : Continuous x := by
      refine contDiff_zero.1 (contDiff_euclidean.2 fun i ↦ contDiff_zero.2 ?_)
      fin_cases i
      exacts [hb₁, hb₂, hp.continuous, hq.continuous]
    exact (hx.sub (contDiff_referenceField f m).continuous).norm
  refine exists_forall_le_mul_exp_of_eventually_le hcont (K := 4 * K₁ + K₂ / 2) ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (max R (max 1 f.rOut)),
    hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 4 < 1))] with z hzR hz4
  have hR' : R < ‖z‖ := (le_max_left _ _).trans_lt hzR
  have hrOut := rOut_le_norm_sq f ((le_max_right _ _).trans_lt hzR)
  have hnhds : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hR')
      fun w hw ↦ hR (show R ≤ ‖w‖ from le_of_lt hw)
  have hs2 := sq_norm_sectionValue x z
  have hs0 : 0 ≤ ‖sectionValue x z‖ := norm_nonneg _
  have h := norm_sub_referenceField_le f hrOut (hp.differentiable (by norm_num) z)
    (hq.differentiable (by norm_num) z) hnhds (by nlinarith)
    (by nlinarith [normSq_le_one_of_tendsto hp hq hsol hlim z])
  have h1 := hK₁ z 1
  have hI := hK₁ z I
  rw [norm_one, mul_one] at h1
  rw [norm_I, mul_one] at hI
  rw [hs2] at h
  nlinarith [hK₂ z]

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
  -- `|α| = √|α|²` is differentiable at `z`, and `log |α|² = 2 log |α|`.
  have hNz : 0 < N z := norm_pos_iff.mpr hα
  have hNd : DifferentiableAt ℝ N z := by
    have hs : DifferentiableAt ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z := by fun_prop
    have h : (fun w ↦ Real.sqrt (4 * (x w 2 ^ 2 + x w 3 ^ 2))) = N := funext fun w ↦ by
      rw [← sq_norm_sectionValue, Real.sqrt_sq (norm_nonneg _)]
    rw [← h]
    exact hs.sqrt (by rw [← sq_norm_sectionValue]; positivity)
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
    hphase.mono fun w hw ↦ sectionValue_gaugeTransform_inv_windingPhase hw
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

/-- Outside the cutoff disc, the connection coefficients of `x - x_ref` are those of the end
trivialization of `x`, since the end trivialization of the reference field is the vacuum. -/
private theorem sub_referenceField_apply_eq_gaugeTransform_inv_windingPhase_apply
    (f : ContDiffBump (0 : ℝ)) {z : ℂ} (hrOut : f.rOut ≤ ‖z‖ ^ 2) {i : Fin 4}
    (hi : i = 0 ∨ i = 1) :
    (x - referenceField f m) z i = gaugeTransform (windingPhase m)⁻¹ x z i := by
  have h := congrFun (gaugeTransform_sub_gaugeTransform (windingPhase m)⁻¹ x (referenceField f m))
    z
  rw [Pi.sub_apply, gaugeTransform_inv_windingPhase_referenceField f m hrOut,
    gaugeLinearAction_apply] at h
  have hi' := congrArg (· i) h
  rcases hi with rfl | rfl <;> simpa [vacuumField_apply] using hi'.symm

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

/-! ### Exponential decay of the first derivatives -/

/-- Outside a disc beyond which the section of a vortex `x` is `|α|` times the winding phase and
nonzero, each connection coefficient of the end trivialization of `x` is differentiable, with
derivative at most half the second derivative of `log |α|²`. -/
private theorem norm_fderiv_gaugeTransform_inv_windingPhase_apply_le
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) {R : ℝ} (hR : 0 ≤ R)
    (hphase : ∀ w : ℂ, R < ‖w‖ → sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hα : ∀ w : ℂ, R < ‖w‖ → sectionValue x w ≠ 0) {z : ℂ} (hz : R < ‖z‖) {i : Fin 4}
    (hi : i = 0 ∨ i = 1) :
    DifferentiableAt ℝ (fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w i) z ∧
      ‖fderiv ℝ (fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w i) z‖ ≤
        ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)))) z‖ / 2 := by
  have hU : ∀ᶠ w in 𝓝 z, R < ‖w‖ := (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  have hw₀ : ∀ w : ℂ, R < ‖w‖ → w ≠ 0 := fun w hw ↦ norm_pos_iff.mp (hR.trans_lt hw)
  have hphase' : ∀ w : ℂ, R < ‖w‖ →
      ∀ᶠ v in 𝓝 w, sectionValue x v = ‖sectionValue x v‖ * windingPhase m v := fun w hw ↦
    Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hw)
      fun v hv ↦ hphase v hv
  have hℓcd : ContDiffAt ℝ 2 (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z :=
    (contDiff_normSq hp hq).contDiffAt.log (by
      rw [← sq_norm_sectionValue]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hα z hz)))
  -- Near `z` the coefficient is `a ∂_v ℓ` with `|a| = 1 / 2` and `|v| = 1`.
  obtain ⟨v, a, hv, ha, hcoeff⟩ : ∃ (v : ℂ) (a : ℝ), ‖v‖ = 1 ∧ |a| = 1 / 2 ∧
      (fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w i) =ᶠ[𝓝 z]
        fun w ↦ a * fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) w v := by
    rcases hi with rfl | rfl
    · refine ⟨I, -1 / 2, norm_I, by norm_num [abs_of_neg], hU.mono fun w hw ↦ ?_⟩
      dsimp only
      rw [gaugeTransform_inv_windingPhase_apply_zero_of_equation_eq_zero (hw₀ w hw)
        (hp.differentiable (by norm_num) w) (hq.differentiable (by norm_num) w)
        (by simp [hsol w]) (by simp [hsol w]) (hphase' w hw) (hα w hw)]
      ring
    · refine ⟨1, 1 / 2, norm_one, by norm_num, hU.mono fun w hw ↦ ?_⟩
      dsimp only
      rw [gaugeTransform_inv_windingPhase_apply_one_of_equation_eq_zero (hw₀ w hw)
        (hp.differentiable (by norm_num) w) (hq.differentiable (by norm_num) w)
        (by simp [hsol w]) (by simp [hsol w]) (hphase' w hw) (hα w hw)]
      ring
  have hd := (hℓcd.hasFDerivAt_fderiv_apply le_rfl v).const_mul a
  refine ⟨(hd.differentiableAt).congr_of_eventuallyEq hcoeff, ?_⟩
  rw [hcoeff.fderiv_eq, hd.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  have h := (fderiv ℝ (fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)))) z).le_opNorm₂ u v
  rw [hv, mul_one] at h
  simp only [smul_apply, ContinuousLinearMap.flip_apply, smul_eq_mul,
    norm_mul, Real.norm_eq_abs, ha]
  rw [← Real.norm_eq_abs]
  linarith

/-- Beyond some radius `R ≥ 1`, the section of a vortex normalized at its end with `|α| → 1` is
`|α|` times the winding phase and satisfies `|α|² ≥ 1 / 4`. -/
private theorem exists_radius_sectionValue_eq_and_quarter_le
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z) :
    ∃ R, 1 ≤ R ∧
      (∀ w : ℂ, R < ‖w‖ → sectionValue x w = ‖sectionValue x w‖ * windingPhase m w) ∧
      ∀ w : ℂ, R < ‖w‖ → 1 / 4 ≤ 4 * (x w 2 ^ 2 + x w 3 ^ 2) := by
  obtain ⟨R₀, -, hR₀⟩ :=
    hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸ hphase)
  obtain ⟨R₂, -, hR₂⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸
      hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 4 < 1)))
  refine ⟨max (max R₀ R₂) 1, le_max_right _ _, fun w hw ↦ hR₀ ?_, fun w hw ↦ (hR₂ ?_).le⟩
  · exact ((le_max_left R₀ R₂).trans (le_max_left _ _)).trans hw.le
  · exact ((le_max_right R₀ R₂).trans (le_max_left _ _)).trans hw.le

/-- The second derivatives of `log |α|²` decay at every rate `c < 1 / 2`. -/
private theorem exists_eventually_norm_fderiv_fderiv_log_normSq_le_mul_exp
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)))) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK⟩ := (isBigO_iteratedFDeriv_log_normSq hp hq hsol hlim hc 2).bound
  refine ⟨K, hK.mono fun z hz ↦ ?_⟩
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  rwa [Real.norm_of_nonneg (Real.exp_pos _).le] at hz

/-- **The pointwise derivative of the end trivialization.** Beyond a radius `R ≥ 0` outside which
the section of a vortex `x` is `|α|` times the winding phase and `|α|² ≥ 1 / 4`, the derivative of
the end trivialization of `x` is bounded by the second derivative of `log |α|²` (the derivative of
its connection) and the gradient of `|α|²` (the derivative of its section `|α|`). -/
private theorem norm_fderiv_gaugeTransform_inv_windingPhase_le
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) {R : ℝ} (hR : 0 ≤ R)
    (hphase : ∀ w : ℂ, R < ‖w‖ → sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hquarter : ∀ w : ℂ, R < ‖w‖ → 1 / 4 ≤ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) {z : ℂ} (hz : R < ‖z‖) :
    ‖fderiv ℝ (gaugeTransform (windingPhase m)⁻¹ x) z‖ ≤
      ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)))) z‖ +
        ‖fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z‖ := by
  set y := gaugeTransform (windingPhase m)⁻¹ x
  set s : ℂ → ℝ := fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2) with hs_def
  have hU : ∀ᶠ w in 𝓝 z, R < ‖w‖ := (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  have hspos : ∀ w : ℂ, R < ‖w‖ → 0 < s w := fun w hw ↦
    (by norm_num : (0 : ℝ) < 1 / 4).trans_le (hquarter w hw)
  have hα : ∀ w : ℂ, R < ‖w‖ → sectionValue x w ≠ 0 := fun w hw h ↦ by
    have := sq_norm_sectionValue x w
    rw [h, norm_zero] at this
    linarith [hspos w hw]
  obtain ⟨hd0, hb0⟩ := norm_fderiv_gaugeTransform_inv_windingPhase_apply_le (m := m) hp hq hsol hR
    hphase hα hz (i := 0) (.inl rfl)
  obtain ⟨hd1, hb1⟩ := norm_fderiv_gaugeTransform_inv_windingPhase_apply_le (m := m) hp hq hsol hR
    hphase hα hz (i := 1) (.inr rfl)
  -- Near `z` the section of `y` is `|α| = √|α|²`, with section coordinates `(|α| / 2, 0)`.
  have hnorm : ∀ w, ‖sectionValue x w‖ = Real.sqrt (s w) := fun w ↦ by
    simp only [hs_def]
    rw [← sq_norm_sectionValue, Real.sqrt_sq (norm_nonneg _)]
  have hN : HasFDerivAt (fun w ↦ Real.sqrt (s w))
      ((1 / (2 * Real.sqrt (s z))) • fderiv ℝ s z) z :=
    (((contDiff_normSq hp hq).differentiable (by norm_num)) z).hasFDerivAt.sqrt
      (hspos z hz).ne'
  have hσ : sectionValue y =ᶠ[𝓝 z] fun w ↦ ofRealCLM (Real.sqrt (s w)) :=
    hU.mono fun w hw ↦ by
      rw [sectionValue_gaugeTransform_inv_windingPhase (hphase w hw), hnorm]
      rfl
  have h2 : (fun w ↦ y w 2) =ᶠ[𝓝 z] fun w ↦ Real.sqrt (s w) * (1 / 2) := hU.mono fun w hw ↦
    (gaugeTransform_inv_windingPhase_apply_two (hphase w hw)).trans (by rw [hnorm]; ring)
  have h3 : (fun w ↦ y w 3) =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := hU.mono fun w hw ↦
    gaugeTransform_inv_windingPhase_apply_three (hphase w hw)
  have hyd : DifferentiableAt ℝ y z := by
    refine differentiableAt_euclidean.mpr fun i ↦ ?_
    fin_cases i
    exacts [hd0, hd1, (hN.differentiableAt.mul_const _).congr_of_eventuallyEq h2,
      (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq h3]
  -- `‖D |α|‖ ≤ ‖D |α|²‖`, since `|α| ≥ 1 / 2`.
  have hsqrt : 1 / 2 ≤ Real.sqrt (s z) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (hquarter z hz)
  have hσd : ‖fderiv ℝ (sectionValue y) z‖ ≤ ‖fderiv ℝ s z‖ := by
    have hd : HasFDerivAt (fun w ↦ ofRealCLM (Real.sqrt (s w)))
        (ofRealCLM.comp ((1 / (2 * Real.sqrt (s z))) • fderiv ℝ s z)) z :=
      ofRealCLM.hasFDerivAt.comp z hN
    rw [hσ.fderiv_eq, hd.fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ofRealCLM_norm, one_mul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [div_le_one (by positivity)]
    linarith
  have h := norm_fderiv_le_add_norm_fderiv_sectionValue hyd
  linarith [norm_nonneg (fderiv ℝ s z)]

/-- **Exponential decay of the first derivatives of the end trivialization.** Let `x` be a plane
vortex with `|α| → 1` at infinity whose section is `|α|` times the winding phase `(z / |z|)^m`
outside a compact set. Then for every `c < 1 / 2` the derivative of its winding-`m` end
trivialization decays at rate `c` outside a compact set. -/
theorem exists_eventually_norm_fderiv_gaugeTransform_inv_windingPhase_le_mul_exp
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖fderiv ℝ (gaugeTransform (windingPhase m)⁻¹ x) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K₁, hK₁⟩ :=
    exists_eventually_norm_fderiv_fderiv_log_normSq_le_mul_exp hp hq hsol hlim hc
  obtain ⟨K₂, hK₂⟩ := exists_norm_fderiv_normSq_le_mul_exp hp hq hsol hlim hc
  obtain ⟨R, hR, hphR, hqR⟩ := exists_radius_sectionValue_eq_and_quarter_le hlim hphase
  refine ⟨K₁ + K₂, ?_⟩
  filter_upwards [hK₁, tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz₁ hzR
  have h := norm_fderiv_gaugeTransform_inv_windingPhase_le hp hq hsol (by linarith) hphR hqR hzR
  linarith [hK₂ z]

/-- **The pointwise derivative of the distance to the reference field.** Beyond a radius
`R ≥ max 1 rOut` outside which the section of a vortex `x` is `|α|` times the winding phase and
`|α|² ≥ 1 / 4`, the derivative of `x - x_ref` is bounded by the second derivative of `log |α|²`
(the derivative of the connection), the gradient of `|α|²` and the modulus defect (the derivative of
the section `(|α| - 1) (z / |z|)^m` of `x - x_ref`). -/
private theorem norm_fderiv_sub_referenceField_le
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) (f : ContDiffBump (0 : ℝ)) {R : ℝ} (hR : max 1 f.rOut ≤ R)
    (hphase : ∀ w : ℂ, R < ‖w‖ → sectionValue x w = ‖sectionValue x w‖ * windingPhase m w)
    (hquarter : ∀ w : ℂ, R < ‖w‖ → 1 / 4 ≤ 4 * (x w 2 ^ 2 + x w 3 ^ 2))
    (hone : ∀ w : ℂ, 4 * (x w 2 ^ 2 + x w 3 ^ 2) ≤ 1) {z : ℂ} (hz : R < ‖z‖) :
    ‖fderiv ℝ (x - referenceField f m) z‖ ≤
      ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)))) z‖ +
        ‖fderiv ℝ (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) z‖ +
        m * (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) := by
  set F := x - referenceField f m with hF_def
  set s : ℂ → ℝ := fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2) with hs_def
  have hR₁ : 1 ≤ R := (le_max_left _ _).trans hR
  have hU : ∀ᶠ w in 𝓝 z, R < ‖w‖ := (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  have hrOut : ∀ w : ℂ, R < ‖w‖ → f.rOut ≤ ‖w‖ ^ 2 := fun w hw ↦ rOut_le_norm_sq f (hR.trans_lt hw)
  have hz₀ : z ≠ 0 := norm_pos_iff.mp ((zero_lt_one.trans_le hR₁).trans hz)
  have hspos : ∀ w : ℂ, R < ‖w‖ → 0 < s w := fun w hw ↦
    (by norm_num : (0 : ℝ) < 1 / 4).trans_le (hquarter w hw)
  have hα : ∀ w : ℂ, R < ‖w‖ → sectionValue x w ≠ 0 := fun w hw h ↦ by
    have := sq_norm_sectionValue x w
    rw [h, norm_zero] at this
    linarith [hspos w hw]
  -- The connection coefficients of `F` are those of the end trivialization near `z`.
  have hconn (i : Fin 4) (hi : i = 0 ∨ i = 1) :
      ‖fderiv ℝ (fun w ↦ F w i) z‖ ≤
        ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.log (s w))) z‖ / 2 := by
    have heq : (fun w ↦ F w i) =ᶠ[𝓝 z] fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w i :=
      hU.mono fun w hw ↦
        sub_referenceField_apply_eq_gaugeTransform_inv_windingPhase_apply f (hrOut w hw) hi
    rw [heq.fderiv_eq]
    exact (norm_fderiv_gaugeTransform_inv_windingPhase_apply_le hp hq hsol (by linarith) hphase
      hα hz hi).2
  -- The section of `F` is `(|α| - 1)` times the winding phase near `z`.
  have hσ : sectionValue F =ᶠ[𝓝 z]
      (fun w ↦ ofRealCLM (Real.sqrt (s w) - 1)) * fun w ↦ (windingPhase m w : ℂ) :=
    hU.mono fun w hw ↦ by
      have hw₀ : w ≠ 0 := norm_pos_iff.mp ((zero_lt_one.trans_le hR₁).trans hw)
      simp only [hF_def, sectionValue_sub, sectionValue_referenceField,
        referenceSection_eq_phase f m (hrOut w hw), ← coe_windingPhase m hw₀, hs_def,
        Pi.mul_apply, ofRealCLM_apply]
      rw [← sq_norm_sectionValue, Real.sqrt_sq (norm_nonneg _)]
      nth_rw 1 [hphase w hw]
      push_cast
      ring
  have hN : HasFDerivAt (fun w ↦ Real.sqrt (s w))
      ((1 / (2 * Real.sqrt (s z))) • fderiv ℝ s z) z :=
    (((contDiff_normSq hp hq).differentiable (by norm_num)) z).hasFDerivAt.sqrt
      (hspos z hz).ne'
  have hW := (differentiableAt_windingPhase m hz₀).hasFDerivAt
  have hprod : HasFDerivAt ((fun w ↦ ofRealCLM (Real.sqrt (s w) - 1)) *
      fun w ↦ (windingPhase m w : ℂ)) _ z := (ofRealCLM.hasFDerivAt.comp z (hN.sub_const 1)).mul hW
  -- Bounds for the two factors.
  have hsqrt : 1 / 2 ≤ Real.sqrt (s z) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (hquarter z hz)
  have hsqrt1 : Real.sqrt (s z) ≤ 1 := Real.sqrt_le_one.mpr (hone z)
  have hdefect : |Real.sqrt (s z) - 1| ≤ 1 - s z := by
    rw [abs_of_nonpos (by linarith)]
    have := Real.sq_sqrt (hspos z hz).le
    nlinarith
  have hdN : ‖(1 / (2 * Real.sqrt (s z))) • fderiv ℝ s z‖ ≤ ‖fderiv ℝ s z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [div_le_one (by positivity)]
    linarith
  have hdW : ‖fderiv ℝ (fun w ↦ (windingPhase m w : ℂ)) z‖ ≤ m :=
    (norm_fderiv_windingPhase_le m hz₀).trans
      (div_le_self (Nat.cast_nonneg m) (hR₁.trans hz.le))
  have hσd : ‖fderiv ℝ (sectionValue F) z‖ ≤ ‖fderiv ℝ s z‖ + m * (1 - s z) := by
    rw [hσ.fderiv_eq, hprod.fderiv]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Circle.norm_coe, one_mul]
    simp only [Function.comp_apply, ofRealCLM_apply, norm_real, Real.norm_eq_abs]
    have h1 := ContinuousLinearMap.opNorm_comp_le ofRealCLM
      ((1 / (2 * Real.sqrt (s z))) • fderiv ℝ s z)
    rw [ofRealCLM_norm, one_mul] at h1
    have h2 : |Real.sqrt (s z) - 1| * ‖fderiv ℝ (fun w ↦ (windingPhase m w : ℂ)) z‖ ≤
        (1 - s z) * m :=
      mul_le_mul hdefect hdW (norm_nonneg _) (by linarith [hone z])
    linarith
  -- Assemble the connection and the section.
  have hFd : DifferentiableAt ℝ F z := by
    have hc := differentiableAt_connection_of_equation hp.contDiffAt hq.contDiffAt
      (fun h ↦ (hspos z hz).ne' (by simp only [hs_def]; rw [h, mul_zero]))
      (Eventually.of_forall fun w ↦ ⟨by simp [hsol w], by simp [hsol w]⟩)
    refine (differentiableAt_euclidean.mpr fun i ↦ ?_).sub
      ((contDiff_referenceField f m).differentiable (by simp) z)
    fin_cases i
    exacts [hc.1, hc.2, hp.differentiable (by norm_num) z, hq.differentiable (by norm_num) z]
  have h := norm_fderiv_le_add_norm_fderiv_sectionValue hFd
  have hs₁ : s z ≤ 1 := hone z
  have hm : 0 ≤ (m : ℝ) * (1 - s z) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  calc ‖fderiv ℝ F z‖ ≤ ‖fderiv ℝ (fderiv ℝ (fun w ↦ Real.log (s w))) z‖ + ‖fderiv ℝ s z‖ +
        m * (1 - s z) := by
        linarith [hconn 0 (.inl rfl), hconn 1 (.inr rfl), norm_nonneg (fderiv ℝ s z)]
    _ = _ := rfl

/-- **Exponential decay of the first derivatives of an end-normalized vortex.** Let `x` be a plane
vortex with `|α| → 1` at infinity whose section is `|α|` times the winding phase `(z / |z|)^m`
outside a compact set. Then for every `c < 1 / 2` the derivative of `x - x_ref` decays at rate
`c` outside a compact set: `‖D (x - x_ref) (z)‖ ≤ K exp (-c |z|)`. -/
theorem exists_eventually_norm_fderiv_sub_referenceField_le_mul_exp
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ᶠ z in cocompact ℂ,
      ‖fderiv ℝ (x - referenceField f m) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K₁, hK₁⟩ :=
    exists_eventually_norm_fderiv_fderiv_log_normSq_le_mul_exp hp hq hsol hlim hc
  obtain ⟨K₂, hK₂⟩ := exists_norm_fderiv_normSq_le_mul_exp hp hq hsol hlim hc
  obtain ⟨K₃, hK₃⟩ := exists_one_sub_normSq_le_mul_exp hp hq hsol hlim hc
  obtain ⟨R₀, -, hphR, hqR⟩ := exists_radius_sectionValue_eq_and_quarter_le hlim hphase
  set R := max R₀ (max 1 f.rOut)
  refine ⟨K₁ + K₂ + m * K₃, ?_⟩
  filter_upwards [hK₁, tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz₁ hzR
  have h := norm_fderiv_sub_referenceField_le hp hq hsol f (le_max_right _ _)
    (fun w hw ↦ hphR w ((le_max_left _ _).trans_lt hw))
    (fun w hw ↦ hqR w ((le_max_left _ _).trans_lt hw))
    (normSq_le_one_of_tendsto hp hq hsol hlim) hzR
  have h₃ := mul_le_mul_of_nonneg_left (hK₃ z) (Nat.cast_nonneg (α := ℝ) m)
  calc ‖fderiv ℝ (x - referenceField f m) z‖ ≤ _ := h
    _ ≤ K₁ * Real.exp (-(c * ‖z‖)) + K₂ * Real.exp (-(c * ‖z‖)) +
        m * (K₃ * Real.exp (-(c * ‖z‖))) := by linarith [hK₂ z]
    _ = (K₁ + K₂ + m * K₃) * Real.exp (-(c * ‖z‖)) := by ring

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

/-- **A framed representative converging exponentially to the reference field.** Every smooth
plane vortex with the degree-`m` end framing `α (z / |z|)^(-m) → 1` has a smooth framed gauge
transform whose section is `|α|` times the winding phase outside a compact set and which
converges to the reference field of `A_m^s` at every rate `c < 1 / 2`. -/
theorem exists_framedGaugeGroup_norm_smul_sub_referenceField_le_mul_exp (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (f : ContDiffBump (0 : ℝ)) :
    ∃ u : framedGaugeGroup,
      (∀ᶠ z in cocompact ℂ,
        sectionValue (u • x) z = ‖sectionValue (u • x) z‖ * windingPhase m z) ∧
      ∀ c < 1 / 2, ∃ K, ∀ z, ‖(u • x) z - referenceField f m z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_sectionValue_smul_eq hx hframe
  refine ⟨u, hu, fun c hc ↦ ?_⟩
  have huc := ((mem_framedGaugeGroup _).1 u.property).1
  have hy : ContDiff ℝ ∞ (u • x) := contDiff_gaugeTransform huc hx
  have hcd (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ (u • x) z i) := contDiff_euclidean.1 hy i
  have hsol' (z : ℂ) : equation (u • x) z = 0 :=
    (equation_gaugeTransform_eq_zero_iff ((huc.of_le (by norm_cast)).contDiffAt)
      fun i ↦ (contDiff_euclidean.1 hx i).differentiable (by simp) z).2 (hsol z)
  have hlim : Tendsto (fun z ↦ 4 * ((u • x) z 2 ^ 2 + (u • x) z 3 ^ 2)) (cocompact ℂ) (𝓝 1) := by
    refine (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe).congr fun z ↦ ?_
    rw [← sq_norm_sectionValue, ← sq_norm_sectionValue, framedGaugeGroup_smul,
      sectionValue_gaugeTransform, norm_mul, Circle.norm_coe, one_mul]
  exact exists_norm_sub_referenceField_le_mul_exp (hcd 0).continuous (hcd 1).continuous
    ((hcd 2).of_le (by norm_cast)) ((hcd 3).of_le (by norm_cast)) hsol' hlim hu f hc

end TauCeti.Vortex
