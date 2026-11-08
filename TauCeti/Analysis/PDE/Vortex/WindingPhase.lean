/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
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
(`TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq`). More generally, a function `g`
that is smooth near infinity and tends to one is made positive near infinity by a smooth framed
gauge (`TauCeti.Vortex.exists_framedGaugeGroup_mul_eq_norm`); here `g = α (z / |z|)^(-m)`. The
gauge is `v / |v|` for `v = 1 + χ (conj g - 1)`, with `χ` a cutoff equal to one outside a large
disc, so no logarithm of the phase is chosen. Hence every smooth
framed vortex has a framed-gauge representative which converges exponentially to the reference
field (`TauCeti.Vortex.exists_framedGaugeGroup_norm_smul_sub_referenceField_le_mul_exp`). This is
the zeroth-order decay of the fields in the end trivialization; decay of their derivatives is not
treated here.

## Main definitions

* `TauCeti.Vortex.windingPhase m`: the winding phase `(z / |z|)^m` as a map `ℂ → Circle`.

## Main results

* `TauCeti.Vortex.gaugeForm_windingPhase`: the logarithmic derivative of the winding phase.
* `TauCeti.Vortex.gaugeTransform_inv_windingPhase_referenceField`: the end trivialization takes
  the reference field to the vacuum outside the cutoff disc.
* `TauCeti.Vortex.exists_norm_sub_referenceField_le_mul_exp`: a vortex normalized at its end
  converges exponentially to the reference field.
* `TauCeti.Vortex.exists_framedGaugeGroup_mul_eq_norm`: a smooth framed gauge making a function
  that tends to one positive near infinity.
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
  have hg : ContDiff ℝ n fun θ : ℝ ↦ (Circle.exp (m * θ) : ℂ) := by
    simp only [Circle.coe_exp]
    exact ((ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const).cexp
  have hper : Function.Periodic (fun θ : ℝ ↦ (Circle.exp (m * θ) : ℂ)) (2 * Real.pi) := by
    intro θ
    simp only [Circle.exp_natCast_mul, Circle.exp_add_two_pi]
  exact hg.contDiffAt_comp_arg hper hz

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
    rw [windingPhase_eq_mul_exp m hz hw]
    rfl
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

/-! ### The end trivialization of the reference field -/

/-- **The end trivialization of the reference field is the vacuum.** Outside the cutoff disc,
the gauge transformation by the inverse winding phase takes the reference field
`(-i m dθ, (z / |z|)^m)` to the vacuum `(0, 1)`. -/
theorem gaugeTransform_inv_windingPhase_referenceField (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    {z : ℂ} (hz : f.rOut ≤ ‖z‖ ^ 2) :
    gaugeTransform (windingPhase m)⁻¹ (referenceField f m) z = vacuumField z := by
  have hz₀ : z ≠ 0 := by
    rintro rfl
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hz
    exact (f.rOut_pos.trans_le hz).false
  have hn := Circle.re_sq_add_im_sq (windingPhase m z)
  have hsec : referenceSection f m z = windingPhase m z := by
    rw [referenceSection_eq_phase f m hz, coe_windingPhase m hz₀]
  have hform := gaugeForm_inv (differentiableAt_windingPhase m hz₀)
  rw [gaugeTransform_apply, referenceField_apply, hsec, vacuumField_apply]
  ext i
  fin_cases i <;>
    simp [referenceConnection_eq_angular f m hz, hform, gaugeForm_windingPhase m hz₀]
  · linear_combination hn / 2
  · ring

/-! ### Exponential convergence to the reference field -/

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}

/-- If the section of `x` is `|α|` times the winding phase near `z`, then its end
trivialization has the real section `|α|` there. -/
private theorem sectionValue_gaugeTransform_inv_windingPhase {z : ℂ}
    (hphase : sectionValue x z = ‖sectionValue x z‖ * windingPhase m z) :
    sectionValue (gaugeTransform (windingPhase m)⁻¹ x) z = ‖sectionValue x z‖ := by
  have h1 : ((windingPhase m z)⁻¹ : Circle) * (windingPhase m z : ℂ) = 1 := by
    rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  rw [sectionValue_gaugeTransform, Pi.inv_apply]
  nth_rw 1 [hphase]
  rw [mul_left_comm, h1, mul_one]

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
  have hu : DifferentiableAt ℝ (fun w ↦ (((windingPhase m)⁻¹ w : Circle) : ℂ)) z := by
    simpa only [Pi.inv_apply, Circle.coe_inv_eq_conj, Function.comp_def,
      Complex.conjCLE_apply] using
      conjCLE.differentiableAt.comp z (differentiableAt_windingPhase m hz)
  have hsx : DifferentiableAt ℝ (sectionValue x) z := by
    rw [funext (sectionValue_apply x)]
    exact (differentiableAt_const (2 : ℂ)).mul
      ((ofRealCLM.differentiableAt.comp z hp).add
        ((ofRealCLM.differentiableAt.comp z hq).mul_const I))
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
  have hz : z ≠ 0 := by
    rintro rfl
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hrOut
    exact (f.rOut_pos.trans_le hrOut).false
  set y := gaugeTransform (windingPhase m)⁻¹ x
  set s := ‖sectionValue x z‖
  -- The section coordinates of the end trivialization are `(|α| / 2, 0)`.
  have hsec : 2 * ((y z 2 : ℂ) + (y z 3 : ℂ) * I) = (s : ℂ) := by
    rw [← sectionValue_apply]
    exact sectionValue_gaugeTransform_inv_windingPhase hphase.self_of_nhds
  have hy2 : y z 2 = s / 2 := by
    have := congrArg Complex.re hsec
    simp only [mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at this
    linarith
  have hy3 : y z 3 = 0 := by
    have := congrArg Complex.im hsec
    simp only [mul_im, add_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at this
    linarith
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
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ z, ‖x z - referenceField f m z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K₁, hK₁⟩ := exists_norm_covariantDerivative_le_mul_exp hb₁ hb₂ hp hq hsol hlim hc
  obtain ⟨K₂, hK₂⟩ := exists_one_sub_normSq_le_mul_exp hb₁ hb₂ hp hq hsol hlim hc
  obtain ⟨R, -, hR⟩ :=
    hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸ hphase)
  have hcont : Continuous fun z ↦ ‖x z - referenceField f m z‖ := by
    have hx : Continuous x := by
      refine contDiff_zero.1 (contDiff_euclidean.2 fun i ↦ contDiff_zero.2 ?_)
      fin_cases i
      exacts [hb₁.continuous, hb₂.continuous, hp.continuous, hq.continuous]
    exact (hx.sub (contDiff_referenceField f m).continuous).norm
  refine exists_forall_le_mul_exp_of_eventually_le hcont (K := 4 * K₁ + K₂ / 2) ?_
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (max R (max 1 f.rOut)),
    hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 4 < 1))] with z hzR hz4
  have hR' : R < ‖z‖ := (le_max_left _ _).trans_lt hzR
  have hrOut : f.rOut ≤ ‖z‖ ^ 2 := by
    have h1 : 1 < ‖z‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hzR
    have : f.rOut < ‖z‖ := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hzR
    nlinarith
  have hnhds : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hR')
      fun w hw ↦ hR (show R ≤ ‖w‖ from le_of_lt hw)
  have hs2 := sq_norm_sectionValue x z
  have hs0 : 0 ≤ ‖sectionValue x z‖ := norm_nonneg _
  have h := norm_sub_referenceField_le f hrOut (hp.differentiable (by norm_num) z)
    (hq.differentiable (by norm_num) z) hnhds (by nlinarith)
    (by nlinarith [normSq_le_one_of_tendsto hb₁ hb₂ hp hq hsol hlim z])
  have h1 := hK₁ z 1
  have hI := hK₁ z I
  rw [norm_one, mul_one] at h1
  rw [norm_I, mul_one] at hI
  rw [hs2] at h
  nlinarith [hK₂ z]

/-! ### Framed gauge normalization of the end phase -/

/-- **A framed gauge making a function positive near infinity.** If `g : ℂ → ℂ` is smooth outside
a compact set and tends to one at infinity, then some smooth framed gauge `u` satisfies
`u g = |g|` outside a compact set. -/
theorem exists_framedGaugeGroup_mul_eq_norm {g : ℂ → ℂ}
    (hg : ∀ᶠ z in cocompact ℂ, ContDiffAt ℝ ∞ g z) (hgt : Tendsto g (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup, ∀ᶠ z in cocompact ℂ, ((u : ℂ → Circle) z : ℂ) * g z = ‖g z‖ := by
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸
      hg.and (hgt.eventually (Metric.ball_mem_nhds 1 one_half_pos)))
  set R := max R₀ 0
  have hgR {z : ℂ} (hz : R < ‖z‖) : ContDiffAt ℝ ∞ g z ∧ 1 / 2 < (g z).re := by
    obtain ⟨hc, h⟩ := hR₀ (show R₀ ≤ ‖z‖ from (le_max_left _ _).trans hz.le)
    rw [dist_eq_norm] at h
    have := abs_re_le_norm (g z - 1)
    rw [sub_re, one_re] at this
    exact ⟨hc, by linarith [abs_lt.1 (this.trans_lt h)]⟩
  -- A cutoff `χ` vanishing on the disc of radius `R + 1` and equal to one outside radius `R + 2`.
  let b : ContDiffBump (0 : ℂ) := ⟨R + 1, R + 2, by positivity, by linarith⟩
  set χ : ℂ → ℝ := fun z ↦ 1 - b z
  have hχ0 {z : ℂ} (hz : ‖z‖ ≤ R + 1) : χ z = 0 := by
    simp only [χ, b.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hz), sub_self]
  have hχ1 {z : ℂ} (hz : R + 2 ≤ ‖z‖) : χ z = 1 := by
    simp only [χ, b.zero_of_le_dist (by rwa [dist_zero_right]), sub_zero]
  -- The unnormalized gauge `v = 1 + χ (conj g - 1)` is smooth with positive real part.
  set v : ℂ → ℂ := fun z ↦ 1 + (χ z : ℂ) * (conj (g z) - 1)
  have hv_re (z : ℂ) : 0 < (v z).re := by
    simp only [v, add_re, one_re, re_ofReal_mul, sub_re, conj_re]
    rcases le_or_gt ‖z‖ R with hz | hz
    · rw [hχ0 (by linarith)]
      norm_num
    · nlinarith [(hgR hz).2, sub_nonneg.2 (b.le_one (x := z)), b.nonneg (x := z)]
  have hv0 (z : ℂ) : v z ≠ 0 := fun h ↦ by simpa [h] using hv_re z
  have hv : ContDiff ℝ ∞ v := by
    refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
    rcases lt_or_ge R ‖z‖ with hz | hz
    · exact contDiffAt_const.add ((ofRealCLM.contDiff.comp
        (contDiff_const.sub b.contDiff)).contDiffAt.mul
        ((conjCLE.contDiff.contDiffAt.comp z (hgR hz).1).sub contDiffAt_const))
    · refine (contDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds
        (show ‖z‖ < R + 1 by linarith)] with w hw
      simp [v, hχ0 (le_of_lt hw)]
  -- The gauge `u = v / |v|`, written as `exp (i arg v)` to avoid a membership proof.
  set u : ℂ → Circle := fun z ↦ Circle.exp (arg (v z))
  have hu (z : ℂ) : (u z : ℂ) = v z / (‖v z‖ : ℂ) := by
    simp only [u, Circle.coe_exp, exp_arg_mul_I (hv0 z)]
  have hvt : Tendsto v (cocompact ℂ) (𝓝 1) := by
    have h := ((continuous_conj.tendsto 1).comp hgt)
    rw [map_one] at h
    refine h.congr' ?_
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (R + 2)] with z hz
    simp [v, hχ1 hz]
  have hmem : u ∈ framedGaugeGroup := by
    refine (mem_framedGaugeGroup u).2 ⟨?_, ?_⟩
    · simp only [hu, div_eq_mul_inv]
      exact hv.mul ((ofRealCLM.contDiff.comp (hv.norm ℝ hv0)).inv
        fun z ↦ ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hv0 z)))
    · have harg := ((continuousAt_arg (by simp)).tendsto).comp hvt
      rw [arg_one] at harg
      have h := (Circle.exp.continuous.tendsto 0).comp harg
      rw [Circle.exp_zero] at h
      exact h
  refine ⟨⟨u, hmem⟩, ?_⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (R + 2)] with z hz
  have hvz : v z = conj (g z) := by simp [v, hχ1 hz]
  have hgz : g z ≠ 0 := fun h ↦ by
    have := (hgR (show R < ‖z‖ by linarith)).2
    simp [h] at this
    linarith
  change (u z : ℂ) * g z = ‖g z‖
  rw [hu z, hvz, Complex.norm_conj, div_mul_eq_mul_div, conj_mul',
    div_eq_iff (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hgz))]
  ring

/-- **Normalization of the end phase by a smooth framed gauge.** A smooth field whose section
has the degree-`m` end framing `α (z / |z|)^(-m) → 1` is equivalent under the smooth framed gauge
group to a field whose section is `|α|` times the winding phase outside a compact set. -/
theorem exists_framedGaugeGroup_sectionValue_smul_eq (hx : ContDiff ℝ ∞ x)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup, ∀ᶠ z in cocompact ℂ,
      sectionValue (u • x) z = ‖sectionValue (u • x) z‖ * windingPhase m z := by
  have hs : ContDiff ℝ ∞ (sectionValue x) := by
    have hc (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ (x z i : ℂ)) :=
      ofRealCLM.contDiff.comp (contDiff_euclidean.1 hx i)
    rw [funext (sectionValue_apply x)]
    exact contDiff_const.mul ((hc 2).add ((hc 3).mul contDiff_const))
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
  exact exists_norm_sub_referenceField_le_mul_exp ((hcd 0).differentiable (by simp))
    ((hcd 1).differentiable (by simp)) ((hcd 2).of_le (by norm_cast)) ((hcd 3).of_le (by norm_cast))
    hsol' hlim hu f hc

end TauCeti.Vortex
