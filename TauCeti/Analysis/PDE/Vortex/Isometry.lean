/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
public import TauCeti.Analysis.PDE.Vortex.Multiplier
public import TauCeti.Analysis.PDE.Vortex.Symmetry
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Sobolev.BesselPotential.ChangeOfVariables

/-!
# Isometries of the plane acting on the affine field space of framed vortices

The orientation-preserving isometries of the plane act on plane-vortex fields by pullback
(`TauCeti.Vortex.translateField`, `TauCeti.Vortex.rotateField`). This file shows that, after a
gauge transformation fixing the framing at infinity, they preserve the affine Sobolev space
`A_m^k = x_m + H^k` of framed degree-`m` fields (`TauCeti.Vortex.framedFieldSpace`), for every
natural order `k`. The direction `H^k` is invariant under translations and rotations
(`translateField_mem_sobolevFields`, `rotateField_mem_sobolevFields`), so the question is
whether the transformed reference field `x_m` stays in `A_m^k`.

* **Rotations.** The reference field is rotation-equivariant up to the constant line-frame gauge
  `u^(-m)`: `u^(-m) · R_u x_m = x_m` (`gaugeTransform_rotateField_referenceField`). Hence
  `x ↦ u^(-m) · R_u x` preserves `A_m^k` (`gaugeTransform_rotateField_mem_framedFieldSpace`).
* **Translations.** For `m ≥ 1` and `a ≠ 0` the translated reference section
  `((z + a) / |z + a|)^m` differs from `(z / |z|)^m` by a term decaying only like `1 / |z|`, which
  is not square integrable on the plane, so a gauge is needed. The **translation gauge**
  `g_a = translationGauge m a` is a smooth circle-valued map with
  `g_a(z) ((z + a) / |z + a|)^m = (z / |z|)^m` outside a disc (`coe_translationGauge_mul_pow`), and
  `g_a = 1` near the disc `|z| ≤ |a|` (`translationGauge_eq_one`). It tends to `1` at infinity, so
  it is a smooth framed gauge (`translationGauge_mem_framedGaugeGroup`). Its logarithmic derivative
  is `m (dθ_z - dθ_(z + a))` outside the disc (`gaugeForm_translationGauge_apply`). It carries the
  translated reference field to `x_m` outside a disc, so `x ↦ g_a · T_a x` preserves `A_m^k`
  (`gaugeTransform_translationGauge_translateField_mem_framedFieldSpace`).

The gauge `g_a` has bounded derivatives of every order
(`exists_norm_iteratedFDeriv_translationGauge_le`), and smooth gauges with bounded derivatives
through order `k` act on `H^k` (`gaugeLinearAction_mem_sobolevFields`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex ComplexConjugate Filter TemperedDistribution
open scoped ContDiff Topology

/-! ### Invariance of the Sobolev direction -/

/-- Translations preserve the integer-order Sobolev fields. -/
theorem translateField_mem_sobolevFields (a : ℂ) {k : ℕ} {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ sobolevFields k) : translateField a y ∈ sobolevFields k :=
  mem_sobolevFields.2 fun i ↦ by
    simpa only [translateField_apply] using
      comp_add_mem_realSobolevFunctions_natCast (by norm_num) (by norm_num) a
        (mem_sobolevFields.1 hy i)

/-- Rotations preserve the integer-order Sobolev fields. -/
theorem rotateField_mem_sobolevFields (u : Circle) {k : ℕ} {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ sobolevFields k) : rotateField u y ∈ sobolevFields k := by
  have h (j : Fin 4) : (fun z ↦ y ((u : ℂ) * z) j) ∈ realSobolevFunctions ℂ k 2 := by
    simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      rotation_apply] using
      comp_continuousLinearEquiv_mem_realSobolevFunctions_natCast (by norm_num) (by norm_num)
        (rotation u).toContinuousLinearEquiv (mem_sobolevFields.1 hy j)
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · convert add_mem (Submodule.smul_mem _ (u : ℂ).re (h 0))
      (Submodule.smul_mem _ (u : ℂ).im (h 1)) using 1
    ext z
    simp
  · convert add_mem (Submodule.smul_mem _ (u : ℂ).re (h 1))
      (Submodule.smul_mem _ (-(u : ℂ).im) (h 0)) using 1
    ext z
    simp [sub_eq_add_neg]
  · convert h 2 using 1
    ext z
    simp
  · convert h 3 using 1
    ext z
    simp

/-- **Smooth gauges act on Sobolev fields.** A smooth gauge whose derivatives through order `k`
are bounded preserves the integer-order Sobolev fields under its linear action, which rotates the
section and fixes the connection. No decay of the gauge is required. -/
theorem gaugeLinearAction_mem_sobolevFields {k : ℕ} {u : ℂ → Circle}
    (hu : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ)))
    (hbound : ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ (u z : ℂ)) z‖ ≤ C)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields k) :
    gaugeLinearAction u y ∈ sobolevFields k := by
  have hc (i : Fin 4) := mem_sobolevFields.1 hy i
  have h0 : (fun _ : ℂ ↦ (0 : ℝ)) ∈ realSobolevFunctions ℂ k 2 := zero_mem _
  -- The linear action is `P y + Re u • Q y + Im u • R y` with constant `P`, `Q`, `R`.
  have hP : (fun z ↦ !₂[y z 0, y z 1, 0, 0]) ∈ sobolevFields k := by
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    exacts [hc 0, hc 1, h0, h0]
  have hQ : (fun z ↦ !₂[0, 0, y z 2, y z 3]) ∈ sobolevFields k := by
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    exacts [h0, h0, hc 2, hc 3]
  have hR : (fun z ↦ !₂[0, 0, -y z 3, y z 2]) ∈ sobolevFields k := by
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    exacts [h0, h0, neg_mem (hc 3), hc 2]
  -- A single bound for the derivatives through order `k` of `Re u` and of `Im u`.
  choose! C hC using hbound
  have hL (L : ℂ →L[ℝ] ℝ) : ∃ M ≥ 0, ∀ n ≤ k, ∀ z,
      ‖iteratedFDeriv ℝ n (fun z ↦ L (u z : ℂ)) z‖ ≤ M := by
    refine ⟨‖L‖ * ∑ n ∈ Finset.range (k + 1), |C n|, by positivity, fun n hn z ↦ ?_⟩
    refine (L.norm_iteratedFDeriv_comp_left hu.contDiffAt (by exact_mod_cast le_top)).trans ?_
    gcongr
    exact (hC n hn z).trans ((le_abs_self _).trans (Finset.single_le_sum
      (f := fun n ↦ |C n|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hn))))
  obtain ⟨Mr, hMr, hre⟩ := hL reCLM
  obtain ⟨Mi, hMi, him⟩ := hL imCLM
  convert add_mem (add_mem hP
    (smul_mem_sobolevFields_natCast k (reCLM.contDiff.comp hu) hMr hre hQ))
    (smul_mem_sobolevFields_natCast k (imCLM.contDiff.comp hu) hMi him hR) using 1
  ext z i
  fin_cases i <;> simp [gaugeLinearAction_apply] <;> ring

/-! ### Rotations and the line frame -/

/-- **The reference field is rotation-equivariant up to the line frame.** Rotating the reference
field by `u` and applying the constant gauge `u^(-m)` returns the reference field. -/
theorem gaugeTransform_rotateField_referenceField (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (u : Circle) :
    gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u (referenceField f m)) =
      referenceField f m := by
  have hu : ‖(u : ℂ)‖ = 1 := Circle.norm_coe u
  funext z
  -- The connection is invariant under simultaneous rotation of point and vector, and real
  -- linear in the vector.
  have hlin (v : ℂ) : referenceConnection f m z v =
      (u : ℂ).re • referenceConnection f m ((u : ℂ) * z) v +
        (u : ℂ).im • referenceConnection f m ((u : ℂ) * z) (I * v) := by
    rw [← referenceConnection_mul f m hu z v, ← map_smul, ← map_smul, ← map_add]
    congr 1
    apply Complex.ext
    · simp only [mul_re, I_re, I_im, smul_re, smul_eq_mul, add_re]
      ring
    · simp only [mul_im, I_re, I_im, smul_im, smul_eq_mul, add_im]
      ring
  -- The constant gauge has vanishing logarithmic derivative.
  have hconst : gaugeForm (fun _ ↦ u⁻¹ ^ m) z = 0 := by
    ext v
    simp
  refine apply_eq_of_sectionValue_eq ?_ ?_ ?_
  · simp only [gaugeTransform_apply, hconst, rotateField_apply_zero,
      referenceField_apply, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_apply, sub_zero]
    rw [hlin 1]
    simp only [add_im, smul_im, smul_eq_mul, mul_one]
  · simp only [gaugeTransform_apply, hconst, rotateField_apply_one,
      referenceField_apply, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      zero_apply, sub_zero]
    rw [hlin I]
    simp only [add_im, smul_im, smul_eq_mul, I_mul_I, map_neg, neg_im]
    ring
  · rw [sectionValue_gaugeTransform, sectionValue_rotateField, sectionValue_referenceField,
      sectionValue_referenceField, referenceSection_mul f m hu]
    simp [← mul_assoc]

/-- **Rotations act on `A_m^k`.** For a framed degree-`m` field `x ∈ A_m^k` and a rotation `u`,
the rotated field followed by the constant line-frame gauge `u^(-m)` lies in `A_m^k`. -/
theorem gaugeTransform_rotateField_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (u : Circle) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m k) :
    gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u x) ∈ framedFieldSpace f m k := by
  rw [mem_framedFieldSpace] at hx ⊢
  have hsub : rotateField u x - rotateField u (referenceField f m) =
      rotateField u (x - referenceField f m) := by
    ext z i
    fin_cases i <;> simp <;> ring
  have h := gaugeTransform_sub_gaugeTransform (fun _ ↦ u⁻¹ ^ m) (rotateField u x)
    (rotateField u (referenceField f m))
  rw [gaugeTransform_rotateField_referenceField, hsub] at h
  rw [h]
  -- The constant gauge has bounded derivatives of every order.
  refine gaugeLinearAction_mem_sobolevFields contDiff_const (fun n _ ↦ ⟨1, fun z ↦ ?_⟩)
    (rotateField_mem_sobolevFields u hx)
  rcases n with _ | n
  · simp
  · simp [iteratedFDeriv_const_of_ne n.succ_ne_zero]

/-! ### Translations and the translation gauge -/

/-- The phase of the translation gauge: `-m arg (1 + a / z)` where `‖z‖² ≥ ‖a‖² + 2`, cut off
smoothly to zero where `‖z‖² ≤ ‖a‖² + 1`, a neighbourhood of the disc on which `1 + a / z` can
leave the slit plane. -/
private def translationPhase (m : ℕ) (a z : ℂ) : ℝ :=
  -(m * Real.smoothTransition (‖z‖ ^ 2 - ‖a‖ ^ 2 - 1) * arg (1 + a / z))

/-- **The translation gauge** of degree `m` and vector `a`: the smooth circle-valued gauge
`exp (-i m χ(z) arg (1 + a / z))`, where the cutoff `χ` vanishes where `‖z‖² ≤ ‖a‖² + 1` and equals
one where `‖z‖² ≥ ‖a‖² + 2`. Outside a disc it carries `((z + a) / ‖z + a‖) ^ m` to `(z / ‖z‖) ^ m`
(`coe_translationGauge_mul_pow`), and it tends to `1` at infinity
(`translationGauge_mem_framedGaugeGroup`). -/
def translationGauge (m : ℕ) (a z : ℂ) : Circle :=
  Circle.exp (translationPhase m a z)

/-- If `‖a‖ < ‖z‖`, then `1 + a / z` lies in the slit plane. -/
private theorem one_add_div_mem_slitPlane {a z : ℂ} (h : ‖a‖ < ‖z‖) :
    1 + a / z ∈ slitPlane :=
  mem_slitPlane_of_norm_lt_one <| by
    rw [norm_div, div_lt_one ((norm_nonneg a).trans_lt h)]
    exact h

/-- A bound `‖a‖² + c ≤ ‖z‖²` with `c > 0` gives `‖a‖ < ‖z‖`. -/
private theorem norm_lt_of_sq_add_le {a z : ℂ} {c : ℝ} (hc : 0 < c) (h : ‖a‖ ^ 2 + c ≤ ‖z‖ ^ 2) :
    ‖a‖ < ‖z‖ :=
  lt_of_pow_lt_pow_left₀ 2 (norm_nonneg z) (by linarith)

/-- The phase of the translation gauge is smooth. -/
private theorem contDiff_translationPhase (m : ℕ) (a : ℂ) :
    ContDiff ℝ ∞ (translationPhase m a) := by
  have hs : ContDiff ℝ ∞ (fun w : ℂ ↦ Real.smoothTransition (‖w‖ ^ 2 - ‖a‖ ^ 2 - 1)) :=
    Real.smoothTransition.contDiff.comp
      (((contDiff_norm_sq ℝ).sub contDiff_const).sub contDiff_const)
  refine contDiff_iff_contDiffAt.2 fun z ↦ ?_
  rcases lt_or_ge (‖z‖ ^ 2) (‖a‖ ^ 2 + 1) with hz | hz
  · -- Near `z` the cutoff vanishes.
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hopen : IsOpen {w : ℂ | ‖w‖ ^ 2 < ‖a‖ ^ 2 + 1} :=
      isOpen_lt (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds hz] with w hw
    have hw' : ‖w‖ ^ 2 - ‖a‖ ^ 2 - 1 ≤ 0 := by
      have hw : ‖w‖ ^ 2 < ‖a‖ ^ 2 + 1 := hw
      linarith
    simp [translationPhase, Real.smoothTransition.zero_of_nonpos hw']
  · have hza := norm_lt_of_sq_add_le one_pos hz
    have hz0 : z ≠ 0 := norm_pos_iff.1 ((norm_nonneg a).trans_lt hza)
    have hlog : ContDiffAt ℂ ∞ (fun w : ℂ ↦ log (1 + a / w)) z :=
      (contDiffAt_log (one_add_div_mem_slitPlane hza)).comp z
        (contDiffAt_const.add (contDiffAt_const.div contDiffAt_id hz0))
    have harg : ContDiffAt ℝ ∞ (fun w : ℂ ↦ arg (1 + a / w)) z := by
      simpa only [Function.comp_def, imCLM_apply, log_im] using
        imCLM.contDiff.contDiffAt.comp z (hlog.restrict_scalars ℝ)
    exact ((contDiffAt_const.mul hs.contDiffAt).mul harg).neg

/-- The phase of the translation gauge tends to zero at infinity. -/
private theorem tendsto_translationPhase (m : ℕ) (a : ℂ) :
    Tendsto (translationPhase m a) (cocompact ℂ) (𝓝 0) := by
  have hdiv : Tendsto (fun z : ℂ ↦ a / z) (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [norm_mul, norm_inv, div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (tendsto_norm_cocompact_atTop (E := ℂ))).const_mul ‖a‖
  have harg : Tendsto (fun z : ℂ ↦ arg (1 + a / z)) (cocompact ℂ) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ ↦ 1 + a / z) (cocompact ℂ) (𝓝 1) := by
      simpa only [add_zero] using hdiv.const_add 1
    simpa only [Function.comp_def, arg_one] using
      (continuousAt_arg one_mem_slitPlane).tendsto.comp h1
  refine squeeze_zero_norm (fun z ↦ ?_) (by simpa using harg.norm.const_mul (m : ℝ))
  simp only [translationPhase, norm_neg, norm_mul, Real.norm_natCast]
  have h₀ := Real.smoothTransition.nonneg (‖z‖ ^ 2 - ‖a‖ ^ 2 - 1)
  have h₁ := Real.smoothTransition.le_one (‖z‖ ^ 2 - ‖a‖ ^ 2 - 1)
  rw [Real.norm_of_nonneg h₀, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) h₁) (Nat.cast_nonneg m)

/-- **The translation gauge is a smooth framed gauge.** -/
theorem translationGauge_mem_framedGaugeGroup (m : ℕ) (a : ℂ) :
    translationGauge m a ∈ framedGaugeGroup :=
  exp_mem_framedGaugeGroup (contDiff_translationPhase m a) (tendsto_translationPhase m a)

/-- The translation gauge is trivial where `‖z‖² ≤ ‖a‖² + 1`. -/
theorem translationGauge_eq_one {m : ℕ} {a z : ℂ} (hz : ‖z‖ ^ 2 ≤ ‖a‖ ^ 2 + 1) :
    translationGauge m a z = 1 := by
  have h : ‖z‖ ^ 2 - ‖a‖ ^ 2 - 1 ≤ 0 := by linarith
  simp [translationGauge, translationPhase, Real.smoothTransition.zero_of_nonpos h]

/-- The translation gauge of degree zero is trivial. -/
@[simp]
theorem translationGauge_zero_left (a : ℂ) : translationGauge 0 a = 1 := by
  funext z
  simp [translationGauge, translationPhase]

/-- The translation gauge of the zero vector is trivial. -/
@[simp]
theorem translationGauge_zero_right (m : ℕ) : translationGauge m 0 = 1 := by
  funext z
  simp [translationGauge, translationPhase]

/-- Where `‖z‖² ≥ ‖a‖² + 2`, the cutoff of the translation phase is inactive. -/
private theorem translationPhase_eq {m : ℕ} {a z : ℂ} (hz : ‖a‖ ^ 2 + 2 ≤ ‖z‖ ^ 2) :
    translationPhase m a z = -(m * arg (1 + a / z)) := by
  rw [translationPhase, Real.smoothTransition.one_of_one_le (by linarith), mul_one]

/-- **The translation gauge outside a disc.** Where `‖z‖² ≥ ‖a‖² + 2`, the translation gauge
carries the translated winding phase `((z + a) / ‖z + a‖) ^ m` to the winding phase
`(z / ‖z‖) ^ m`. -/
theorem coe_translationGauge_mul_pow {m : ℕ} {a z : ℂ} (hz : ‖a‖ ^ 2 + 2 ≤ ‖z‖ ^ 2) :
    (translationGauge m a z : ℂ) * ((z + a) / ‖z + a‖) ^ m = (z / ‖z‖) ^ m := by
  have hza := norm_lt_of_sq_add_le two_pos hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 ((norm_nonneg a).trans_lt hza)
  have hza0 : z + a ≠ 0 := by
    intro h
    rw [add_eq_zero_iff_eq_neg.1 h, norm_neg] at hza
    exact lt_irrefl _ hza
  have hn : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz0)
  have hna : (‖z + a‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hza0)
  set w := 1 + a / z with hw
  have hw' : w = (z + a) / z := by
    rw [hw]
    field_simp
  have hw0 : w ≠ 0 := by
    rw [hw']
    exact div_ne_zero hza0 hz0
  -- `exp (i arg w) = w / ‖w‖`.
  have hexp : exp (arg w * I) = w / ‖w‖ := by
    rw [eq_div_iff (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hw0)), mul_comm,
      norm_mul_exp_arg_mul_I]
  have hnorm : (‖w‖ : ℂ) = ‖z + a‖ / ‖z‖ := by
    rw [hw', norm_div, ofReal_div]
  rw [translationGauge, Circle.coe_exp, translationPhase_eq hz, ofReal_neg, ofReal_mul,
    ofReal_natCast, neg_mul, exp_neg, mul_assoc, exp_nat_mul, hexp, hnorm, hw', ← inv_pow,
    ← mul_pow]
  congr 1
  field_simp

/-- The derivative of `w ↦ arg (1 + a / w)` at a point `z` with `‖a‖ < ‖z‖`, applied to `v`, is
`Im (v / (z + a)) - Im (v / z)`, that is `dθ_(z + a) - dθ_z`. -/
private theorem hasFDerivAt_arg_one_add_div {a z : ℂ} (h : ‖a‖ < ‖z‖) :
    HasFDerivAt (fun w : ℂ ↦ arg (1 + a / w))
      (imCLM ∘L ((ContinuousLinearMap.toSpanSingleton ℂ (1 / (z + a) - 1 / z)).restrictScalars
        ℝ)) z := by
  have hz0 : z ≠ 0 := norm_pos_iff.1 ((norm_nonneg a).trans_lt h)
  have hza0 : z + a ≠ 0 := by
    intro h'
    rw [add_eq_zero_iff_eq_neg.1 h', norm_neg] at h
    exact lt_irrefl _ h
  have hd : HasDerivAt (fun w : ℂ ↦ 1 + a / w) (a * -(z ^ 2)⁻¹) z := by
    simpa only [div_eq_mul_inv] using ((hasDerivAt_inv hz0).const_mul a).const_add 1
  have hlog := hd.clog (one_add_div_mem_slitPlane h)
  have hval : a * -(z ^ 2)⁻¹ / (1 + a / z) = 1 / (z + a) - 1 / z := by
    field_simp
    ring
  rw [hval] at hlog
  simpa only [Function.comp_def, imCLM_apply, log_im] using
    imCLM.hasFDerivAt.comp z (hlog.hasFDerivAt.restrictScalars ℝ)

/-- **The logarithmic derivative of the translation gauge.** Where `‖z‖² > ‖a‖² + 2`, the real
one-form `Im (g⁻¹ dg)` of the translation gauge is `m (dθ_z - dθ_(z + a))`, where
`dθ_z (v) = Im (v / z)`. -/
theorem gaugeForm_translationGauge_apply {m : ℕ} {a z : ℂ} (hz : ‖a‖ ^ 2 + 2 < ‖z‖ ^ 2)
    (v : ℂ) :
    gaugeForm (translationGauge m a) z v = m * ((v / z).im - (v / (z + a)).im) := by
  have hza := norm_lt_of_sq_add_le two_pos hz.le
  have hopen : IsOpen {w : ℂ | ‖a‖ ^ 2 + 2 < ‖w‖ ^ 2} :=
    isOpen_lt continuous_const (by fun_prop)
  have heq : translationPhase m a =ᶠ[𝓝 z] fun w ↦ -(m * arg (1 + a / w)) := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact translationPhase_eq hw.le
  have hderiv := ((hasFDerivAt_arg_one_add_div hza).const_mul (m : ℝ)).neg.congr_of_eventuallyEq
    heq
  have hg : translationGauge m a = fun w ↦ Circle.exp (translationPhase m a w) := rfl
  rw [hg, gaugeForm_exp ((contDiff_translationPhase m a).differentiable (by simp) z),
    hderiv.fderiv]
  simp only [neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, imCLM_apply, smul_eq_mul]
  rw [mul_sub, mul_one_div, mul_one_div]
  simp only [sub_im]
  ring

/-- Points of norm greater than `2 ‖a‖ + r + 2` lie, together with their translates by `a`, in
the region where the reference field of a cutoff with outer radius `r` and the translation gauge
have their exact exterior form. -/
private theorem exterior_of_lt_norm {a z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : 2 * ‖a‖ + r + 2 < ‖z‖) :
    ‖a‖ ^ 2 + 2 < ‖z‖ ^ 2 ∧ r ≤ ‖z‖ ^ 2 ∧ r ≤ ‖z + a‖ ^ 2 := by
  have ha := norm_nonneg a
  have hza : ‖z‖ - ‖a‖ ≤ ‖z + a‖ := by
    simpa using norm_sub_norm_le z (-a)
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have h1 : r + 2 ≤ ‖z + a‖ := by linarith
  nlinarith

/-- **Bounded derivatives of the translation gauge.** Every iterated derivative of the translation
gauge is bounded on the whole plane: outside a disc it is the product of the winding phase and the
conjugate of its translate. -/
theorem exists_norm_iteratedFDeriv_translationGauge_le (m : ℕ) (a : ℂ) (n : ℕ) :
    ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ (translationGauge m a z : ℂ)) z‖ ≤ C := by
  -- Any cutoff serves to write the winding phase as a globally smooth function.
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : ContDiff ℝ ∞ (referenceSection f m) := contDiff_referenceSection f m
  have hs' : ContDiff ℝ ∞ (fun z ↦ conj (referenceSection f m (z + a))) :=
    conjCLE.contDiff.comp (hs.comp (contDiff_id.add contDiff_const))
  have hg := ((mem_framedGaugeGroup _).1 (translationGauge_mem_framedGaugeGroup m a)).1
  choose C hC using exists_norm_iteratedFDeriv_referenceSection_le f m
  refine (hg.of_le (by exact_mod_cast le_top)).exists_norm_iteratedFDeriv_le_of_eq_of_lt_norm
    (g := fun z ↦ referenceSection f m z * conj (referenceSection f m (z + a)))
    (R := 2 * ‖a‖ + f.rOut + 2)
    (C := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i * C (n - i)) (fun z hz ↦ ?_)
    (fun z _ ↦ ?_)
  · obtain ⟨h₁, h₂, h₃⟩ := exterior_of_lt_norm f.rOut_pos hz
    have hunit : referenceSection f m (z + a) * conj (referenceSection f m (z + a)) = 1 := by
      rw [mul_conj, normSq_eq_norm_sq, norm_referenceSection f m h₃]
      simp
    have hmul := coe_translationGauge_mul_pow (m := m) h₁.le
    rw [← referenceSection_eq_phase f m h₃, ← referenceSection_eq_phase f m h₂] at hmul
    rw [← hmul, mul_assoc, hunit, mul_one]
  · refine (norm_iteratedFDeriv_mul_le hs hs' z (by exact_mod_cast le_top)).trans
      (Finset.sum_le_sum fun i _ ↦ ?_)
    have h' : ‖iteratedFDeriv ℝ (n - i) (fun z ↦ conj (referenceSection f m (z + a))) z‖ ≤
        C (n - i) := by
      have hc := conjLIE.norm_iteratedFDeriv_comp_left (fun z ↦ referenceSection f m (z + a)) z
        (n - i)
      simp only [Function.comp_def, conjLIE_apply] at hc
      rw [hc, iteratedFDeriv_comp_add_right]
      exact hC _ _
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hC i z) (Nat.cast_nonneg _)) h'
      (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (hC i z)))

/-- Outside a disc, the translation gauge carries the translated reference field back to the
reference field. -/
private theorem gaugeTransform_translationGauge_translateField_referenceField_apply
    (f : ContDiffBump (0 : ℝ)) (m : ℕ) (a : ℂ) {z : ℂ} (hz : 2 * ‖a‖ + f.rOut + 2 < ‖z‖) :
    gaugeTransform (translationGauge m a) (translateField a (referenceField f m)) z =
      referenceField f m z := by
  obtain ⟨h₁, h₂, h₃⟩ := exterior_of_lt_norm f.rOut_pos hz
  refine apply_eq_of_sectionValue_eq ?_ ?_ ?_
  · simp only [gaugeTransform_apply, translateField_apply, referenceField_apply,
      PiLp.toLp_apply, Matrix.cons_val_zero]
    rw [gaugeForm_translationGauge_apply h₁, referenceConnection_eq_angular f m h₂,
      referenceConnection_eq_angular f m h₃]
    simp
    ring
  · simp only [gaugeTransform_apply, translateField_apply, referenceField_apply,
      PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [gaugeForm_translationGauge_apply h₁, referenceConnection_eq_angular f m h₂,
      referenceConnection_eq_angular f m h₃]
    simp
    ring
  · rw [sectionValue_gaugeTransform, sectionValue_translateField, sectionValue_referenceField,
      sectionValue_referenceField, referenceSection_eq_phase f m h₃,
      referenceSection_eq_phase f m h₂, coe_translationGauge_mul_pow h₁.le]

/-- The translation gauge applied to the translated reference field differs from the reference
field by a smooth compactly supported field. -/
private theorem hasCompactSupport_gaugeTransform_translationGauge_translateField_sub
    (f : ContDiffBump (0 : ℝ)) (m : ℕ) (a : ℂ) :
    HasCompactSupport
      (gaugeTransform (translationGauge m a) (translateField a (referenceField f m)) -
        referenceField f m) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * ‖a‖ + f.rOut + 2))
    fun z hz ↦ ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  rw [Pi.sub_apply, gaugeTransform_translationGauge_translateField_referenceField_apply f m a hz,
    sub_self]

/-- **Translations act on `A_m^k`.** For a framed degree-`m` field `x ∈ A_m^k` and a vector `a`,
the translated field followed by the translation gauge lies in `A_m^k`. -/
theorem gaugeTransform_translationGauge_translateField_mem_framedFieldSpace
    {f : ContDiffBump (0 : ℝ)} {m k : ℕ} (a : ℂ) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m k) :
    gaugeTransform (translationGauge m a) (translateField a x) ∈ framedFieldSpace f m k := by
  rw [mem_framedFieldSpace] at hx ⊢
  have hg := ((mem_framedGaugeGroup _).1 (translationGauge_mem_framedGaugeGroup m a)).1
  have htr : translateField a (referenceField f m) = fun z ↦ referenceField f m (z + a) :=
    funext fun z ↦ translateField_apply a _ z
  have hD := mem_sobolevFields_of_hasCompactSupport
    ((contDiff_gaugeTransform hg (htr ▸ (contDiff_referenceField f m).comp
      (contDiff_id.add contDiff_const))).sub (contDiff_referenceField f m))
    (hasCompactSupport_gaugeTransform_translationGauge_translateField_sub f m a) k
  have hsub : translateField a x - translateField a (referenceField f m) =
      translateField a (x - referenceField f m) := by
    funext z
    simp
  have h := gaugeLinearAction_mem_sobolevFields hg
    (fun n _ ↦ exists_norm_iteratedFDeriv_translationGauge_le m a n)
    (translateField_mem_sobolevFields a hx)
  rw [← hsub, ← gaugeTransform_sub_gaugeTransform] at h
  have hD' : gaugeTransform (translationGauge m a) (translateField a (referenceField f m)) -
      referenceField f m ∈ sobolevFields k := hD
  simpa only [sub_add_sub_cancel] using add_mem h hD'

end TauCeti.Vortex
