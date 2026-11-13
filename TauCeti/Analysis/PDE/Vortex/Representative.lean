/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.WindingPhase
public import TauCeti.Analysis.PDE.Vortex.VacuumOperator.Regularity
import TauCeti.Analysis.PDE.Vortex.Multiplier
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Smooth framed vortices have representatives in the affine Sobolev field space

A smooth plane vortex `x` with the degree-`m` end framing `α(z) (z / |z|)^(-m) → 1` is equivalent
under the smooth framed gauge group to a field of the affine Sobolev field space
`A_m^s = x_ref + H^s` for every real order `s`
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`). Together with
`TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace`, by which two representatives in
`A_m^k`, `k ≥ 2`, related by a `C²` gauge are related by an element of the Sobolev gauge group
`G_(k+1)`, this compares smooth framed vortex orbits with the Sobolev model: no orbit is missed, and
the larger smooth framed gauge group identifies no more points of the model than `G_(k+1)` does.

By `TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq` the orbit contains a field whose
section is `|α|` times the winding phase `(z / |z|)^m` outside a compact set, and such a field
converges to `x_ref` exponentially
(`TauCeti.Vortex.exists_norm_sub_referenceField_le_mul_exp`). Sobolev regularity of all orders
then comes from the vortex equations themselves, in the winding end trivialization
`Y = (z / |z|)^(-m) · x` outside a compact set:

* there the section of `Y` is the real positive function `|α|`, and the holomorphicity rows read
  `b₁ = -∂₂ log p`, `b₂ = ∂₁ log p`, so the connection is divergence free: the gauge-fixing row
  `d₀*` of the deformation `y = Y - vacuum` vanishes (`gaugeAdjoint_vacuumField_sub_eq_zero`);
* the vortex defects of `Y = vacuum + y` vanish;
* so the deformation `ψ = χ y`, cut off near the origin, is a smooth bounded square-integrable
  gauge-fixed vortex deformation of the vacuum whose gauge-fixing row and vortex defects are
  compactly supported, and lies in every `H^k`
  (`TauCeti.Vortex.mem_sobolevFields_of_forall_mem_sobolevFields_equation`);
* outside a compact set `x - x_ref` is `ψ` with its section multiplied by the reference section, a
  smooth coefficient with bounded derivatives (`mul_section_mem_sobolevFields_natCast`).

## Main results

* `TauCeti.Vortex.eventually_gaugeTransform_inv_windingPhase`: outside a compact set, the winding
  end trivialization of an end-normalized vortex is a smooth vortex with real positive section whose
  deformation from the vacuum has vanishing gauge-fixing row.
* `TauCeti.Vortex.sub_referenceField_mem_sobolevFields`: an end-normalized smooth vortex with
  `|α| → 1` differs from `x_ref` by a field in every integer-order Sobolev space.
* `TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`: every smooth framed vortex
  orbit meets `A_m^s` for all `s` at once.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Metric
open scoped Topology ContDiff

/-- **The gauge-fixing row vanishes in the end trivialization.** On an open set where a `C²`
vortex has real positive section, `q = 0` and `p > 0`, the holomorphicity rows give
`b₁ = -∂₂ log p` and `b₂ = ∂₁ log p`, so the connection is divergence free: the gauge-fixing row
`d₀*` of its deformation from the vacuum vanishes. -/
theorem gaugeAdjoint_vacuumField_sub_eq_zero {Y : ℂ → EuclideanSpace ℝ (Fin 4)} {U : Set ℂ}
    (hU : IsOpen U) (hY : ∀ w ∈ U, ContDiffAt ℝ 2 Y w) (hsol : ∀ w ∈ U, equation Y w = 0)
    (h₃ : ∀ w ∈ U, Y w 3 = 0) (h₂ : ∀ w ∈ U, 0 < Y w 2) {z : ℂ} (hz : z ∈ U) :
    gaugeAdjoint vacuumField (Y - vacuumField) z = 0 := by
  have hYi (i : Fin 4) {w : ℂ} (hw : w ∈ U) : ContDiffAt ℝ 2 (fun t ↦ Y t i) w :=
    contDiffAt_euclidean.1 (hY w hw) i
  have hd (i : Fin 4) {w : ℂ} (hw : w ∈ U) : DifferentiableAt ℝ (fun t ↦ Y t i) w :=
    (hYi i hw).differentiableAt two_ne_zero
  -- On `U` the derivative of `q` vanishes, so the holomorphicity rows read `∂₁ p = b₂ p` and
  -- `∂₂ p = -b₁ p`.
  have hq (w : ℂ) (hw : w ∈ U) : fderiv ℝ (fun t ↦ Y t 3) w = 0 := by
    have : (fun t ↦ Y t 3) =ᶠ[𝓝 w] fun _ ↦ 0 :=
      Filter.eventually_of_mem (hU.mem_nhds hw) fun t ht ↦ h₃ t ht
    rw [this.fderiv_eq, fderiv_const_apply]
  have hrow (w : ℂ) (hw : w ∈ U) : fderiv ℝ (fun t ↦ Y t 2) w 1 = Y w 1 * Y w 2 ∧
      fderiv ℝ (fun t ↦ Y t 2) w I = -(Y w 0 * Y w 2) := by
    have h₁ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 1) (hsol w hw)
    have h₂' := congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v 2) (hsol w hw)
    simp only [equation_apply_one, equation_apply_two, hq w hw, h₃ w hw,
      zero_apply, PiLp.zero_apply] at h₁ h₂'
    constructor <;> linarith
  have e₁ : (fun w ↦ Y w 1 * Y w 2) =ᶠ[𝓝 z] fun w ↦ fderiv ℝ (fun t ↦ Y t 2) w 1 :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw ↦ (hrow w hw).1.symm
  have e₂ : (fun w ↦ Y w 0 * Y w 2) =ᶠ[𝓝 z] fun w ↦ -fderiv ℝ (fun t ↦ Y t 2) w I :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw ↦
      (by rw [(hrow w hw).2, neg_neg] : Y w 0 * Y w 2 = -fderiv ℝ (fun t ↦ Y t 2) w I)
  have d₁ := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L I) e₁.fderiv_eq
  have d₂ := congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L 1) e₂.fderiv_eq
  simp only [fderiv_fun_mul (hd 1 hz) (hd 2 hz), fderiv_fun_mul (hd 0 hz) (hd 2 hz),
    fderiv_fun_neg, add_apply, smul_apply,
    neg_apply, smul_eq_mul] at d₁ d₂
  have hcomm := fderiv_fderiv_apply_comm (hYi 2 hz) (by simp) I 1
  obtain ⟨r₁, rI⟩ := hrow z hz
  have hsum : Y z 2 * (fderiv ℝ (fun t ↦ Y t 0) z 1 + fderiv ℝ (fun t ↦ Y t 1) z I) = 0 := by
    rw [r₁] at d₂
    rw [rI] at d₁
    linear_combination d₁ + d₂ - hcomm
  have hsum' := (mul_eq_zero.1 hsum).resolve_left (h₂ z hz).ne'
  simp only [gaugeAdjoint_def, vacuumField_apply, Pi.sub_apply, PiLp.sub_apply, h₃ z hz]
  simpa using hsum'

/-- If near every point outside a compact set a smooth field `ψ` agrees with a deformation `y` of
the vacuum whose gauge-fixing row and vortex defects vanish there, then the gauge-fixing row and
vortex defects of `ψ` form a smooth compactly supported field, hence lie in every `H^j`. -/
private theorem gaugeFixedDefect_mem_sobolevFields {ψ y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hψ : ContDiff ℝ ∞ ψ) {R : ℝ} (hψy : ∀ z, R < ‖z‖ → ψ =ᶠ[𝓝 z] y)
    (hgauge : ∀ z, R < ‖z‖ → gaugeAdjoint vacuumField y z = 0)
    (hsol : ∀ z, R < ‖z‖ → equation (vacuumField + y) z = 0) (j : ℕ) :
    (fun z ↦ !₂[gaugeAdjoint vacuumField ψ z, equation (vacuumField + ψ) z 0,
      equation (vacuumField + ψ) z 1, equation (vacuumField + ψ) z 2]) ∈ sobolevFields j := by
  refine mem_sobolevFields_of_hasCompactSupport ?_ ?_ j
  · have hL := contDiff_gaugeFixedOperator (n := ∞) contDiff_vacuumField hψ
    have he := contDiff_equation (n := ∞) (m := ∞) (contDiff_vacuumField.add hψ) le_rfl
    have he' (i : Fin 3) : ContDiff ℝ ∞ (fun z ↦ equation (vacuumField + ψ) z i) :=
      contDiff_euclidean.1 he i
    have hL' : ContDiff ℝ ∞ (fun z ↦ gaugeAdjoint vacuumField ψ z) := by
      simpa only [gaugeFixedOperator_apply_zero] using contDiff_euclidean.1 hL 0
    refine contDiff_euclidean.2 fun i ↦ ?_
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
    exacts [hL', he' 0, he' 1, he' 2]
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) fun z hz ↦ ?_
    have hz' : R < ‖z‖ := by simpa using hz
    have heq : vacuumField + ψ =ᶠ[𝓝 z] vacuumField + y := by
      filter_upwards [hψy z hz'] with w hw
      simp only [Pi.add_apply, hw]
    rw [gaugeAdjoint_congr_nhds _ (hψy z hz'), hgauge z hz', equation_congr_nhds heq,
      hsol z hz']
    ext i
    fin_cases i <;> simp

/-- **The winding end trivialization of an end-normalized vortex.** Let `x` be a smooth plane
vortex whose section is nonzero and equal to `|α|` times the winding phase `(z / |z|)^m` outside a
compact set. Outside a compact set its end trivialization `Y = (z / |z|)^(-m) · x` is smooth, solves
the vortex equations, has real positive section, and the gauge-fixing row of its deformation
`Y - vacuum` from the vacuum vanishes. -/
theorem eventually_gaugeTransform_inv_windingPhase {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (hne : ∀ᶠ z in cocompact ℂ, sectionValue x z ≠ 0) :
    ∀ᶠ z in cocompact ℂ, ContDiffAt ℝ ∞ (gaugeTransform (windingPhase m)⁻¹ x) z ∧
      equation (gaugeTransform (windingPhase m)⁻¹ x) z = 0 ∧
      0 < gaugeTransform (windingPhase m)⁻¹ x z 2 ∧ gaugeTransform (windingPhase m)⁻¹ x z 3 = 0 ∧
      gaugeAdjoint vacuumField (gaugeTransform (windingPhase m)⁻¹ x - vacuumField) z = 0 := by
  obtain ⟨R, -, hR⟩ := hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸
    (hphase.and hne).and (tendsto_norm_cocompact_atTop.eventually_gt_atTop 0))
  set U : Set ℂ := {z | R < ‖z‖}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hRU {z : ℂ} (hz : z ∈ U) := hR (Set.mem_ofPred.2 hz.le)
  have hU0 {z : ℂ} (hz : z ∈ U) : z ≠ 0 := norm_pos_iff.1 (hRU hz).2
  set Y := gaugeTransform (windingPhase m)⁻¹ x
  have hY {z : ℂ} (hz : z ∈ U) : ContDiffAt ℝ ∞ Y z :=
    contDiffAt_gaugeTransform (contDiffAt_inv_windingPhase m (hU0 hz)) hx.contDiffAt
  have hYsec {z : ℂ} (hz : z ∈ U) : Y z 2 = ‖sectionValue x z‖ / 2 ∧ Y z 3 = 0 := by
    have h := sectionValue_gaugeTransform_inv_windingPhase (hRU hz).1.1
    rw [sectionValue_apply] at h
    have h₂ := congrArg Complex.re h
    have h₃ := congrArg Complex.im h
    simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat,
      im_ofNat] at h₂ h₃
    constructor <;> linarith
  have hYpos {z : ℂ} (hz : z ∈ U) : 0 < Y z 2 := by
    rw [(hYsec hz).1]
    exact half_pos (norm_pos_iff.2 (hRU hz).1.2)
  have hYsol {z : ℂ} (hz : z ∈ U) : equation Y z = 0 :=
    (equation_gaugeTransform_eq_zero_iff (contDiffAt_inv_windingPhase m (hU0 hz))
      fun i ↦ (contDiff_euclidean.1 hx i).differentiable (by simp) z).2 (hsol z)
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z (hz : z ∈ U)
  exact ⟨hY hz, hYsol hz, hYpos hz, (hYsec hz).2,
    gaugeAdjoint_vacuumField_sub_eq_zero hUo (fun w hw ↦ (hY hw).of_le (by simp))
      (fun w hw ↦ hYsol hw) (fun w hw ↦ (hYsec hw).2) (fun w hw ↦ hYpos hw) hz⟩

/-- A smooth field which, outside a compact set, is a field `ψ ∈ H^k` with its section multiplied
by the reference section of `A_m^s`, lies in `H^k`. -/
private theorem mem_sobolevFields_of_eventually_eq_sectionMul_referenceSection
    {D ψ : ℂ → EuclideanSpace ℝ (Fin 4)} (hD : ContDiff ℝ ∞ D) (hψ : ContDiff ℝ ∞ ψ)
    (f : ContDiffBump (0 : ℝ)) (m : ℕ) {k : ℕ} (hψk : ψ ∈ sobolevFields k) {R : ℝ}
    (hDψ : ∀ z, R < ‖z‖ → D z = sectionMul (referenceSection f m) ψ z) :
    D ∈ sobolevFields k := by
  have hF : sectionMul (referenceSection f m) ψ ∈ sobolevFields k :=
    mul_section_mem_sobolevFields_natCast (contDiff_referenceSection f m)
      (fun n _ ↦ exists_norm_iteratedFDeriv_referenceSection_le f m n) hψk
  have hG : D - sectionMul (referenceSection f m) ψ ∈ sobolevFields k :=
    mem_sobolevFields_of_hasCompactSupport
      (hD.sub (contDiff_sectionMul (contDiff_referenceSection f m) hψ))
      (HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) R) fun z hz ↦ by
        rw [hDψ z (by simpa using hz)]
        exact sub_self _) k
  simpa using add_mem hF hG

/-- **Sobolev regularity of an end-normalized smooth vortex.** Let `x` be a smooth plane vortex
with `|α| → 1` at infinity whose section is `|α|` times the winding phase `(z / |z|)^m` outside a
compact set. Then `x - x_ref` lies in every integer-order Sobolev space, where `x_ref` is the
reference field of the affine field space `A_m^s`. -/
theorem sub_referenceField_mem_sobolevFields {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) (k : ℕ) : x - referenceField f m ∈ sobolevFields k := by
  have hxi (i : Fin 4) : ContDiff ℝ ∞ (fun w ↦ x w i) := contDiff_euclidean.1 hx i
  obtain ⟨K, hK⟩ := exists_norm_sub_referenceField_le_mul_exp (hxi 0).continuous
    (hxi 1).continuous ((hxi 2).of_le (by simp)) ((hxi 3).of_le (by simp)) hsol
    hlim hphase f (c := 1 / 4) (by norm_num)
  have hK0 : 0 ≤ K := by simpa using (norm_nonneg _).trans (hK 0)
  have hne : ∀ᶠ z in cocompact ℂ, sectionValue x z ≠ 0 :=
    (hlim.eventually (lt_mem_nhds zero_lt_one)).mono fun z hz h ↦ by
      rw [← sq_norm_sectionValue, h, norm_zero] at hz
      norm_num at hz
  -- A radius beyond which the end trivialization has the properties above and the reference field
  -- is the winding field.
  obtain ⟨R, -, hR⟩ := hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸
    (eventually_gaugeTransform_inv_windingPhase hx hsol hphase hne).and
      (tendsto_norm_cocompact_atTop.eventually_gt_atTop (max 1 f.rOut)))
  set R₀ := max R 0
  have hRU {z : ℂ} (hz : R₀ < ‖z‖) := hR ((le_max_left _ _).trans hz.le)
  -- The deformation `y` of the end trivialization from the vacuum is the end trivialization of
  -- `x - x_ref`.
  set y := gaugeTransform (windingPhase m)⁻¹ x - vacuumField
  have hyz {z : ℂ} (hz : R₀ < ‖z‖) :
      y z = gaugeLinearAction (windingPhase m)⁻¹ (x - referenceField f m) z := by
    have hr := gaugeTransform_inv_windingPhase_referenceField f m (rOut_le_norm_sq f (hRU hz).2)
    rw [← gaugeTransform_sub_gaugeTransform, Pi.sub_apply, hr]
    rfl
  -- Cut `y` off near the origin: `ψ` is smooth, bounded and square integrable.
  obtain ⟨ψ, hψ, hψU, hψy⟩ := exists_contDiff_cutoff_outside_closedBall (n := ⊤) (y := y)
    (R := R₀ + 1) (le_max_right R 0) (by linarith) fun z hz ↦
      (hRU hz).1.1.sub contDiff_vacuumField.contDiffAt
  have hψbound (z : ℂ) : ‖ψ z‖ ≤ K * Real.exp (-(1 / 4 * ‖z‖)) := by
    rcases hψy z with h | ⟨hz, h⟩
    · rw [h, norm_zero]
      exact (norm_nonneg _).trans (hK z)
    · rw [hyz hz, norm_gaugeLinearAction] at h
      exact h.trans (hK z)
  have hψB (z : ℂ) : ‖ψ z‖ ≤ K := (hψbound z).trans (mul_le_of_le_one_right hK0
    (Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg z])))
  -- The gauge-fixed vortex defect of `ψ` vanishes outside a compact set, so `ψ` lies in every
  -- `H^j`.
  have hψk := mem_sobolevFields_of_forall_mem_sobolevFields_equation hψ hψB
    (mem_sobolevFields_zero_of_norm_le_mul_exp hψ.continuous.aestronglyMeasurable (by norm_num)
      hψbound)
    (gaugeFixedDefect_mem_sobolevFields hψ hψU
      (fun z hz ↦ (hRU (by linarith)).1.2.2.2.2) fun z hz ↦ by
        convert (hRU (by linarith)).1.2.1 using 2
        funext w
        simp only [y, Pi.add_apply, Pi.sub_apply, add_sub_cancel])
  -- Back in the winding frame: outside a compact set, `x - x_ref` is `ψ` with its section
  -- multiplied by the reference section.
  refine mem_sobolevFields_of_eventually_eq_sectionMul_referenceSection (R := R₀ + 1)
    (hx.sub (contDiff_referenceField f m)) hψ f m (hψk k) fun z (hz : R₀ + 1 < ‖z‖) ↦ ?_
  have hzU : R₀ < ‖z‖ := by linarith
  have hs : referenceSection f m z = windingPhase m z := by
    rw [referenceSection_eq_phase f m (rOut_le_norm_sq f (hRU hzU).2),
      coe_windingPhase m (ne_zero_of_rOut_le_norm_sq f (rOut_le_norm_sq f (hRU hzU).2))]
  rw [← Pi.sub_apply x (referenceField f m) z,
    ← gaugeLinearAction_gaugeLinearAction_inv (windingPhase m) (x - referenceField f m),
    gaugeLinearAction_apply, ← hyz hzU, sectionMul_apply, hs, (hψU z hz).eq_of_nhds]

/-- **Every smooth framed vortex orbit meets the affine Sobolev field space.** A smooth plane
vortex `x` with the degree-`m` end framing `α (z / |z|)^(-m) → 1` is equivalent under the smooth
framed gauge group to a field lying in the affine field space `A_m^s` for every real order `s`. -/
theorem exists_framedGaugeGroup_smul_mem_framedFieldSpace {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {m : ℕ} (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (f : ContDiffBump (0 : ℝ)) :
    ∃ u : framedGaugeGroup, ∀ s : ℝ, u • x ∈ framedFieldSpace f m s := by
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_sectionValue_smul_eq hx hframe
  refine ⟨u, fun s ↦ ?_⟩
  obtain ⟨huc, hu1⟩ := (mem_framedGaugeGroup _).1 u.property
  rw [framedGaugeGroup_smul] at hu ⊢
  have hux : ContDiff ℝ ∞ (gaugeTransform u.val x) := contDiff_gaugeTransform huc hx
  have hsol' (z : ℂ) : equation (gaugeTransform u.val x) z = 0 :=
    (equation_gaugeTransform_eq_zero_iff ((huc.of_le (by norm_cast)).contDiffAt)
      fun i ↦ (contDiff_euclidean.1 hx i).differentiable (by simp) z).2 (hsol z)
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow
    (tendsto_sectionValue_gaugeTransform hu1 hframe)
  exact framedFieldSpace_mono f m (Nat.le_ceil s) (mem_framedFieldSpace.2
    (sub_referenceField_mem_sobolevFields hux hsol' hlim hu f ⌈s⌉₊))

end TauCeti.Vortex
