/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.GaussGreen
public import TauCeti.Analysis.BoundedVariation.ReducedBoundary.Ball
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Geometry.Euclidean.Volume.Sphere

/-!
# Checks for the Gauss–Green formula on the reduced boundary

The two Checks of the Gauss–Green formula `∫_s div φ = ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹`
(GeometricMeasureTheory roadmap §6.1), in a real inner product space `E` of dimension `n ≥ 2`.

* *The ball.* For `s = ball 0 R` and a compactly supported `C¹` field `φ` equal to `x` near the
  closed ball, `∫_s div φ = n |ball 0 R|` and `∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹ = R Hⁿ⁻¹(sphere 0 R)`, and
  the formula makes the two equal (`ball_check`); the inner normal would give the opposite sign
  (`setIntegral_inner_neg_normal_ball`).
* *Flux escaping to infinity.* For `s` the exterior `(closedBall 0 1)ᶜ` of the unit ball and the
  bounded `C¹` field `φ = (1 − θ) x / ‖x‖ⁿ` (`fluxField`), with `θ` a bump function equal to one
  near `0` and supported in the unit ball, `div φ = 0` on `s` and `P(s) = P(ball 0 1)` is
  finite, but `∫_s div φ = 0` while `∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹ = −Hⁿ⁻¹(sphere 0 1) = −n ω_n`
  (`exterior_check`).
  Both integrability hypotheses of the extension to fields without compact support
  (`TauCeti.integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal_of_bounded`)
  fail: `|s| = ∞` and `‖φ‖` is not integrable on `s`.
-/

open MeasureTheory Metric Module Set TopologicalSpace Filter
open scoped ENNReal RealInnerProductSpace Topology

public noncomputable section

namespace TauCeti.Examples.GaussGreenBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The ball -/

/-- The indicator of a ball has finite perimeter in the whole space. -/
theorem forall_exists_totalVariationOn_indicator_ball_ne_top {c : E} {r : ℝ} :
    ∀ K, IsCompact K → K ⊆ (⊤ : Opens E) → ∃ U : Opens E, K ⊆ (U : Set E) ∧
      totalVariationOn volume U ((ball c r).indicator 1) ≠ ∞ := fun _ _ _ => by
  refine ⟨⊤, by simp, ?_⟩
  rw [← perimeter_def, perimeter_ball_eq_ofReal_div_mul]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne

omit [MeasurableSpace E] [BorelSpace E] in
/-- The divergence of a field equal to `x` on an open set containing the ball `ball 0 R` is
`n` on the ball. -/
theorem trace_fderiv_mul_indicator_ball {R R' : ℝ} (hRR' : R ≤ R') {φ : E → E}
    (hid : EqOn φ id (ball 0 R')) (x : E) :
    LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * (ball (0 : E) R).indicator 1 x =
      finrank ℝ E * (ball (0 : E) R).indicator 1 x := by
  by_cases hx : x ∈ ball (0 : E) R
  · have hev : φ =ᶠ[𝓝 x] id :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (ball_subset_ball hRR' hx)) hid
    rw [hev.fderiv_eq, fderiv_id, ContinuousLinearMap.coe_id, LinearMap.trace_id]
  · simp [hx]

/-- **The Gauss–Green formula on a ball** (first Check of §6.1). For `s = ball 0 R` and a
compactly supported `C¹` field `φ` equal to `x` on a ball `ball 0 R'` with `R < R'`, the left side
is `∫_s div φ = n |ball 0 R|`, the right side is `∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹ = R Hⁿ⁻¹(sphere 0 R)`,
and the two agree; with `|ball 0 R| = Rⁿ ω_n` this is `n ω_n Rⁿ = R · n ω_n Rⁿ⁻¹`. -/
theorem ball_check (hn : 2 ≤ finrank ℝ E) {R R' : ℝ} (hR : 0 < R) (hRR' : R < R') {φ : E → E}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hid : EqOn φ id (ball 0 R')) :
    ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * (ball (0 : E) R).indicator 1 x =
        finrank ℝ E * volume.real (ball (0 : E) R) ∧
      ∫ x in reducedBoundary volume ⊤ (ball (0 : E) R),
          ⟪φ x, outerNormal volume ⊤ (ball (0 : E) R) x⟫ ∂μHE[finrank ℝ E - 1] =
        R * μHE[finrank ℝ E - 1].real (sphere (0 : E) R) ∧
      finrank ℝ E * volume.real (ball (0 : E) R) =
        R * μHE[finrank ℝ E - 1].real (sphere (0 : E) R) ∧
      volume.real (ball (0 : E) R) = R ^ finrank ℝ E * volume.real (ball (0 : E) 1) := by
  have hL : ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) *
      (ball (0 : E) R).indicator 1 x = finrank ℝ E * volume.real (ball (0 : E) R) := by
    simp_rw [trace_fderiv_mul_indicator_ball hRR'.le hid]
    rw [integral_const_mul, integral_indicator_one measurableSet_ball]
  have hR' : ∫ x in reducedBoundary volume ⊤ (ball (0 : E) R),
      ⟪φ x, outerNormal volume ⊤ (ball (0 : E) R) x⟫ ∂μHE[finrank ℝ E - 1] =
        R * μHE[finrank ℝ E - 1].real (sphere (0 : E) R) := by
    rw [reducedBoundary_ball hR, mul_comm, ← smul_eq_mul, ← setIntegral_const]
    refine setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx => ?_
    have hxR : ‖x‖ = R := mem_sphere_zero_iff_norm.1 hx
    rw [outerNormal_ball hR hx, hid (sphere_subset_ball hRR' hx), id, sub_zero,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hxR]
    field_simp
  refine ⟨hL, hR', ?_, Measure.addHaar_real_ball_of_pos _ _ hR⟩
  rw [← hL, ← hR']
  exact integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal hn
    (locallyIntegrableOn_indicator_const measurableSet_ball.nullMeasurableSet 1)
    forall_exists_totalVariationOn_indicator_ball_ne_top hφ hc (by simp)

/-- With the inner normal `−x / R` in place of the outer normal the flux through the sphere is
`−n |ball 0 R|`, which has the wrong sign. -/
theorem setIntegral_inner_neg_normal_ball (hn : 2 ≤ finrank ℝ E) {R R' : ℝ} (hR : 0 < R)
    (hRR' : R < R') {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hid : EqOn φ id (ball 0 R')) :
    ∫ x in sphere (0 : E) R, ⟪φ x, -(R⁻¹ • x)⟫ ∂μHE[finrank ℝ E - 1] =
        -(finrank ℝ E * volume.real (ball (0 : E) R)) ∧
      -(finrank ℝ E * volume.real (ball (0 : E) R)) < 0 := by
  obtain ⟨-, hR', hGG, -⟩ := ball_check hn hR hRR' hφ hc hid
  have hn0 : (0 : ℝ) < finrank ℝ E := by exact_mod_cast (by omega : 0 < finrank ℝ E)
  refine ⟨?_, neg_neg_of_pos (mul_pos hn0 ?_)⟩
  · simp_rw [inner_neg_right, integral_neg]
    rw [hGG, ← hR', reducedBoundary_ball hR]
    refine congrArg _ (setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx => ?_)
    rw [outerNormal_ball hR hx, sub_zero]
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    exact ENNReal.toReal_pos (measure_ball_pos _ _ hR).ne' measure_ball_lt_top.ne

/-- A field `φ` as in the first Check exists: a bump function equal to one on `ball 0 R'` times
`x`. -/
example [Nontrivial E] {R' : ℝ} (hR' : 0 < R') : ∃ φ : E → E, ContDiff ℝ 1 φ ∧
    HasCompactSupport φ ∧ EqOn φ id (ball 0 R') := by
  let θ : ContDiffBump (0 : E) := ⟨R', R' + 1, hR', by linarith⟩
  refine ⟨fun x => θ x • x, θ.contDiff.smul contDiff_id,
    θ.hasCompactSupport.smul_right, fun x hx => ?_⟩
  simp only [id, θ.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul]

/-! ### Flux escaping to infinity -/

/-- The field `(1 − θ(x)) x / ‖x‖ⁿ`: it is `x / ‖x‖ⁿ` outside the support of the bump function
`θ` centred at `0`, and vanishes near `0`. -/
def fluxField (θ : ContDiffBump (0 : E)) (x : E) : E :=
  (1 - θ x) • (‖x‖ ^ finrank ℝ E)⁻¹ • x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Unfolding lemma for `fluxField`. -/
theorem fluxField_def (θ : ContDiffBump (0 : E)) (x : E) :
    fluxField θ x = (1 - θ x) • (‖x‖ ^ finrank ℝ E)⁻¹ • x :=
  (rfl)

variable {θ : ContDiffBump (0 : E)} {x : E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Outside the support of `θ` the field is `x / ‖x‖ⁿ`. -/
theorem fluxField_of_le (hx : θ.rOut ≤ ‖x‖) :
    fluxField θ x = (‖x‖ ^ finrank ℝ E)⁻¹ • x := by
  rw [fluxField_def, θ.zero_of_le_dist (by rwa [dist_zero_right]), sub_zero, one_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Where `θ = 1` the field vanishes. -/
theorem fluxField_of_le_rIn (hx : ‖x‖ ≤ θ.rIn) : fluxField θ x = 0 := by
  rw [fluxField_def, θ.one_of_mem_closedBall (by rwa [mem_closedBall_zero_iff]), sub_self,
    zero_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The field is smooth: it vanishes near `0`, and away from `0` it is a product of smooth
functions. -/
theorem contDiff_fluxField : ContDiff ℝ 1 (fluxField θ) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : ‖x‖ < θ.rIn
  · have hev : fluxField θ =ᶠ[𝓝 x] fun _ => 0 :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)) fun y hy =>
        fluxField_of_le_rIn (mem_ball_zero_iff.1 hy).le
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (by simpa using θ.rIn_pos)
    exact (contDiffAt_const.sub θ.contDiff.contDiffAt).smul
      ((((contDiffAt_norm ℝ hx0).pow _).inv (pow_ne_zero _ (norm_ne_zero_iff.2 hx0))).smul
        contDiffAt_id)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The field is bounded by `θ.rIn ^ (1 − n)`. -/
theorem norm_fluxField_le (hn : 1 ≤ finrank ℝ E) (x : E) :
    ‖fluxField θ x‖ ≤ (θ.rIn ^ (finrank ℝ E - 1))⁻¹ := by
  have hr := θ.rIn_pos
  by_cases hx : ‖x‖ ≤ θ.rIn
  · rw [fluxField_of_le_rIn hx, norm_zero]
    positivity
  replace hx := not_le.1 hx
  have hx0 : 0 < ‖x‖ := hr.trans hx
  have hpow : ‖x‖ ^ finrank ℝ E = ‖x‖ ^ (finrank ℝ E - 1) * ‖x‖ := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [fluxField_def, norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (by positivity)),
    hpow, mul_inv, mul_assoc, inv_mul_cancel₀ hx0.ne', mul_one]
  calc ‖1 - θ x‖ * (‖x‖ ^ (finrank ℝ E - 1))⁻¹ ≤ 1 * (‖x‖ ^ (finrank ℝ E - 1))⁻¹ := by
        gcongr
        rw [Real.norm_of_nonneg (sub_nonneg.2 θ.le_one)]
        linarith [θ.nonneg (x := x)]
    _ ≤ (θ.rIn ^ (finrank ℝ E - 1))⁻¹ := by
        rw [one_mul]
        gcongr

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Euler's identity** for `ρ(y) = ‖y‖⁻ⁿ`, homogeneous of degree `−n`: `Dρ(x) x = −n ρ(x)`. -/
theorem fderiv_inv_norm_pow_apply_self (hx : x ≠ 0) :
    fderiv ℝ (fun y : E => (‖y‖ ^ finrank ℝ E)⁻¹) x x =
      -(finrank ℝ E * (‖x‖ ^ finrank ℝ E)⁻¹) := by
  set n := finrank ℝ E
  set ρ : E → ℝ := fun y => (‖y‖ ^ n)⁻¹
  have hρ : DifferentiableAt ℝ ρ x :=
    (((contDiffAt_norm ℝ hx).pow n).inv (pow_ne_zero _ (norm_ne_zero_iff.2 hx))).differentiableAt
      one_ne_zero
  have hρ' : HasFDerivAt ρ (fderiv ℝ ρ x) ((1 : ℝ) • x) := by
    rw [one_smul]
    exact hρ.hasFDerivAt
  have h₁ := hρ'.comp_hasDerivAt (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const x)
  have h₂ : HasDerivAt (fun t : ℝ => (t ^ n)⁻¹ * ρ x) (-(n * ρ x)) 1 := by
    have := ((hasDerivAt_pow n (1 : ℝ)).inv (by simp)).mul_const (ρ x)
    simpa using this
  have hev : (fun t : ℝ => (t ^ n)⁻¹ * ρ x) =ᶠ[𝓝 1] ρ ∘ fun t : ℝ => t • x := by
    filter_upwards [lt_mem_nhds one_pos] with t ht
    simp only [ρ, Function.comp_apply, norm_smul, Real.norm_of_nonneg ht.le, mul_pow, mul_inv]
  have := (h₂.congr_of_eventuallyEq hev.symm).unique h₁
  simpa [ρ] using this.symm

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The field is divergence free outside the support of `θ`**: `div (x / ‖x‖ⁿ) = 0` for
`x ≠ 0`. -/
theorem trace_fderiv_fluxField (hx : θ.rOut < ‖x‖) :
    LinearMap.trace ℝ E (fderiv ℝ (fluxField θ) x : E →ₗ[ℝ] E) = 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact (lt_irrefl _ (θ.rOut_pos.trans (by simpa using hx)))
  have hev : fluxField θ =ᶠ[𝓝 x] fun y => (‖y‖ ^ finrank ℝ E)⁻¹ • y :=
    Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hx)
      fun y hy => fluxField_of_le (le_of_lt hy)
  have hρ : DifferentiableAt ℝ (fun y : E => (‖y‖ ^ finrank ℝ E)⁻¹) x :=
    (((contDiffAt_norm ℝ hx0).pow _).inv (pow_ne_zero _ (norm_ne_zero_iff.2 hx0))).differentiableAt
      one_ne_zero
  rw [hev.fderiv_eq, trace_fderiv_smul (φ := fun y => y) hρ differentiableAt_id, fderiv_fun_id,
    ContinuousLinearMap.coe_id, LinearMap.trace_id, fderiv_inv_norm_pow_apply_self hx0]
  ring

/-- **Flux escaping to infinity** (second Check of §6.1). In dimension `n ≥ 2`, let `s` be the
exterior `(closedBall 0 1)ᶜ` of the unit ball and `θ` a bump function centred at `0` with
`θ.rOut ≤ 1`. The field `φ = fluxField θ` is `C¹` and bounded, `div φ = 0` on `s`, and `s` has the
finite perimeter of the unit ball, yet `∫_s div φ = 0` while
`∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹ = −Hⁿ⁻¹(sphere 0 1) < 0`: the formula fails. Both hypotheses of
`TauCeti.integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal_of_bounded` that
could rescue it fail, `|s| = ∞` and `‖φ‖` is not integrable on `s`. -/
theorem exterior_check (hn : 2 ≤ finrank ℝ E) (hθ : θ.rOut ≤ 1) :
    ContDiff ℝ 1 (fluxField θ) ∧
      (∀ x, ‖fluxField θ x‖ ≤ (θ.rIn ^ (finrank ℝ E - 1))⁻¹) ∧
      (∀ x ∈ (closedBall (0 : E) 1)ᶜ,
        LinearMap.trace ℝ E (fderiv ℝ (fluxField θ) x : E →ₗ[ℝ] E) = 0) ∧
      perimeter volume ⊤ (closedBall (0 : E) 1)ᶜ = perimeter volume ⊤ (ball (0 : E) 1) ∧
      perimeter volume ⊤ (ball (0 : E) 1) ≠ ∞ ∧
      ∫ x, LinearMap.trace ℝ E (fderiv ℝ (fluxField θ) x : E →ₗ[ℝ] E) *
        (closedBall (0 : E) 1)ᶜ.indicator 1 x = 0 ∧
      ∫ x in reducedBoundary volume ⊤ (closedBall (0 : E) 1)ᶜ,
          ⟪fluxField θ x, outerNormal volume ⊤ (closedBall (0 : E) 1)ᶜ x⟫
            ∂μHE[finrank ℝ E - 1] =
        -μHE[finrank ℝ E - 1].real (sphere (0 : E) 1) ∧
      -μHE[finrank ℝ E - 1].real (sphere (0 : E) 1) < 0 ∧
      volume (closedBall (0 : E) 1)ᶜ = ∞ ∧
      ¬Integrable fun x => ‖fluxField θ x‖ * (closedBall (0 : E) 1)ᶜ.indicator 1 x := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hout : ∀ x ∈ (closedBall (0 : E) 1)ᶜ, θ.rOut < ‖x‖ := fun x hx =>
    hθ.trans_lt (by simpa using hx)
  have hdiv : ∀ x ∈ (closedBall (0 : E) 1)ᶜ,
      LinearMap.trace ℝ E (fderiv ℝ (fluxField θ) x : E →ₗ[ℝ] E) = 0 := fun x hx =>
    trace_fderiv_fluxField (hout x hx)
  have hS := euclideanHausdorffMeasure_sphere (0 : E) one_pos
  have hSpos : 0 < μHE[finrank ℝ E - 1].real (sphere (0 : E) 1) := by
    refine ENNReal.toReal_pos ?_ ?_ <;> rw [hS]
    · simp [(measure_ball_pos volume (0 : E) one_pos).ne', show finrank ℝ E ≠ 0 by omega]
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne) (by simp)
  refine ⟨contDiff_fluxField, norm_fluxField_le (by omega), hdiv, ?_, ?_, ?_, ?_,
    neg_neg_of_pos hSpos, ?_, ?_⟩
  · rw [perimeter_compl, perimeter_closedBall one_pos, perimeter_ball one_pos]
  · rw [perimeter_ball one_pos]
    exact ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne
  · refine (integral_congr_ae (ae_of_all _ fun x => ?_)).trans (integral_zero E ℝ)
    by_cases hx : x ∈ (closedBall (0 : E) 1)ᶜ
    · simp [hdiv x hx]
    · simp [hx]
  · rw [reducedBoundary_compl_closedBall one_pos, ← mul_neg_one, ← smul_eq_mul,
      ← setIntegral_const]
    refine setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx => ?_
    have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hx
    rw [outerNormal_compl_closedBall one_pos hx, fluxField_of_le (hx1 ▸ hθ), hx1, one_pow,
      inv_one, one_smul, sub_zero, one_smul, inner_neg_right, real_inner_self_eq_norm_sq, hx1]
    norm_num
  · rw [measure_compl isClosed_closedBall.measurableSet measure_closedBall_lt_top.ne,
      measure_univ_of_isAddLeftInvariant]
    exact ENNReal.sub_eq_top_iff.2 ⟨rfl, measure_closedBall_lt_top.ne⟩
  · intro hint
    have hf : (fun x => ‖fluxField θ x‖ * (closedBall (0 : E) 1)ᶜ.indicator 1 x) =
        fun x => (Ioi (1 : ℝ)).indicator (fun y => (y ^ (finrank ℝ E - 1))⁻¹) ‖x‖ := by
      funext x
      by_cases hx : x ∈ (closedBall (0 : E) 1)ᶜ
      · have hx1 : 1 < ‖x‖ := by simpa using hx
        have hpow : ‖x‖ ^ finrank ℝ E = ‖x‖ ^ (finrank ℝ E - 1) * ‖x‖ := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem (mem_Ioi.2 hx1),
          fluxField_of_le (hθ.trans hx1.le), norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 (by positivity)), hpow, mul_inv, Pi.one_apply,
          mul_one, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
      · have hx1 : ¬1 < ‖x‖ := by simpa using hx
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (by simpa using hx1), mul_zero]
    rw [hf, integrable_fun_norm_addHaar] at hint
    have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 1) := by
      refine (hint.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun (fun y hy => ?_)
        measurableSet_Ioi
      have hy0 : 0 < y := zero_lt_one.trans hy
      simp only [smul_eq_mul, Set.indicator_of_mem hy]
      exact mul_inv_cancel₀ (by positivity)
    simp at h1

end TauCeti.Examples.GaussGreenBall
