/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.GaussGreen
public import TauCeti.Analysis.BoundedVariation.ReducedBoundary.Ball
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.BoundedVariation.Convex
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.NormRpow
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Geometry.Euclidean.Volume.Sphere

/-!
# Checks for the Gauss–Green formula on the reduced boundary

Two worked examples of the Gauss–Green formula `∫_s div φ = ∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹`, in a real
inner product space `E` of dimension `n ≥ 2`: the ball, and a counterexample when the domain is
unbounded.

* *The ball.* For `s = ball 0 R` and a compactly supported `C¹` field `φ` equal to `x` on the
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

omit [MeasurableSpace E] [BorelSpace E] in
/-- The divergence of a field equal to `x` on the ball `ball 0 R` is `n` on the ball. -/
theorem trace_fderiv_mul_indicator_ball {R : ℝ} {φ : E → E} (hid : EqOn φ id (ball 0 R))
    (x : E) :
    LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * (ball (0 : E) R).indicator 1 x =
      finrank ℝ E * (ball (0 : E) R).indicator 1 x := by
  by_cases hx : x ∈ ball (0 : E) R
  · have hev : φ =ᶠ[𝓝 x] id := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hx) hid
    rw [hev.fderiv_eq, fderiv_id, ContinuousLinearMap.coe_id, LinearMap.trace_id]
  · simp [hx]

/-- **The Gauss–Green formula on a ball.** For `s = ball 0 R` and a compactly supported `C¹`
field `φ` equal to `x` on the closed ball `closedBall 0 R`, the left side is
`∫_s div φ = n |ball 0 R|`, the right side is `∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹ = R Hⁿ⁻¹(sphere 0 R)`, and
the two agree; with `|ball 0 R| = Rⁿ ω_n` this is `n ω_n Rⁿ = R · n ω_n Rⁿ⁻¹`. -/
theorem ball_check (hn : 2 ≤ finrank ℝ E) {R : ℝ} (hR : 0 < R) {φ : E → E}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hid : EqOn φ id (closedBall 0 R)) :
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
    simp_rw [trace_fderiv_mul_indicator_ball (hid.mono ball_subset_closedBall)]
    rw [integral_const_mul, integral_indicator_one measurableSet_ball]
  have hR' : ∫ x in reducedBoundary volume ⊤ (ball (0 : E) R),
      ⟪φ x, outerNormal volume ⊤ (ball (0 : E) R) x⟫ ∂μHE[finrank ℝ E - 1] =
        R * μHE[finrank ℝ E - 1].real (sphere (0 : E) R) := by
    rw [reducedBoundary_ball hR, mul_comm, ← smul_eq_mul, ← setIntegral_const]
    refine setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx => ?_
    have hxR : ‖x‖ = R := mem_sphere_zero_iff_norm.1 hx
    rw [outerNormal_ball hR hx, hid (sphere_subset_closedBall hx)]
    simp [real_inner_smul_right, hxR]
    field_simp
  refine ⟨hL, hR', ?_, Measure.addHaar_real_ball_of_pos _ _ hR⟩
  rw [← hL, ← hR']
  exact integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal hn
    (locallyIntegrableOn_indicator_const measurableSet_ball.nullMeasurableSet 1)
    (fun _ hK _ => (convex_ball 0 R).exists_opens_totalVariationOn_indicator_ne_top hK.isBounded)
    hφ hc
    (by simp)

/-- With the inner normal `−x / R` in place of the outer normal the flux through the sphere is
`−n |ball 0 R|`, which has the wrong sign. -/
theorem setIntegral_inner_neg_normal_ball (hn : 2 ≤ finrank ℝ E) {R : ℝ} (hR : 0 < R)
    {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hid : EqOn φ id (closedBall 0 R)) :
    ∫ x in sphere (0 : E) R, ⟪φ x, -(R⁻¹ • x)⟫ ∂μHE[finrank ℝ E - 1] =
        -(finrank ℝ E * volume.real (ball (0 : E) R)) ∧
      -(finrank ℝ E * volume.real (ball (0 : E) R)) < 0 := by
  obtain ⟨-, hR', hGG, -⟩ := ball_check hn hR hφ hc hid
  have hn0 : (0 : ℝ) < finrank ℝ E := by exact_mod_cast (by omega : 0 < finrank ℝ E)
  refine ⟨?_, neg_neg_of_pos (mul_pos hn0 ?_)⟩
  · simp_rw [inner_neg_right, integral_neg]
    rw [hGG, ← hR', reducedBoundary_ball hR]
    refine congrArg _ (setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx => ?_)
    rw [outerNormal_ball hR hx, sub_zero]
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
    exact ENNReal.toReal_pos (measure_ball_pos _ _ hR).ne' measure_ball_lt_top.ne

/-- A field `φ` as in `ball_check` exists: a bump function equal to one on `closedBall 0 R` times
`x`. -/
example [Nontrivial E] {R : ℝ} (hR : 0 < R) : ∃ φ : E → E, ContDiff ℝ 1 φ ∧
    HasCompactSupport φ ∧ EqOn φ id (closedBall 0 R) := by
  let θ : ContDiffBump (0 : E) := ⟨R, R + 1, hR, by linarith⟩
  refine ⟨fun x => θ x • x, θ.contDiff.smul contDiff_id,
    θ.hasCompactSupport.smul_right, fun x hx => ?_⟩
  simp only [id, θ.one_of_mem_closedBall hx, one_smul]

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
theorem fluxField_of_rOut_le (hx : θ.rOut ≤ ‖x‖) :
    fluxField θ x = (‖x‖ ^ finrank ℝ E)⁻¹ • x := by
  rw [fluxField_def, θ.zero_of_le_dist (by rwa [dist_zero_right]), sub_zero, one_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Where `θ = 1` the field vanishes. -/
theorem fluxField_of_le_rIn (hx : ‖x‖ ≤ θ.rIn) : fluxField θ x = 0 := by
  rw [fluxField_def, θ.one_of_mem_closedBall (by rwa [mem_closedBall_zero_iff]), sub_self,
    zero_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The field `fluxField θ` is `C¹`. -/
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

omit [MeasurableSpace E] [BorelSpace E] in
/-- Away from `0` the field has norm `‖1 − θ(x)‖ / ‖x‖ⁿ⁻¹`. -/
theorem norm_fluxField (hx : x ≠ 0) :
    ‖fluxField θ x‖ = ‖1 - θ x‖ * (‖x‖ ^ (finrank ℝ E - 1))⁻¹ := by
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  have hpow : ‖x‖ ^ finrank ℝ E = ‖x‖ ^ (finrank ℝ E - 1) * ‖x‖ := by
    rw [← pow_succ, Nat.sub_add_cancel Module.finrank_pos]
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  rw [fluxField_def, norm_smul, norm_smul, norm_inv, norm_pow, norm_norm, hpow]
  field_simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- Outside the support of `θ` the field has norm `‖x‖^(1 − n)`. -/
theorem norm_fluxField_of_rOut_le (hx : θ.rOut ≤ ‖x‖) :
    ‖fluxField θ x‖ = (‖x‖ ^ (finrank ℝ E - 1))⁻¹ := by
  rw [norm_fluxField (norm_pos_iff.1 (θ.rOut_pos.trans_le hx)),
    θ.zero_of_le_dist (by rwa [dist_zero_right]), sub_zero, norm_one, one_mul]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The field is bounded by `θ.rIn ^ (1 − n)`. -/
theorem norm_fluxField_le (x : E) : ‖fluxField θ x‖ ≤ (θ.rIn ^ (finrank ℝ E - 1))⁻¹ := by
  have hr := θ.rIn_pos
  by_cases hx : ‖x‖ ≤ θ.rIn
  · rw [fluxField_of_le_rIn hx, norm_zero]
    positivity
  replace hx := not_le.1 hx
  rw [norm_fluxField (norm_pos_iff.1 (hr.trans hx))]
  calc ‖1 - θ x‖ * (‖x‖ ^ (finrank ℝ E - 1))⁻¹ ≤ 1 * (‖x‖ ^ (finrank ℝ E - 1))⁻¹ := by
        gcongr
        rw [Real.norm_of_nonneg (sub_nonneg.2 θ.le_one)]
        linarith [θ.nonneg (x := x)]
    _ ≤ (θ.rIn ^ (finrank ℝ E - 1))⁻¹ := by
        rw [one_mul]
        gcongr

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The field is divergence free outside the support of `θ`**: at every `x` with
`θ.rOut < ‖x‖`, where the field equals `x / ‖x‖ⁿ` near `x`, its divergence is zero. -/
theorem trace_fderiv_fluxField_eq_zero_of_rOut_lt (hx : θ.rOut < ‖x‖) :
    LinearMap.trace ℝ E (fderiv ℝ (fluxField θ) x : E →ₗ[ℝ] E) = 0 := by
  have hx0 : x ≠ 0 := norm_pos_iff.1 (θ.rOut_pos.trans hx)
  -- Near `x` the field is the radial field `‖y‖ ^ (-n) • y`, whose divergence is
  -- `(n + (-n)) ‖x‖ ^ (-n) = 0`.
  have hev : fluxField θ =ᶠ[𝓝 x] fun y => ‖y‖ ^ (-(finrank ℝ E : ℝ)) • y :=
    Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hx)
      fun y hy => by
        rw [fluxField_of_rOut_le (le_of_lt hy), Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  rw [hev.fderiv_eq, (hasFDerivAt_norm_rpow_smul_self_of_ne _ hx0).fderiv,
    trace_rpow_smul_id_add_smulRight, add_neg_cancel, zero_mul]

/-- The flux of `fluxField θ` out of the exterior of the unit ball, whose outer normal on the unit
sphere is `−x`, is `−Hⁿ⁻¹(sphere 0 1)`. -/
theorem setIntegral_inner_fluxField_outerNormal_compl_closedBall (hθ : θ.rOut ≤ 1) :
    ∫ x in reducedBoundary volume ⊤ (closedBall (0 : E) 1)ᶜ,
        ⟪fluxField θ x, outerNormal volume ⊤ (closedBall (0 : E) 1)ᶜ x⟫ ∂μHE[finrank ℝ E - 1] =
      -μHE[finrank ℝ E - 1].real (sphere (0 : E) 1) := by
  rw [reducedBoundary_compl_closedBall one_pos, ← mul_neg_one, ← smul_eq_mul,
    ← setIntegral_const]
  refine setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx => ?_
  have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hx
  rw [outerNormal_compl_closedBall one_pos hx, fluxField_of_rOut_le (hx1 ▸ hθ)]
  simp [hx1, inner_neg_right]

/-- The norm of `fluxField θ` is not integrable on the exterior of the unit ball: there it is
`‖x‖^(1 − n)`, and in polar coordinates `∫_1^∞ r^(n−1) r^(1−n) dr = ∞`. -/
theorem not_integrable_norm_fluxField_mul_indicator_compl_closedBall [Nontrivial E]
    (hθ : θ.rOut ≤ 1) :
    ¬Integrable fun x => ‖fluxField θ x‖ * (closedBall (0 : E) 1)ᶜ.indicator 1 x := by
  intro hint
  -- The integrand is the norm power `‖x‖ ^ (1 - n)` restricted to `(closedBall 0 1)ᶜ`, which is
  -- not integrable there since `1 - n ≥ -n`.
  have hpow (x : E) : (‖x‖ ^ (finrank ℝ E - 1))⁻¹ = ‖x‖ ^ ((1 : ℝ) - finrank ℝ E) := by
    rw [← neg_sub, Real.rpow_neg (norm_nonneg _), ← Real.rpow_natCast, Nat.cast_sub finrank_pos,
      Nat.cast_one]
  have hf : (fun x => ‖fluxField θ x‖ * (closedBall (0 : E) 1)ᶜ.indicator 1 x) =
      (closedBall (0 : E) 1)ᶜ.indicator fun x => ‖x‖ ^ ((1 : ℝ) - finrank ℝ E) := by
    funext x
    by_cases hx : x ∈ (closedBall (0 : E) 1)ᶜ
    · simp [Set.indicator_of_mem hx, hpow,
        norm_fluxField_of_rOut_le (hθ.trans (by simpa using hx : 1 < ‖x‖).le)]
    · simp [Set.indicator_of_notMem hx]
  rw [hf, integrable_indicator_iff isClosed_closedBall.measurableSet.compl] at hint
  linarith [(integrableOn_norm_rpow_compl_closedBall_iff one_pos).1 hint]

/-- **Flux escaping to infinity.** In dimension `n ≥ 2`, let `s` be the exterior
`(closedBall 0 1)ᶜ` of the unit ball and `θ` a bump function centred at `0` with `θ.rOut ≤ 1`.
The field `φ = fluxField θ` is `C¹` and bounded, `div φ = 0` on `s`, and `s` has the finite
perimeter of the unit ball, yet `∫_s div φ = 0` while `∫_{∂*s} ⟪φ, ν_s⟫ dHⁿ⁻¹ = −Hⁿ⁻¹(sphere 0 1)
< 0`: the formula fails. Both hypotheses of
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
  -- The divergence vanishes on `s`, which lies outside the support of `θ`.
  have hdiv : ∀ x ∈ (closedBall (0 : E) 1)ᶜ,
      LinearMap.trace ℝ E (fderiv ℝ (fluxField θ) x : E →ₗ[ℝ] E) = 0 := fun x hx =>
    trace_fderiv_fluxField_eq_zero_of_rOut_lt (hθ.trans_lt (by simpa using hx))
  -- The unit sphere has positive finite measure `n |ball 0 1|`.
  have hS := euclideanHausdorffMeasure_sphere (0 : E) one_pos
  have hSpos : 0 < μHE[finrank ℝ E - 1].real (sphere (0 : E) 1) := by
    refine ENNReal.toReal_pos ?_ ?_ <;> rw [hS]
    · simp [(measure_ball_pos volume (0 : E) one_pos).ne', show finrank ℝ E ≠ 0 by omega]
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne) (by simp)
  refine ⟨contDiff_fluxField, norm_fluxField_le, hdiv, ?_,
    ((convex_ball 0 1).perimeter_lt_top isBounded_ball).ne, ?_,
    setIntegral_inner_fluxField_outerNormal_compl_closedBall hθ, neg_neg_of_pos hSpos, ?_,
    not_integrable_norm_fluxField_mul_indicator_compl_closedBall hθ⟩
  · rw [perimeter_compl, perimeter_closedBall one_pos, perimeter_ball one_pos]
  · refine (integral_congr_ae (ae_of_all _ fun x => ?_)).trans (integral_zero E ℝ)
    by_cases hx : x ∈ (closedBall (0 : E) 1)ᶜ
    · simp [hdiv x hx]
    · simp [hx]
  · rw [measure_compl isClosed_closedBall.measurableSet measure_closedBall_lt_top.ne,
      measure_univ_of_isAddLeftInvariant]
    exact ENNReal.sub_eq_top_iff.2 ⟨rfl, measure_closedBall_lt_top.ne⟩

end TauCeti.Examples.GaussGreenBall
