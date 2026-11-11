/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.AdjointBoundary
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Green's formula on a disc and the duality for the rotating-line problem

For complex functions `g` and `ξ` that are real `C¹` near a closed disc `|z - c| ≤ r`, Stokes'
formula for the one-form `g ξ dz`, whose exterior derivative is `d(g ξ dz) = 2 i \bar∂(g ξ) dA`,
gives **Green's formula for `\bar∂` with boundary term**

`∫_{|z - c| < r} (g \bar∂ξ + ξ \bar∂g) dA = (2 i)⁻¹ ∮_{|z - c| = r} g ξ dz`.

Its real part is the integration by parts behind McDuff–Salamon Lemma C.1.9 on the disc:

`∫ Re (g \bar∂ξ) = -∫ Re (ξ \bar∂g) + ½ ∫_{-π}^{π} Re (r e^{iθ} g ξ)(c + r e^{iθ}) dθ`.

For `g` holomorphic on the open disc and continuous up to the boundary the area term in `g`
vanishes, and a limit `r → R` removes the need for regularity of `g` on the boundary circle.

On the unit disc with boundary values of `ξ` on the rotating line `w ^ (k / 2) ℝ`, the cokernel of
`\bar∂` is represented by the adjoint solutions `TauCeti.unitDiscAdjointKernel k`: the forms
`η = conj g d(conj z)` with `g` holomorphic and `η(∂_θ)` on the same line. The pairing of `η` with
`\bar∂ξ d(conj z)` is a positive multiple of `∫ Re (g \bar∂ξ)`. By Green's formula it reduces to
the boundary term `½ ∫ Re (w g ξ) dθ`, and the adjoint boundary condition is exactly the condition
that makes `w g ξ` purely imaginary on the circle for every admissible `ξ`
(`TauCeti.adjoint_boundary_iff_forall_re_mul_eq_zero`). So every adjoint solution is orthogonal
to the image of `\bar∂`: this is one direction of the duality (C.1.3) of McDuff–Salamon on the
disc model. The other direction, that a function orthogonal to all adjoint solutions lies in the
image, is the solvability of the Riemann–Hilbert problem and is not treated here.

## Main results

* `TauCeti.integral_ball_conjWirtingerDeriv_eq_circleIntegral`:
  `∫_{|z - c| < r} \bar∂h dA = (2 i)⁻¹ ∮_{|z - c| = r} h dz` for `h` real `C¹` near the closed
  disc.
* `TauCeti.integral_ball_mul_conjWirtingerDeriv_add_eq_circleIntegral`: Green's formula for the
  product `g ξ`.
* `TauCeti.integral_ball_re_mul_conjWirtingerDeriv_eq`: its real form, with the boundary term
  written in the angle.
* `TauCeti.integral_ball_mul_conjWirtingerDeriv_eq_circleIntegral_of_diffContOnCl`: Green's
  formula for `g` holomorphic on the open disc and continuous on its closure.
* `TauCeti.adjoint_boundary_iff_forall_re_mul_eq_zero`: at a point `w` of the unit circle, `c`
  satisfies the adjoint boundary condition exactly when `Re (w c v) = 0` for every `v` on the line
  `v = w ^ k conj v`.
* `TauCeti.integral_ball_re_mul_conjWirtingerDeriv_eq_zero_of_mem_unitDiscAdjointKernel`: the
  orthogonality `∫_{|z| < 1} Re (g \bar∂ξ) = 0` for adjoint solutions `g` and `ξ` with boundary
  values on the rotating line.

## Checks

* `TauCeti.unitDiscAdjointKernel_neg_two`: for `k = -2` the adjoint solutions are the real
  multiples of the constant `-I`, and
  `TauCeti.integral_ball_im_conjWirtingerDeriv_eq_zero_of_eq_zpow_neg_two_mul_conj` is the
  resulting orthogonality `∫ Im (\bar∂ξ) = 0`.
* `TauCeti.exists_mem_unitDiscCauchyRiemannKernel_integral_ball_re_mul_ne_zero`: the unshifted
  condition `g ∈ unitDiscCauchyRiemannKernel k` is not the dual one. For `k = 0`, `g = 1` and
  `ξ z = Re z`, real on the circle with `\bar∂ξ = ½`, the pairing is `π / 2`
  (`TauCeti.integral_ball_re_conjWirtingerDeriv_ofReal_re`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (Lemma C.1.9 and the duality (C.1.3)).
-/

public section

namespace TauCeti

open Complex Metric MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real

/-! ### Green's formula on a disc -/

/-- The one-form `h dz` on the plane, `v ↦ h z * v`. -/
private noncomputable def dzForm (h : ℂ → ℂ) : ℂ → ℂ [⋀^Fin 1]→L[ℝ] ℂ :=
  fun z ↦ ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).toContinuousLinearEquiv
    |>.toContinuousLinearMap.comp (ContinuousLinearMap.mul ℝ ℂ)) (h z)

private theorem dzForm_apply (h : ℂ → ℂ) (z : ℂ) (v : Fin 1 → ℂ) :
    dzForm h z v = h z * v 0 := by
  simp [dzForm, ContinuousAlternatingMap.ofSubsingletonLIE]

private theorem contDiffAt_dzForm {h : ℂ → ℂ} {z : ℂ} (hh : ContDiffAt ℝ 1 h z) :
    ContDiffAt ℝ 1 (dzForm h) z :=
  (ContinuousLinearMap.contDiff _).contDiffAt.comp z hh

/-- The exterior derivative of `h dz` on the frame `(1, I)` is `2 i \bar∂h`. -/
private theorem extDeriv_dzForm {h : ℂ → ℂ} {z : ℂ} (hh : ContDiffAt ℝ 1 h z) :
    extDeriv (dzForm h) z ![1, I] = 2 * I * conjWirtingerDeriv h z 1 := by
  rw [extDeriv_apply ((contDiffAt_dzForm hh).differentiableAt one_ne_zero)]
  simp only [Nat.reduceAdd, Int.reduceNeg, dzForm_apply, Fin.removeNth, Fin.isValue, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Fin.sum_univ_two, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    pow_zero, Fin.zero_succAbove, Fin.succ_zero_eq_one, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, one_mul, Nat.mod_succ, pow_one, ne_eq,
    one_ne_zero, not_false_eq_true, Fin.succAbove_ne_zero_zero, mul_one, neg_mul]
  have hh' : DifferentiableAt ℝ h z := hh.differentiableAt one_ne_zero
  rw [fderiv_mul_const hh', conjWirtingerDeriv_apply]
  simp only [smul_apply, smul_eq_mul, mul_one]
  linear_combination (-(fderiv ℝ h z I)) * I_mul_I

/-- An open disc and its closure differ by a null set. -/
private theorem ball_ae_eq_closedBall (c : ℂ) (r : ℝ) :
    ball c r =ᵐ[volume] closedBall c r := by
  rw [← ball_union_sphere]
  exact (union_ae_eq_left_of_ae_eq_empty
    (ae_eq_empty.2 (Measure.addHaar_sphere volume c r))).symm

/-- A circle integral written over the angle interval `[-π, π]`. -/
private theorem integral_neg_pi_pi_eq_circleIntegral (h : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    (∫ θ in -π..π, circleMap 0 r θ * I * h (circleMap c r θ)) = ∮ z in C(c, r), h z := by
  have hper : Function.Periodic (fun θ ↦ circleMap 0 r θ * I * h (circleMap c r θ)) (2 * π) :=
    fun θ ↦ by simp only [periodic_circleMap _ _ θ]
  have := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at this
  rw [this, circleIntegral]
  simp only [deriv_circleMap, smul_eq_mul]

/-- Stokes' formula for `h dz` on a closed disc, with the boundary term written in the angle. -/
private theorem integral_ball_conjWirtingerDeriv_eq_integral_circle {h : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hh : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 h z) :
    ∫ z in ball c r, conjWirtingerDeriv h z 1 =
      (2 * I)⁻¹ * ∫ θ in -π..π, circleMap 0 r θ * I * h (circleMap c r θ) := by
  have hs := integral_extDeriv_closedBall hr fun z hz ↦ contDiffAt_dzForm (hh z hz)
  rw [setIntegral_congr_fun measurableSet_closedBall fun z hz ↦ extDeriv_dzForm (hh z hz),
    integral_const_mul, ← setIntegral_congr_set (ball_ae_eq_closedBall c r)] at hs
  simp only [dzForm_apply] at hs
  rw [eq_inv_mul_iff_mul_eq₀ (mul_ne_zero two_ne_zero I_ne_zero), hs]
  exact intervalIntegral.integral_congr fun θ _ ↦ by ring

/-- **Stokes' formula for `\bar∂` on a disc.** For `h` real `C¹` near the closed disc
`|z - c| ≤ r`, `∫_{|z - c| < r} \bar∂h dA = (2 i)⁻¹ ∮_{|z - c| = r} h dz`. -/
theorem integral_ball_conjWirtingerDeriv_eq_circleIntegral {h : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hh : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 h z) :
    ∫ z in ball c r, conjWirtingerDeriv h z 1 = (2 * I)⁻¹ * ∮ z in C(c, r), h z := by
  rw [integral_ball_conjWirtingerDeriv_eq_integral_circle hr hh,
    integral_neg_pi_pi_eq_circleIntegral]

variable {g ξ : ℂ → ℂ} {c : ℂ} {r : ℝ}

private theorem conjWirtingerDeriv_mul_apply_one {z : ℂ} (hg : ContDiffAt ℝ 1 g z)
    (hξ : ContDiffAt ℝ 1 ξ z) :
    conjWirtingerDeriv (fun y ↦ g y * ξ y) z 1 =
      g z * conjWirtingerDeriv ξ z 1 + ξ z * conjWirtingerDeriv g z 1 := by
  rw [conjWirtingerDeriv_fun_mul (hg.differentiableAt one_ne_zero)
    (hξ.differentiableAt one_ne_zero)]
  rfl

/-- **Green's formula for `\bar∂` with boundary term.** For `g` and `ξ` real `C¹` near the
closed disc `|z - c| ≤ r`,
`∫_{|z - c| < r} (g \bar∂ξ + ξ \bar∂g) dA = (2 i)⁻¹ ∮_{|z - c| = r} g ξ dz`. -/
theorem integral_ball_mul_conjWirtingerDeriv_add_eq_circleIntegral (hr : 0 ≤ r)
    (hg : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 g z)
    (hξ : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 ξ z) :
    ∫ z in ball c r, (g z * conjWirtingerDeriv ξ z 1 + ξ z * conjWirtingerDeriv g z 1) =
      (2 * I)⁻¹ * ∮ z in C(c, r), g z * ξ z := by
  rw [← integral_ball_conjWirtingerDeriv_eq_circleIntegral hr fun z hz ↦ (hg z hz).mul (hξ z hz)]
  refine setIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_
  have hz' := ball_subset_closedBall hz
  exact (conjWirtingerDeriv_mul_apply_one (hg z hz') (hξ z hz')).symm

private theorem integral_re_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : ∫ x, (f x).re ∂μ = (∫ x, f x ∂μ).re :=
  reCLM.integral_comp_comm hf

private theorem intervalIntegral_re_eq {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    ∫ x in a..b, (f x).re = (∫ x in a..b, f x).re :=
  reCLM.intervalIntegral_comp_comm hf

/-- A function continuous at every point of a closed disc is integrable on the open disc. -/
private theorem integrableOn_ball_of_continuousAt {f : ℂ → ℂ}
    (hf : ∀ z ∈ closedBall c r, ContinuousAt f z) : IntegrableOn f (ball c r) :=
  ((continuousOn_of_forall_continuousAt hf).integrableOn_compact
    (isCompact_closedBall c r)).mono_set ball_subset_closedBall

private theorem continuousAt_conjWirtingerDeriv {z : ℂ} (hg : ContDiffAt ℝ 1 g z) :
    ContinuousAt (fun y ↦ conjWirtingerDeriv g y 1) z :=
  (hg.conjWirtingerDeriv_apply (m := 0) (by simp) 1).continuousAt

/-- **Green's formula, real form.** For `g` and `ξ` real `C¹` near the closed disc
`|z - c| ≤ r`, `∫ Re (g \bar∂ξ) = -∫ Re (ξ \bar∂g) + ½ ∫_{-π}^{π} Re (r e^{iθ} g ξ) dθ`, where
`g` and `ξ` are evaluated at `c + r e^{iθ}` in the boundary term. This is the integration by
parts of McDuff–Salamon Lemma C.1.9 on the disc. -/
theorem integral_ball_re_mul_conjWirtingerDeriv_eq (hr : 0 ≤ r)
    (hg : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 g z)
    (hξ : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 ξ z) :
    ∫ z in ball c r, (g z * conjWirtingerDeriv ξ z 1).re =
      -(∫ z in ball c r, (ξ z * conjWirtingerDeriv g z 1).re) +
        2⁻¹ * ∫ θ in -π..π,
          (circleMap 0 r θ * g (circleMap c r θ) * ξ (circleMap c r θ)).re := by
  have hA : IntegrableOn (fun z ↦ g z * conjWirtingerDeriv ξ z 1) (ball c r) :=
    integrableOn_ball_of_continuousAt fun z hz ↦
      (hg z hz).continuousAt.mul (continuousAt_conjWirtingerDeriv (hξ z hz))
  have hB : IntegrableOn (fun z ↦ ξ z * conjWirtingerDeriv g z 1) (ball c r) :=
    integrableOn_ball_of_continuousAt fun z hz ↦
      (hξ z hz).continuousAt.mul (continuousAt_conjWirtingerDeriv (hg z hz))
  have hcont : Continuous fun θ ↦ circleMap 0 r θ * g (circleMap c r θ) * ξ (circleMap c r θ) := by
    have hcm (f : ℂ → ℂ) (hf : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 f z) :
        Continuous fun θ ↦ f (circleMap c r θ) :=
      (continuousOn_of_forall_continuousAt fun z hz ↦ (hf z hz).continuousAt).comp_continuous
        (continuous_circleMap c r) fun θ ↦ circleMap_mem_closedBall c hr θ
    exact ((continuous_circleMap 0 r).mul (hcm g hg)).mul (hcm ξ hξ)
  have h := integral_ball_conjWirtingerDeriv_eq_integral_circle hr
    fun z hz ↦ (hg z hz).mul (hξ z hz)
  rw [setIntegral_congr_fun measurableSet_ball fun z hz ↦
      conjWirtingerDeriv_mul_apply_one (hg z (ball_subset_closedBall hz))
        (hξ z (ball_subset_closedBall hz)),
    integral_add hA hB, ← intervalIntegral.integral_const_mul] at h
  have hb : (fun θ ↦ (2 * I)⁻¹ * (circleMap 0 r θ * I * (g (circleMap c r θ) *
      ξ (circleMap c r θ)))) = fun θ ↦ (2 : ℂ)⁻¹ *
        (circleMap 0 r θ * g (circleMap c r θ) * ξ (circleMap c r θ)) := by
    funext θ
    field_simp
  rw [hb, intervalIntegral.integral_const_mul] at h
  have hre := congrArg re h
  rw [add_re, ← integral_re_eq hA, ← integral_re_eq hB,
    show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl, re_ofReal_mul,
    ← intervalIntegral_re_eq (hcont.intervalIntegrable (-π) π)] at hre
  linarith

/-- **Green's formula for a holomorphic factor.** If `g` is holomorphic on the open disc
`|z - c| < R` and continuous on its closure, and `ξ` is real `C¹` near the closed disc, then
`∫_{|z - c| < R} g \bar∂ξ dA = (2 i)⁻¹ ∮_{|z - c| = R} g ξ dz`. The area term `ξ \bar∂g` of
Green's formula is absent, and `g` need not be differentiable on the boundary circle: the formula
is the limit of Green's formula on the discs of radius `r < R`. -/
theorem integral_ball_mul_conjWirtingerDeriv_eq_circleIntegral_of_diffContOnCl {R : ℝ}
    (hR : 0 < R) (hg : DiffContOnCl ℂ g (ball c R))
    (hξ : ∀ z ∈ closedBall c R, ContDiffAt ℝ 1 ξ z) :
    ∫ z in ball c R, g z * conjWirtingerDeriv ξ z 1 = (2 * I)⁻¹ * ∮ z in C(c, R), g z * ξ z := by
  have hgc : ContinuousOn g (closedBall c R) := by
    simpa [closure_ball c hR.ne'] using hg.continuousOn
  have hξc : ContinuousOn ξ (closedBall c R) :=
    continuousOn_of_forall_continuousAt fun z hz ↦ (hξ z hz).continuousAt
  set F : ℂ → ℂ := fun z ↦ g z * conjWirtingerDeriv ξ z 1 with hF
  have hFi : IntegrableOn F (ball c R) :=
    ((hgc.mul (continuousOn_of_forall_continuousAt fun z hz ↦
      continuousAt_conjWirtingerDeriv (hξ z hz))).integrableOn_compact
        (isCompact_closedBall c R)).mono_set ball_subset_closedBall
  -- Green's formula on the smaller discs.
  have hsmall : ∀ r ∈ Ioo 0 R,
      ∫ z in ball c r, F z = (2 * I)⁻¹ * ∮ z in C(c, r), g z * ξ z := by
    intro r hr
    have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hr.2
    have hgr : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 g z := fun z hz ↦
      ((hg.differentiableOn.contDiffOn isOpen_ball).contDiffAt
        (isOpen_ball.mem_nhds (hsub hz))).restrict_scalars ℝ
    rw [← integral_ball_mul_conjWirtingerDeriv_add_eq_circleIntegral hr.1.le hgr
      fun z hz ↦ hξ z (closedBall_subset_closedBall hr.2.le hz)]
    refine setIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_
    have hd : DifferentiableAt ℂ g z :=
      hg.differentiableAt isOpen_ball (ball_subset_ball hr.2.le hz)
    simp [hF, hd.conjWirtingerDeriv_eq_zero]
  -- The area integrals converge by dominated convergence.
  have harea : Tendsto (fun r ↦ ∫ z in ball c r, F z) (𝓝[<] R) (𝓝 (∫ z in ball c R, F z)) := by
    simp_rw [← integral_indicator measurableSet_ball]
    refine tendsto_integral_filter_of_dominated_convergence
      ((ball c R).indicator fun z ↦ ‖F z‖) ?_ ?_
      (IntegrableOn.integrable_indicator hFi.norm measurableSet_ball) ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact ((hFi.mono_set (ball_subset_ball (le_of_lt hr))).integrable_indicator
        measurableSet_ball).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with r hr
      refine Eventually.of_forall fun z ↦ ?_
      rw [norm_indicator_eq_indicator_norm]
      exact indicator_le_indicator_of_subset (ball_subset_ball (le_of_lt hr))
        (fun _ ↦ norm_nonneg _) z
    · refine Eventually.of_forall fun z ↦ ?_
      by_cases hz : z ∈ ball c R
      · rw [indicator_of_mem hz]
        refine tendsto_const_nhds.congr' ?_
        have : dist z c < R := hz
        filter_upwards [Ioo_mem_nhdsLT this] with r hr
        rw [indicator_of_mem (show dist z c < r from hr.1)]
      · rw [indicator_of_notMem hz]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with r hr
        rw [indicator_of_notMem fun h ↦ hz (ball_subset_ball (le_of_lt hr) h)]
  -- The circle integrals converge by continuity of the clamped parametric integral.
  have hcirc : Tendsto (fun r ↦ ∮ z in C(c, r), g z * ξ z) (𝓝[<] R)
      (𝓝 (∮ z in C(c, R), g z * ξ z)) := by
    set ρ : ℝ → ℝ := fun r ↦ max 0 (min r R) with hρ
    have hρc : Continuous ρ := by fun_prop
    have hρR : ρ R = R := by simp [hρ, hR.le]
    have hmem (r θ : ℝ) : circleMap c (ρ r) θ ∈ closedBall c R := by
      rw [mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
        abs_of_nonneg (le_max_left _ _)]
      exact max_le hR.le (min_le_right _ _)
    have hG : Continuous fun p : ℝ × ℝ ↦
        deriv (circleMap c (ρ p.1)) p.2 • (g (circleMap c (ρ p.1) p.2) *
          ξ (circleMap c (ρ p.1) p.2)) := by
      simp only [deriv_circleMap, smul_eq_mul]
      have hcm : Continuous fun p : ℝ × ℝ ↦ circleMap c (ρ p.1) p.2 := by
        unfold circleMap
        fun_prop
      have hcm0 : Continuous fun p : ℝ × ℝ ↦ circleMap 0 (ρ p.1) p.2 := by
        unfold circleMap
        fun_prop
      exact (hcm0.mul continuous_const).mul ((hgc.mul hξc).comp_continuous hcm
        fun p ↦ hmem p.1 p.2)
    have hcont : Continuous fun r ↦ ∮ z in C(c, ρ r), g z * ξ z :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hG 0 (2 * π)
    have := (hcont.tendsto R).mono_left (nhdsWithin_le_nhds (s := Iio R))
    rw [hρR] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hR] with r hr
    simp [hρ, hr.1.le, hr.2.le]
  exact tendsto_nhds_unique_of_eventuallyEq harea (hcirc.const_mul _)
    (by filter_upwards [Ioo_mem_nhdsLT hR] with r hr using hsmall r hr)

/-! ### The dual boundary condition on the unit circle -/

section Boundary

variable {k : ℤ} {w : ℂ}

private theorem conj_zpow_mul_zpow (hw : ‖w‖ = 1) : conj (w ^ k) * w ^ k = 1 := by
  rw [conj_mul', norm_zpow, hw, one_zpow]
  norm_num

/-- The adjoint boundary condition, solved for `conj w * conj c`. -/
private theorem adjoint_boundary_iff' (c : ℂ) :
    -I * conj w * conj c = w ^ k * conj (-I * conj w * conj c) ↔
      conj w * conj c = -(w ^ k * w * c) := by
  simp only [map_mul, map_neg, conj_I, conj_conj]
  constructor
  · intro h
    linear_combination I * h + (conj w * conj c + w ^ k * w * c) * I_sq
  · intro h
    linear_combination (-I) * h

/-- **The boundary term vanishes.** At a point `w` of the unit circle, if `c` satisfies the
adjoint boundary condition of index `k` and `v` lies on the line `v = w ^ k * conj v`, then
`w c v` is purely imaginary. -/
theorem re_mul_mul_eq_zero_of_adjoint_boundary (hw : ‖w‖ = 1) {c v : ℂ}
    (hc : -I * conj w * conj c = w ^ k * conj (-I * conj w * conj c))
    (hv : v = w ^ k * conj v) : (w * c * v).re = 0 := by
  rw [adjoint_boundary_iff'] at hc
  have ep := conj_zpow_mul_zpow (k := k) hw
  have hv' : conj v = conj (w ^ k) * v := by
    conv_lhs => rw [hv]
    rw [map_mul, conj_conj]
  have h : w * c * v + conj (w * c * v) = 0 := by
    simp only [map_mul]
    linear_combination conj v * hc - (w ^ k * w * c) * hv' - (w * c * v) * ep
  rw [add_conj, ofReal_eq_zero] at h
  linarith

/-- **The dual boundary condition is forced.** At a point `w` of the unit circle, `c` satisfies
the adjoint boundary condition of index `k` exactly when `Re (w c v) = 0` for every `v` on the line
`v = w ^ k * conj v`. So the adjoint condition of `TauCeti.unitDiscAdjointKernel` is the boundary
condition that makes the boundary term of Green's formula vanish for every admissible `ξ`; this
is the disc analogue of the half-plane condition `η(∂_s) ∈ ℝⁿ`. -/
theorem adjoint_boundary_iff_forall_re_mul_eq_zero (hw : ‖w‖ = 1) (c : ℂ) :
    -I * conj w * conj c = w ^ k * conj (-I * conj w * conj c) ↔
      ∀ v, v = w ^ k * conj v → (w * c * v).re = 0 := by
  refine ⟨fun hc v hv ↦ re_mul_mul_eq_zero_of_adjoint_boundary hw hc hv, fun H ↦ ?_⟩
  have ep := conj_zpow_mul_zpow (k := k) hw
  rw [adjoint_boundary_iff']
  -- `D = w ^ k * (w * c) + conj (w * c)` lies on the line, and `D * conj D = 2 Re (w c D)`.
  set D := w ^ k * (w * c) + conj (w * c) with hD
  have hDl : D = w ^ k * conj D := by
    simp only [hD, map_add, map_mul, conj_conj]
    linear_combination (-(conj w * conj c)) * ep
  have h0 := H D hDl
  have h2 : D * conj D = w * c * D + conj (w * c * D) := by
    simp only [hD, map_add, map_mul, conj_conj]
    linear_combination (w * c * conj w * conj c) * ep
  rw [add_conj, h0, mul_zero, mul_conj] at h2
  have hD0 : D = 0 := normSq_eq_zero.1 (by exact_mod_cast h2)
  simp only [hD, map_mul] at hD0
  linear_combination hD0

end Boundary

/-! ### Orthogonality of the adjoint solutions to the image of `\bar∂` -/

/-- **Adjoint solutions are orthogonal to the image of `\bar∂`.** Let `ξ` be real `C¹` near the
closed unit disc with boundary values on the rotating line `w ^ (k / 2) ℝ`, that is
`ξ w = w ^ k * conj (ξ w)` for `‖w‖ = 1`, and let `u` restrict on the closed disc to an adjoint
solution of index `k`. Then `∫_{|z| < 1} Re (u \bar∂ξ) dA = 0`. This is one direction of the
duality (C.1.3) of McDuff–Salamon on the disc model: the form `conj u d(conj z)` is
`L²`-orthogonal to `\bar∂ξ d(conj z)`. -/
theorem integral_ball_re_mul_conjWirtingerDeriv_eq_zero_of_mem_unitDiscAdjointKernel {k : ℤ}
    {u : ℂ → ℂ} (hu : (closedBall (0 : ℂ) 1).domRestrict u ∈ unitDiscAdjointKernel k)
    (hξ : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 1 ξ z)
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, ξ w = w ^ k * conj (ξ w)) :
    ∫ z in ball (0 : ℂ) 1, (u z * conjWirtingerDeriv ξ z 1).re = 0 := by
  obtain ⟨u', hu', hbu', hres⟩ := mem_unitDiscAdjointKernel_iff.1 hu
  have heq : ∀ z ∈ closedBall (0 : ℂ) 1, u z = u' z := fun z hz ↦
    (congrFun hres ⟨z, hz⟩).symm
  have hu'c : ContinuousOn u' (closedBall 0 1) := by
    simpa [closure_ball (0 : ℂ) one_ne_zero] using hu'.continuousOn
  have hFi : IntegrableOn (fun z ↦ u' z * conjWirtingerDeriv ξ z 1) (ball 0 1) :=
    ((hu'c.mul (continuousOn_of_forall_continuousAt fun z hz ↦
      continuousAt_conjWirtingerDeriv (hξ z hz))).integrableOn_compact
        (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  rw [setIntegral_congr_fun measurableSet_ball fun z hz ↦ by
      rw [heq z (ball_subset_closedBall hz)],
    integral_re_eq hFi,
    integral_ball_mul_conjWirtingerDeriv_eq_circleIntegral_of_diffContOnCl one_pos hu' hξ,
    ← integral_neg_pi_pi_eq_circleIntegral, ← intervalIntegral.integral_const_mul]
  -- Pointwise on the circle the integrand is purely imaginary.
  have hpt (θ : ℝ) : (2 * I)⁻¹ * (circleMap 0 1 θ * I * (u' (circleMap 0 1 θ) *
      ξ (circleMap 0 1 θ))) =
        ((2⁻¹ * (circleMap 0 1 θ * u' (circleMap 0 1 θ) * ξ (circleMap 0 1 θ)).im : ℝ) : ℂ) *
          I := by
    have hw : ‖circleMap 0 1 θ‖ = 1 := by simp
    have hre := re_mul_mul_eq_zero_of_adjoint_boundary hw
      (hbu' _ (by simp)) (hb _ (by simp))
    set x := circleMap 0 1 θ * u' (circleMap 0 1 θ) * ξ (circleMap 0 1 θ) with hx
    have hx' : x = (x.im : ℂ) * I := by
      conv_lhs => rw [← re_add_im x, hre]
      simp
    have h2I : (2 * I)⁻¹ * (circleMap 0 1 θ * I * (u' (circleMap 0 1 θ) *
        ξ (circleMap 0 1 θ))) = 2⁻¹ * x := by
      rw [hx]
      field_simp
    rw [h2I]
    conv_lhs => rw [hx']
    push_cast
    ring
  simp_rw [hpt, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  simp

/-! ### Checks -/

/-- **Check: the adjoint solutions for `k = -2`.** For the boundary condition of index `-2` the
adjoint problem is the problem of index `0` for `I g`, whose solutions are the real constants, so
the adjoint solutions are the real multiples of the constant `-I`. -/
theorem unitDiscAdjointKernel_neg_two :
    unitDiscAdjointKernel (-2) = ℝ ∙ (fun _ : closedBall (0 : ℂ) 1 ↦ -I) := by
  have hmem : (fun _ : closedBall (0 : ℂ) 1 ↦ -I) ∈ unitDiscAdjointKernel (-2) := by
    refine mem_unitDiscAdjointKernel_iff.2 ⟨fun _ ↦ -I, diffContOnCl_const, fun w hw ↦ ?_, rfl⟩
    have hw : ‖w‖ = 1 := by simpa using hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    have e : conj w * w = 1 := by
      rw [conj_mul', hw]
      norm_num
    simp only [map_mul, map_neg, conj_I, conj_conj, zpow_neg, zpow_ofNat]
    field_simp
    linear_combination -e
  have hne : (fun _ : closedBall (0 : ℂ) 1 ↦ -I) ≠ 0 := fun h ↦ by
    simpa using congrFun h ⟨0, by simp⟩
  refine (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hmem)
    ?_).symm
  rw [finrank_span_singleton hne, finrank_unitDiscAdjointKernel]
  rfl

/-- **Check: orthogonality for `k = -2`.** For `ξ` real `C¹` near the closed unit disc with
`ξ w = w ^ (-2) * conj (ξ w)` on the circle, `∫_{|z| < 1} Im (\bar∂ξ) dA = 0`: the pairing of
`\bar∂ξ` with the adjoint solution `-I` of `TauCeti.unitDiscAdjointKernel_neg_two`. -/
theorem integral_ball_im_conjWirtingerDeriv_eq_zero_of_eq_zpow_neg_two_mul_conj
    (hξ : ∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 1 ξ z)
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, ξ w = w ^ (-2 : ℤ) * conj (ξ w)) :
    ∫ z in ball (0 : ℂ) 1, (conjWirtingerDeriv ξ z 1).im = 0 := by
  have h := integral_ball_re_mul_conjWirtingerDeriv_eq_zero_of_mem_unitDiscAdjointKernel
    (u := fun _ ↦ -I)
    (by rw [unitDiscAdjointKernel_neg_two]; exact Submodule.mem_span_singleton_self _) hξ hb
  simpa using h

/-- The integral over the unit disc of `\bar∂` of `ξ z = Re z`: since `\bar∂ (Re z) = ½`, it is
half the area `π`. -/
theorem integral_ball_re_conjWirtingerDeriv_ofReal_re :
    ∫ z in ball (0 : ℂ) 1, (conjWirtingerDeriv (fun z : ℂ ↦ (z.re : ℂ)) z 1).re = π / 2 := by
  have h (z : ℂ) : conjWirtingerDeriv (fun z : ℂ ↦ (z.re : ℂ)) z 1 = 2⁻¹ := by
    rw [conjWirtingerDeriv_apply,
      show (fun z : ℂ ↦ (z.re : ℂ)) = ⇑(ofRealCLM.comp reCLM : ℂ →L[ℝ] ℂ) from rfl,
      (ofRealCLM.comp reCLM).fderiv]
    simp
  simp only [h, setIntegral_const]
  simp [Measure.real]
  ring

/-- **Check: the unshifted condition is not the dual one.** The plausible dual condition
`g ∈ unitDiscCauchyRiemannKernel k`, without the shift `k ↦ -k - 2`, does not make the pairing
vanish: for `k = 0`, the real constant `g = 1` is a solution, `ξ z = Re z` is real on the circle,
and `∫_{|z| < 1} Re (g \bar∂ξ) dA = π / 2 ≠ 0`. -/
theorem exists_mem_unitDiscCauchyRiemannKernel_integral_ball_re_mul_ne_zero :
    ∃ u ξ : ℂ → ℂ, (closedBall (0 : ℂ) 1).domRestrict u ∈ unitDiscCauchyRiemannKernel 0 ∧
      (∀ z ∈ closedBall (0 : ℂ) 1, ContDiffAt ℝ 1 ξ z) ∧
      (∀ w ∈ sphere (0 : ℂ) 1, ξ w = w ^ (0 : ℤ) * conj (ξ w)) ∧
      ∫ z in ball (0 : ℂ) 1, (u z * conjWirtingerDeriv ξ z 1).re ≠ 0 := by
  refine ⟨fun _ ↦ 1, fun z ↦ (z.re : ℂ), mem_unitDiscCauchyRiemannKernel_iff.2
    ⟨fun _ ↦ 1, diffContOnCl_const, fun w _ ↦ by simp, rfl⟩,
    fun z _ ↦ (ofRealCLM.comp reCLM).contDiff.contDiffAt, fun w _ ↦ by simp, ?_⟩
  simp only [one_mul, integral_ball_re_conjWirtingerDeriv_ofReal_re]
  positivity

end TauCeti
