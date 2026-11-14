/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
import TauCeti.MeasureTheory.Integral.Circle.Integral
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.InterBall
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Green's formula for `\bar∂` on a disc

For a function `h` with values in a complex Banach space `E` that is real `C¹` near a closed disc
`|z - c| ≤ r`, Stokes' formula for the one-form `h dz`, whose exterior derivative is
`d(h dz) = 2 i \bar∂h dA`, gives

`∫_{|z - c| < r} \bar∂h dA = (2 i)⁻¹ ∮_{|z - c| = r} h dz`.

Applied to `h = g ξ`, with `g` complex-valued, it gives **Green's formula for `\bar∂` with
boundary term**

`∫_{|z - c| < r} (g \bar∂ξ + (\bar∂g) ξ) dA = (2 i)⁻¹ ∮_{|z - c| = r} g ξ dz`.

For complex-valued `ξ` its real part is the integration by parts behind McDuff–Salamon
Lemma C.1.9 on the disc:

`∫ Re (g \bar∂ξ) = -∫ Re (ξ \bar∂g) + ½ ∫_{-π}^{π} Re (r e^{iθ} g ξ)(c + r e^{iθ}) dθ`.

For `g` holomorphic on the open disc and continuous up to the boundary the area term in `g`
vanishes, and a limit `r → R` removes the need for regularity of `g` on the boundary circle.

## Main results

* `TauCeti.integral_ball_conjWirtingerDeriv_eq_circleIntegral`:
  `∫_{|z - c| < r} \bar∂h dA = (2 i)⁻¹ ∮_{|z - c| = r} h dz` for `h` real `C¹` near the closed
  disc.
* `TauCeti.integral_ball_smul_conjWirtingerDeriv_add_eq_circleIntegral`: Green's formula for the
  product `g ξ`.
* `TauCeti.integral_ball_re_mul_conjWirtingerDeriv_eq`: its real form for complex-valued `ξ`,
  with the boundary term written in the angle.
* `TauCeti.integral_ball_smul_conjWirtingerDeriv_eq_circleIntegral_of_diffContOnCl`: Green's
  formula for `g` holomorphic on the open disc and continuous on its closure.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (Lemma C.1.9).
-/

public section

namespace TauCeti

open Complex Metric MeasureTheory Set Filter Topology
open scoped Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The one-form `h dz` on the plane, `v ↦ v • h z`. -/
private noncomputable def dzForm (h : ℂ → E) : ℂ → ℂ [⋀^Fin 1]→L[ℝ] E :=
  fun z ↦ ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).toContinuousLinearEquiv
    |>.toContinuousLinearMap.comp (ContinuousLinearMap.lsmul ℝ ℂ).flip) (h z)

private theorem dzForm_apply (h : ℂ → E) (z : ℂ) (v : Fin 1 → ℂ) :
    dzForm h z v = v 0 • h z := by
  simp [dzForm, ContinuousAlternatingMap.ofSubsingletonLIE]

private theorem contDiffAt_dzForm {h : ℂ → E} {z : ℂ} (hh : ContDiffAt ℝ 1 h z) :
    ContDiffAt ℝ 1 (dzForm h) z :=
  (ContinuousLinearMap.contDiff _).contDiffAt.comp z hh

/-- The exterior derivative of `h dz` on the frame `(1, I)` is `2 i \bar∂h`. -/
private theorem extDeriv_dzForm {h : ℂ → E} {z : ℂ} (hh : ContDiffAt ℝ 1 h z) :
    extDeriv (dzForm h) z ![1, I] = (2 * I) • conjWirtingerDeriv h z 1 := by
  rw [extDeriv_apply ((contDiffAt_dzForm hh).differentiableAt one_ne_zero)]
  have hh' : DifferentiableAt ℝ h z := hh.differentiableAt one_ne_zero
  rw [conjWirtingerDeriv_apply, smul_smul, show (2 : ℂ) * I * 2⁻¹ = I by ring, smul_add, smul_smul,
    I_mul_I, neg_one_smul]
  simp [dzForm_apply, Fin.sum_univ_succ, Fin.removeNth, fderiv_fun_const_smul hh']

/-- **Stokes' formula for `\bar∂` on a disc.** For `h` real `C¹` near the closed disc
`|z - c| ≤ r`, `∫_{|z - c| < r} \bar∂h dA = (2 i)⁻¹ ∮_{|z - c| = r} h dz`. -/
theorem integral_ball_conjWirtingerDeriv_eq_circleIntegral {h : ℂ → E} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hh : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 h z) :
    ∫ z in ball c r, conjWirtingerDeriv h z 1 = (2 * I)⁻¹ • ∮ z in C(c, r), h z := by
  have hs := integral_extDeriv_closedBall hr fun z hz ↦ contDiffAt_dzForm (hh z hz)
  rw [setIntegral_congr_fun measurableSet_closedBall fun z hz ↦ extDeriv_dzForm (hh z hz),
    integral_smul, setIntegral_congr_set (volume.addHaar_closedBall_ae_eq_ball c r)] at hs
  simp only [dzForm_apply] at hs
  rw [integral_neg_pi_pi_eq_circleIntegral] at hs
  rw [← hs, smul_smul, inv_mul_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero), one_smul]

section Product

variable {g : ℂ → ℂ} {ξ : ℂ → E} {c : ℂ} {r : ℝ}

/-- **Green's formula for `\bar∂` with boundary term.** For `g` and `ξ` real `C¹` near the
closed disc `|z - c| ≤ r`, with `g` complex-valued,
`∫_{|z - c| < r} (g \bar∂ξ + (\bar∂g) ξ) dA = (2 i)⁻¹ ∮_{|z - c| = r} g ξ dz`. -/
theorem integral_ball_smul_conjWirtingerDeriv_add_eq_circleIntegral (hr : 0 ≤ r)
    (hg : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 g z)
    (hξ : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 ξ z) :
    ∫ z in ball c r, (g z • conjWirtingerDeriv ξ z 1 + conjWirtingerDeriv g z 1 • ξ z) =
      (2 * I)⁻¹ • ∮ z in C(c, r), g z • ξ z := by
  rw [← integral_ball_conjWirtingerDeriv_eq_circleIntegral (h := fun z ↦ g z • ξ z) hr
    fun z hz ↦ (hg z hz).smul (hξ z hz)]
  refine setIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_
  have hz' := ball_subset_closedBall hz
  exact (conjWirtingerDeriv_smul_apply ((hg z hz').differentiableAt one_ne_zero)
    ((hξ z hz').differentiableAt one_ne_zero) 1).symm

/-- For `g` continuous on the closed disc `|z - c| ≤ r` and `ξ` real `C¹` near it, the product
`g \bar∂ξ` is integrable on the open disc. -/
theorem integrableOn_ball_smul_conjWirtingerDeriv (hg : ContinuousOn g (closedBall c r))
    (hξ : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 ξ z) :
    IntegrableOn (fun z ↦ g z • conjWirtingerDeriv ξ z 1) (ball c r) :=
  ((hg.smul (continuousOn_of_forall_continuousAt fun z hz ↦
    ((hξ z hz).conjWirtingerDeriv_apply (m := 0) (by simp) 1).continuousAt)).integrableOn_compact
      (isCompact_closedBall c r)).mono_set ball_subset_closedBall

/-- **Green's formula for a holomorphic factor.** If `g` is holomorphic on the open disc
`|z - c| < R` and continuous on its closure, and `ξ` is real `C¹` near the closed disc, then
`∫_{|z - c| < R} g \bar∂ξ dA = (2 i)⁻¹ ∮_{|z - c| = R} g ξ dz`. The area term `(\bar∂g) ξ` of
Green's formula is absent, and `g` need not be differentiable on the boundary circle: the formula
is the limit of Green's formula on the discs of radius `r < R`. -/
theorem integral_ball_smul_conjWirtingerDeriv_eq_circleIntegral_of_diffContOnCl {R : ℝ}
    (hR : 0 < R) (hg : DiffContOnCl ℂ g (ball c R))
    (hξ : ∀ z ∈ closedBall c R, ContDiffAt ℝ 1 ξ z) :
    ∫ z in ball c R, g z • conjWirtingerDeriv ξ z 1 = (2 * I)⁻¹ • ∮ z in C(c, R), g z • ξ z := by
  have hgc : ContinuousOn g (closedBall c R) := by
    simpa [closure_ball c hR.ne'] using hg.continuousOn
  have hξc : ContinuousOn ξ (closedBall c R) :=
    continuousOn_of_forall_continuousAt fun z hz ↦ (hξ z hz).continuousAt
  -- Green's formula on the smaller discs, where `g` is `C¹` and `\bar∂g = 0`.
  have hsmall : ∀ r ∈ Ioo 0 R,
      ∫ z in ball c r, g z • conjWirtingerDeriv ξ z 1 = (2 * I)⁻¹ • ∮ z in C(c, r), g z • ξ z := by
    intro r hr
    have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hr.2
    have hgr : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 g z := fun z hz ↦
      ((hg.differentiableOn.contDiffOn isOpen_ball).contDiffAt
        (isOpen_ball.mem_nhds (hsub hz))).restrict_scalars ℝ
    rw [← integral_ball_smul_conjWirtingerDeriv_add_eq_circleIntegral hr.1.le hgr
      fun z hz ↦ hξ z (closedBall_subset_closedBall hr.2.le hz)]
    refine setIntegral_congr_fun measurableSet_ball fun z hz ↦ ?_
    have hd : DifferentiableAt ℂ g z :=
      hg.differentiableAt isOpen_ball (ball_subset_ball hr.2.le hz)
    simp [hd.conjWirtingerDeriv_eq_zero]
  -- Both sides converge as `r → R⁻`.
  have hcirc : Tendsto (fun r ↦ ∮ z in C(c, r), g z • ξ z) (𝓝[<] R)
      (𝓝 (∮ z in C(c, R), g z • ξ z)) :=
    (ContinuousOn.continuousOn_circleIntegral (f := fun z ↦ g z • ξ z) (hgc.smul hξc) R
      ⟨hR.le, le_rfl⟩).tendsto.mono_left
      (nhdsWithin_le_of_mem (mem_of_superset (Ioo_mem_nhdsLT hR) Ioo_subset_Icc_self))
  exact tendsto_nhds_unique_of_eventuallyEq
    (IntegrableOn.tendsto_integral_ball_nhdsLT
      (integrableOn_ball_smul_conjWirtingerDeriv hgc hξ))
    (hcirc.const_smul _) (by filter_upwards [Ioo_mem_nhdsLT hR] with r hr using hsmall r hr)

end Product

section Scalar

variable {g ξ : ℂ → ℂ} {c : ℂ} {r : ℝ}

/-- **Green's formula, real form.** For complex-valued `g` and `ξ` real `C¹` near the closed disc
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
  have hcont (f : ℂ → ℂ) (hf : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 f z) :
      ContinuousOn f (closedBall c r) :=
    continuousOn_of_forall_continuousAt fun z hz ↦ (hf z hz).continuousAt
  have hA := integrableOn_ball_smul_conjWirtingerDeriv (hcont g hg) hξ
  have hB := integrableOn_ball_smul_conjWirtingerDeriv (hcont ξ hξ) hg
  simp only [smul_eq_mul] at hA hB
  have hcm (f : ℂ → ℂ) (hf : ∀ z ∈ closedBall c r, ContDiffAt ℝ 1 f z) :
      Continuous fun θ ↦ f (circleMap c r θ) :=
    (hcont f hf).comp_continuous (continuous_circleMap c r) fun θ ↦ circleMap_mem_closedBall c hr θ
  have hb : Continuous fun θ ↦ circleMap 0 r θ * g (circleMap c r θ) * ξ (circleMap c r θ) :=
    ((continuous_circleMap 0 r).mul (hcm g hg)).mul (hcm ξ hξ)
  have h := integral_ball_smul_conjWirtingerDeriv_add_eq_circleIntegral hr hg hξ
  rw [setIntegral_congr_fun measurableSet_ball fun z _ ↦ by
      rw [smul_eq_mul, smul_eq_mul, mul_comm (conjWirtingerDeriv g z 1)],
    integral_add hA hB, ← integral_neg_pi_pi_eq_circleIntegral,
    ← intervalIntegral.integral_smul] at h
  have hbθ : (fun θ ↦ (2 * I)⁻¹ • (circleMap 0 r θ * I) • (g (circleMap c r θ) •
      ξ (circleMap c r θ))) = fun θ ↦ (2 : ℂ)⁻¹ *
        (circleMap 0 r θ * g (circleMap c r θ) * ξ (circleMap c r θ)) := by
    funext θ
    simp only [smul_eq_mul]
    field_simp
  rw [hbθ, intervalIntegral.integral_const_mul] at h
  have hre := congrArg re h
  have hreA := integral_re hA
  have hreB := integral_re hB
  have hreb := intervalIntegral.intervalIntegral_re (hb.intervalIntegrable (μ := volume) (-π) π)
  simp only [RCLike.re_to_complex] at hreA hreB hreb
  rw [add_re, ← hreA, ← hreB, show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl, re_ofReal_mul,
    ← hreb] at hre
  linarith

end Scalar

end TauCeti
