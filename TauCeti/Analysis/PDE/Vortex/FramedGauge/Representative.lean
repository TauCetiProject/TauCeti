/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Smooth framed vortices in the affine Sobolev field space

A plane vortex `x` whose section is normalized at its end — equal outside a compact set to `|α|`
times the winding phase `(z / |z|)^m` — has real positive section `|α| = exp ((1 / 2) log |α|²)` in
the winding-`m` end trivialization. Away from the zeros of `α`, the holomorphicity equation
`∂bar_a α = 0` expresses the connection of the end trivialization as `(-∂₂ L, ∂₁ L)` where
`L = (1 / 2) log |α|²` (`TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_zero`,
`TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_one`), while outside the cutoff disc of
`referenceField f m` the reference field becomes the vacuum. Hence outside a ball the
end-trivialized defect `gaugeTransform (windingPhase m)⁻¹ x - vacuumField` has coordinates
`(-∂₂ L, ∂₁ L, (exp L - 1) / 2, 0)` and the field defect `x - referenceField f m` has coordinates

`(-∂₂ L, ∂₁ L, (exp L - 1) (x_ref)₂, (exp L - 1) (x_ref)₃)`.

Every iterated derivative of `log |α|²` is `O(exp (-c |z|))` at infinity for every `c < 1 / 2`
(`TauCeti.Vortex.isBigO_iteratedFDeriv_log_normSq`), and every iterated derivative of
`referenceField f m` is globally bounded
(`TauCeti.Vortex.exists_norm_iteratedFDeriv_referenceField_apply_le`). Differentiating the exterior
formulas therefore gives exponential decay at infinity of all iterated derivatives of both
`gaugeTransform (windingPhase m)⁻¹ x - vacuumField`
(`TauCeti.Vortex.isBigO_iteratedFDeriv_gaugeTransform_inv_windingPhase_sub_vacuumField`) and
`x - referenceField f m` (`TauCeti.Vortex.isBigO_iteratedFDeriv_sub_referenceField`,
`TauCeti.Vortex.exists_norm_iteratedFDeriv_sub_referenceField_le_mul_exp`).

When `x` is smooth, each coordinate of `x - referenceField f m` lies in `realSobolevFunctions` by
`TemperedDistribution.mem_realSobolevFunctions_of_isBigO_iteratedFDeriv_exp`, so `x` belongs to the
affine Sobolev model `framedFieldSpace f m s` at every real order `s`
(`TauCeti.Vortex.mem_framedFieldSpace_of_sectionValue_eq_mul_windingPhase`). Combining with the
end-phase normalization `TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq` shows that
every smooth degree-`m` framed plane vortex has a smooth framed gauge transform lying in
`framedFieldSpace f m s` for every `f` and `s`, with exponential decay of all iterated derivatives
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace_norm_iteratedFDeriv_le_mul_exp`).
Note that the normalizing smooth framed gauge need only tend to `1` at infinity (for instance with a
`1 / |z|` tail) and need not itself lie in a Sobolev gauge group; only the normalized representative
lies in `A_m^s`.

## Main results

* `TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_zero`,
  `TauCeti.Vortex.gaugeTransform_inv_windingPhase_apply_one`: the connection coordinates
  `(-(1 / 2) ∂₂(log |α|²), (1 / 2) ∂₁(log |α|²))` of the winding-`m` end trivialization where
  `∂bar_a α = 0` and the section is `|α|` times `windingPhase m`.
* `TauCeti.Vortex.isBigO_iteratedFDeriv_gaugeTransform_inv_windingPhase_sub_vacuumField_apply`,
  `TauCeti.Vortex.isBigO_iteratedFDeriv_gaugeTransform_inv_windingPhase_sub_vacuumField`: for a
  vortex with smooth section, `|α| → 1`, and end-normalized phase outside a compact set, every
  iterated derivative of `gaugeTransform (windingPhase m)⁻¹ x - vacuumField` is `O(exp (-c |z|))` at
  infinity for all `c < 1 / 2`.
* `TauCeti.Vortex.isBigO_iteratedFDeriv_sub_referenceField_apply`,
  `TauCeti.Vortex.isBigO_iteratedFDeriv_sub_referenceField`: the corresponding `O(exp (-c |z|))`
  derivative decay for `x - referenceField f m`.
* `TauCeti.Vortex.exists_norm_iteratedFDeriv_sub_referenceField_le_mul_exp`: when `x` is smooth,
  `‖Dⁿ(x - referenceField f m)(z)‖ ≤ K exp (-c |z|)` on the whole plane.
* `TauCeti.Vortex.mem_framedFieldSpace_of_sectionValue_eq_mul_windingPhase`: a smooth
  end-normalized vortex lies in `framedFieldSpace f m s` for every cutoff `f` and order `s : ℝ`.
* `TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace_norm_iteratedFDeriv_le_mul_exp`:
  every smooth framed degree-`m` vortex has a smooth framed gauge representative lying in
  `framedFieldSpace f m s` for all `f` and `s` whose difference from `referenceField f m` decays
  exponentially with all derivatives.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Asymptotics Complex ComplexConjugate Filter Metric
open scoped ContDiff Topology

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {m : ℕ}

/-! ### Exterior coordinate formulas in the end trivialization -/

/-- Shared proof of `gaugeTransform_inv_windingPhase_apply_zero` and
`gaugeTransform_inv_windingPhase_apply_one`. -/
private theorem gaugeTransform_inv_windingPhase_apply_zero_and_one {z : ℂ} (hz : z ≠ 0)
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w) :
    gaugeTransform (windingPhase m)⁻¹ x z 0 =
        -(1 / 2) * fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z I ∧
      gaugeTransform (windingPhase m)⁻¹ x z 1 =
        (1 / 2) * fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z 1 := by
  set ℓ : ℂ → ℝ := fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))
  set u : ℂ → Circle := (windingPhase m)⁻¹
  set y : ℂ → EuclideanSpace ℝ (Fin 4) := gaugeTransform u x
  have hu : ContDiffAt ℝ 2 (fun w ↦ (u w : ℂ)) z := by
    simpa only [u, Pi.inv_apply, Circle.coe_inv_eq_conj, Function.comp_def, conjCLE_apply] using
      conjCLE.contDiff.contDiffAt.comp z (contDiffAt_windingPhase m hz)
  have hu1 : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z := hu.differentiableAt two_ne_zero
  -- In the end trivialization `y`, the section is real on `𝓝 z`, so `y · 3` vanishes near `z`.
  have hy3_nhds : (fun w ↦ y w 3) =ᶠ[𝓝 z] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hphase] with w hw
    have him := congrArg Complex.im
      (sectionValue_apply y w ▸ sectionValue_gaugeTransform_inv_windingPhase hw)
    simp only [mul_im, add_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at him
    linarith
  have hy3 : y z 3 = 0 := hy3_nhds.eq_of_nhds
  have hdy3 : fderiv ℝ (fun w ↦ y w 3) z = 0 := by simpa using hy3_nhds.fderiv_eq
  have hyp : DifferentiableAt ℝ (fun w ↦ y w 2) z := by
    simp only [y, gaugeTransform_apply, PiLp.toLp_apply, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    exact ((reCLM.differentiableAt.comp z hu1).mul hp).sub
      ((imCLM.differentiableAt.comp z hu1).mul hq)
  have hyq : DifferentiableAt ℝ (fun w ↦ y w 3) z :=
    (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hy3_nhds
  -- Gauge covariance of `∂bar_a α` gives `equation y z 1 = 0` and `equation y z 2 = 0` at `z`.
  have hdbar : 2 * ((equation y z 1 : ℂ) + (equation y z 2 : ℂ) * I) = 0 := by
    calc 2 * ((equation y z 1 : ℂ) + (equation y z 2 : ℂ) * I)
        = covariantDerivative y z 1 + I * covariantDerivative y z I :=
          (covariantDerivative_one_add_I_mul_covariantDerivative_I hyp hyq).symm
      _ = (u z : ℂ) * (covariantDerivative x z 1 + I * covariantDerivative x z I) := by
          rw [covariantDerivative_gaugeTransform hu1 hp hq 1,
            covariantDerivative_gaugeTransform hu1 hp hq I]
          ring
      _ = (u z : ℂ) * (2 * ((equation x z 1 : ℂ) + (equation x z 2 : ℂ) * I)) := by
          rw [covariantDerivative_one_add_I_mul_covariantDerivative_I hp hq]
      _ = 0 := by simp [h₁, h₂]
  have hy12 : (equation y z 1 : ℂ) + (equation y z 2 : ℂ) * I = 0 :=
    (mul_eq_zero.1 hdbar).resolve_left two_ne_zero
  have hy1 : equation y z 1 = 0 := by simpa using congrArg Complex.re hy12
  have hy2 : equation y z 2 = 0 := by simpa using congrArg Complex.im hy12
  have hℓy : (fun w ↦ Real.log (4 * (y w 2 ^ 2 + y w 3 ^ 2))) = ℓ := by
    funext w; simp only [ℓ, y, u, gaugeTransform_apply_two_sq_add_apply_three_sq]
  have hyα : y z 2 ^ 2 + y z 3 ^ 2 ≠ 0 := by
    simpa only [y, u, gaugeTransform_apply_two_sq_add_apply_three_sq] using hα
  have hf1 := fderiv_log_normSq_apply_one hyp hyq hyα hy1 hy2
  have hfI := fderiv_log_normSq_apply_I hyp hyq hyα hy1 hy2
  rw [hℓy, hy3, hdy3] at hf1 hfI
  simp only [zero_apply, mul_zero, zero_mul, sub_zero, zero_div, neg_zero, zero_sub] at hf1 hfI
  exact ⟨by linarith [hfI], by linarith [hf1]⟩

/-- At a nonzero point where `α ≠ 0`, `∂bar_a α = 0`, and near which the section is `|α|` times
`windingPhase m`, the first connection coordinate of the winding-`m` end trivialization of `x` is
`-(1 / 2) ∂₂(log |α|²)`. -/
theorem gaugeTransform_inv_windingPhase_apply_zero {z : ℂ} (hz : z ≠ 0)
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w) :
    gaugeTransform (windingPhase m)⁻¹ x z 0 =
      -(1 / 2) * fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z I :=
  (gaugeTransform_inv_windingPhase_apply_zero_and_one hz hp hq hα h₁ h₂ hphase).1

/-- At a nonzero point where `α ≠ 0`, `∂bar_a α = 0`, and near which the section is `|α|` times
`windingPhase m`, the second connection coordinate of the winding-`m` end trivialization of `x` is
`(1 / 2) ∂₁(log |α|²)`. -/
theorem gaugeTransform_inv_windingPhase_apply_one {z : ℂ} (hz : z ≠ 0)
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w) :
    gaugeTransform (windingPhase m)⁻¹ x z 1 =
      (1 / 2) * fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z 1 :=
  (gaugeTransform_inv_windingPhase_apply_zero_and_one hz hp hq hα h₁ h₂ hphase).2

/-- Outside the cutoff disc of `referenceField f m`, at a nonzero point where `α ≠ 0`,
`∂bar_a α = 0`, and near which the section is `|α|` times `windingPhase m`, the connection defect
of `x - referenceField f m` is `(-(1 / 2) ∂₂(log |α|²), (1 / 2) ∂₁(log |α|²))` and its section
defect is `(exp ((1 / 2) log |α|²) - 1)` times the reference section coordinates. -/
private theorem sub_referenceField_eq_of_sectionValue_eq_mul_windingPhase
    (f : ContDiffBump (0 : ℝ)) {z : ℂ} (hrOut : f.rOut ≤ ‖z‖ ^ 2)
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0)
    (hphase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w) :
    let ℓ : ℂ → ℝ := fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))
    (x z 0 - referenceField f m z 0 = -(1 / 2) * fderiv ℝ ℓ z I) ∧
      (x z 1 - referenceField f m z 1 = (1 / 2) * fderiv ℝ ℓ z 1) ∧
      (x z 2 - referenceField f m z 2 = (Real.exp (ℓ z / 2) - 1) * referenceField f m z 2) ∧
      (x z 3 - referenceField f m z 3 = (Real.exp (ℓ z / 2) - 1) * referenceField f m z 3) := by
  intro ℓ
  have hz : z ≠ 0 := ne_zero_of_rOut_le_norm_sq f hrOut
  have hy0 := gaugeTransform_inv_windingPhase_apply_zero hz hp hq hα h₁ h₂ hphase
  have hy1 := gaugeTransform_inv_windingPhase_apply_one hz hp hq hα h₁ h₂ hphase
  -- Subtract `vacuumField = gaugeTransform (windingPhase m)⁻¹ (referenceField f m)`.
  have hsub := congrFun (gaugeTransform_sub_gaugeTransform (windingPhase m)⁻¹ x
    (referenceField f m)) z
  rw [Pi.sub_apply, gaugeTransform_inv_windingPhase_referenceField f m hrOut] at hsub
  have hconn0 : gaugeTransform (windingPhase m)⁻¹ x z 0 = x z 0 - referenceField f m z 0 := by
    simpa [vacuumField_apply, gaugeLinearAction_apply] using congrArg (· 0) hsub
  have hconn1 : gaugeTransform (windingPhase m)⁻¹ x z 1 = x z 1 - referenceField f m z 1 := by
    simpa [vacuumField_apply, gaugeLinearAction_apply] using congrArg (· 1) hsub
  -- Outside the cutoff disc `referenceSection f m z = windingPhase m z` and `|α| = exp (ℓ / 2)`.
  have hexp : ‖sectionValue x z‖ = Real.exp (ℓ z / 2) := by
    have hpos : 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
      lt_of_le_of_ne (by positivity) (mul_ne_zero four_ne_zero hα).symm
    dsimp only [ℓ]
    rw [Real.exp_half, Real.exp_log hpos, ← sq_norm_sectionValue, Real.sqrt_sq (norm_nonneg _)]
  have hsec_sub : sectionValue x z - sectionValue (referenceField f m) z =
      (Real.exp (ℓ z / 2) - 1 : ℝ) * sectionValue (referenceField f m) z := by
    rw [sectionValue_referenceField, hphase.self_of_nhds, hexp, referenceSection_eq_phase f m hrOut,
      ← coe_windingPhase m hz]
    push_cast
    ring
  have hsec_re := congrArg Complex.re hsec_sub
  have hsec_im := congrArg Complex.im hsec_sub
  simp only [sectionValue_apply, sub_re, sub_im, mul_re, mul_im, add_re, add_im, ofReal_re,
    ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at hsec_re hsec_im
  exact ⟨hconn0.symm.trans hy0, hconn1.symm.trans hy1, by linarith, by linarith⟩

/-- Cut off `(1 / 2) log |α|²` near the origin via `TauCeti.exists_contDiff_eventually_eventuallyEq`
to obtain a globally smooth function `L` on `ℂ` that agrees locally with
`(1 / 2) log (4 (p² + q²))` outside a compact set and inherits exponential derivative decay at
every rate `c' < 1 / 2`. -/
private theorem exists_contDiff_eq_half_log_normSq
    (hp : ContDiff ℝ ∞ (fun w ↦ x w 2)) (hq : ContDiff ℝ ∞ (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ L : ℂ → ℝ, ContDiff ℝ ∞ L ∧
      (∀ᶠ z in cocompact ℂ,
        L =ᶠ[𝓝 z] fun w ↦ (1 / 2) * Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) ∧
      ∀ {c' : ℝ}, c' < 1 / 2 → ∀ j : ℕ,
        iteratedFDeriv ℝ j L =O[cocompact ℂ] fun z ↦ Real.exp (-(c' * ‖z‖)) := by
  have hpos : ∀ᶠ z in cocompact ℂ, 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1))
  obtain ⟨L, hL, hL_ev⟩ := TauCeti.exists_contDiff_eventually_eventuallyEq (n := ⊤)
    (f := fun w ↦ (1 / 2) * Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)))
    (hpos.mono fun _ hz ↦ contDiffAt_const.mul ((contDiff_normSq hp hq).contDiffAt.log
      (by positivity)))
  refine ⟨L, hL, hL_ev, fun {c'} hc' j ↦ ?_⟩
  have hlog :=
    (isBigO_iteratedFDeriv_log_normSq hp hq hsol hlim hc' j).norm_left.const_mul_left (1 / 2)
  refine isBigO_norm_left.1 ((EventuallyEq.isBigO ?_).trans hlog)
  filter_upwards [hL_ev, hpos] with z hnhds hz
  have hnhds' : L =ᶠ[𝓝 z] fun w ↦ (1 / 2 : ℝ) • Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2)) := hnhds
  have hcd_log : ContDiffAt ℝ j (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z :=
    ((contDiff_normSq hp hq).contDiffAt.log (by positivity)).of_le (by simp)
  rw [(hnhds'.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_const_smul_apply' hcd_log, norm_smul,
    Real.norm_eq_abs, abs_of_pos one_half_pos]

/-- Bound the `n`-th iterated derivative of `(exp L - 1) · (referenceField f m)ₖ` along
`cocompact ℂ` by combining `ContDiff.isBigO_iteratedFDeriv_exp_sub_one` with the uniform derivative
bounds on `referenceField f m`. -/
private theorem isBigO_iteratedFDeriv_exp_sub_one_mul_referenceField (f : ContDiffBump (0 : ℝ))
    (m : ℕ) {L : ℂ → ℝ} (hL : ContDiff ℝ ∞ L)
    (hLbdd : ∀ j : ℕ, iteratedFDeriv ℝ j L =O[cocompact ℂ] fun _ ↦ (1 : ℝ)) {c : ℝ}
    (hLc : ∀ j : ℕ, iteratedFDeriv ℝ j L =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)))
    (k : Fin 4) (n : ℕ) :
    iteratedFDeriv ℝ n (fun z ↦ (Real.exp (L z) - 1) * referenceField f m z k) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  have hL₀ : L =O[cocompact ℂ] fun _ ↦ (1 : ℝ) :=
    (isBigO_of_le _ fun _ ↦ by simp [iteratedFDeriv_zero_eq_comp]).trans (hLbdd 0)
  have hexp (j : ℕ) :
      iteratedFDeriv ℝ j (fun z ↦ Real.exp (L z) - 1) =O[cocompact ℂ]
        fun z ↦ Real.exp (-(c * ‖z‖)) :=
    (hL.of_le (by simp)).isBigO_iteratedFDeriv_exp_sub_one hL₀
      (fun i _ _ ↦ hLbdd i) (fun i _ ↦ hLc i)
  have href_bdd (j : ℕ) :
      iteratedFDeriv ℝ j (fun z ↦ referenceField f m z k) =O[cocompact ℂ] fun _ ↦ (1 : ℝ) := by
    obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_referenceField_apply_le f m k j
    exact IsBigO.of_bound (max C 0) (Eventually.of_forall fun z ↦ by
      simpa using (hC z).trans (le_max_left C 0))
  have hB := (ContinuousLinearMap.mul ℝ ℝ).isBigO_iteratedFDeriv_of_bilinear (n := n)
    ((Real.contDiff_exp.comp hL).sub contDiff_const)
    (contDiff_euclidean.1 (contDiff_referenceField f m) k) (by simp)
    (fun j _ ↦ hexp j) (fun j _ ↦ href_bdd j)
  simpa only [ContinuousLinearMap.mul_apply', Function.comp_apply, mul_one] using hB

/-- Lift coordinatewise smooth surrogates with `O(ρ)` iterated derivatives outside a compact set to
vector-valued `O(ρ)` iterated derivative decay in `EuclideanSpace ℝ (Fin 4)`. -/
private theorem isBigO_iteratedFDeriv_of_eventuallyEq_coord
    {F : ℂ → EuclideanSpace ℝ (Fin 4)} {g : Fin 4 → ℂ → ℝ} (hg_cd : ∀ i, ContDiff ℝ ∞ (g i))
    (hg_ev : ∀ᶠ z in cocompact ℂ, ∀ i, (fun w ↦ F w i) =ᶠ[𝓝 z] g i) {ρ : ℂ → ℝ} {n : ℕ}
    (hg_decay : ∀ i, iteratedFDeriv ℝ n (g i) =O[cocompact ℂ] ρ) :
    iteratedFDeriv ℝ n F =O[cocompact ℂ] ρ := by
  let e (i : Fin 4) : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (1 : ℝ →L[ℝ] ℝ).smulRight (EuclideanSpace.single i 1)
  let G : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ ∑ i : Fin 4, e i (g i z)
  have hG_decay : iteratedFDeriv ℝ n G =O[cocompact ℂ] ρ := by
    have hsum_eq : iteratedFDeriv ℝ n G =
        fun z ↦ ∑ i : Fin 4, iteratedFDeriv ℝ n (fun w ↦ e i (g i w)) z :=
      funext fun z ↦ iteratedFDeriv_fun_sum_apply fun i _ ↦
        ((e i).contDiff.comp (hg_cd i)).contDiffAt.of_le (by simp)
    rw [hsum_eq]
    refine IsBigO.fun_sum fun i _ ↦ isBigO_norm_left.1 ((isBigO_of_le _ fun z ↦ ?_).trans
      ((hg_decay i).norm_left.const_mul_left ‖e i‖))
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (by positivity)]
    exact (e i).norm_iteratedFDeriv_comp_left (hg_cd i).contDiffAt (by simp)
  refine (EventuallyEq.isBigO ?_).trans hG_decay
  filter_upwards [hg_ev] with z hz
  have hnhds : F =ᶠ[𝓝 z] G := by
    filter_upwards [Filter.eventually_all.2 hz] with w hw
    ext j
    simp [G, e, Finset.sum_apply, Pi.single_apply, hw j]
  exact (hnhds.iteratedFDeriv ℝ n).eq_of_nhds

/-- Construct globally smooth coordinate surrogates `g : Fin 4 → ℂ → ℝ` that agree locally with the
coordinates of `gaugeTransform (windingPhase m)⁻¹ x - vacuumField` outside a compact set and have
`O(exp (-c |z|))` iterated derivatives at infinity for every `c < 1 / 2`. -/
private theorem exists_contDiff_gaugeTransform_inv_windingPhase_sub_vacuumField_eq_and_isBigO
    (hp : ContDiff ℝ ∞ (fun w ↦ x w 2)) (hq : ContDiff ℝ ∞ (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z) :
    ∃ g : Fin 4 → ℂ → ℝ, (∀ i, ContDiff ℝ ∞ (g i)) ∧
      (∀ᶠ z in cocompact ℂ, ∀ i,
        (fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w i - vacuumField w i) =ᶠ[𝓝 z] g i) ∧
      ∀ {c : ℝ}, c < 1 / 2 → ∀ i n,
        iteratedFDeriv ℝ n (g i) =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨L, hL, hL_ev, hL_decay⟩ := exists_contDiff_eq_half_log_normSq hp hq hsol hlim
  have hLf : ContDiff ℝ ∞ (fderiv ℝ L) := hL.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  let g : Fin 4 → ℂ → ℝ := ![fun z ↦ -fderiv ℝ L z I, fun z ↦ fderiv ℝ L z 1,
    fun z ↦ (1 / 2 : ℝ) * (Real.exp (L z) - 1), 0]
  have hg_cd (i : Fin 4) : ContDiff ℝ ∞ (g i) := by
    fin_cases i
    · exact ((ContinuousLinearMap.apply ℝ ℝ I).contDiff.comp hLf).neg
    · exact (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)).contDiff.comp hLf
    · exact contDiff_const.mul ((Real.contDiff_exp.comp hL).sub contDiff_const)
    · exact contDiff_const
  have hev_pt : ∀ᶠ z in cocompact ℂ,
      ∀ i, gaugeTransform (windingPhase m)⁻¹ x z i - vacuumField z i = g i z := by
    obtain ⟨R₀, -, hR₀⟩ :=
      hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸ hphase)
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (max R₀ 1),
      hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)),
      hL_ev] with z hzR hgt hL_nhds i
    have hz : z ≠ 0 := norm_pos_iff.1 (by linarith [le_max_right R₀ 1])
    have hnhds_phase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w :=
      Filter.eventually_of_mem
        ((isOpen_lt continuous_const continuous_norm).mem_nhds ((le_max_left _ _).trans_lt hzR))
        fun w hw ↦ hR₀ hw.le
    have hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hgt; linarith
    have hfderiv_L : fderiv ℝ L z =
        (1 / 2 : ℝ) • fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z := by
      rw [hL_nhds.fderiv_eq]
      exact fderiv_const_mul (((contDiff_normSq hp hq).contDiffAt.log
        (mul_ne_zero four_ne_zero hα)).differentiableAt (by simp)) (1 / 2)
    have hy0 := gaugeTransform_inv_windingPhase_apply_zero hz
      (hp.differentiable (by simp) z) (hq.differentiable (by simp) z) hα
      (by simp [hsol z]) (by simp [hsol z]) hnhds_phase
    have hy1 := gaugeTransform_inv_windingPhase_apply_one hz
      (hp.differentiable (by simp) z) (hq.differentiable (by simp) z) hα
      (by simp [hsol z]) (by simp [hsol z]) hnhds_phase
    have hsec := sectionValue_apply (gaugeTransform (windingPhase m)⁻¹ x) z ▸
      sectionValue_gaugeTransform_inv_windingPhase hnhds_phase.self_of_nhds
    have hexp : ‖sectionValue x z‖ = Real.exp (L z) := by
      have hpos : 0 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) := by linarith
      rw [hL_nhds.eq_of_nhds,
        show (1 / 2 : ℝ) * Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) =
          Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) / 2 by ring,
        Real.exp_half, Real.exp_log hpos, ← sq_norm_sectionValue, Real.sqrt_sq (norm_nonneg _)]
    fin_cases i
    · dsimp [g]; rw [hy0, hfderiv_L]; simp [vacuumField_apply, smul_eq_mul]
    · dsimp [g]; rw [hy1, hfderiv_L]; simp [vacuumField_apply, smul_eq_mul]
    · have hre := congrArg Complex.re (hexp ▸ hsec)
      simp only [mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at hre
      dsimp [g]; simp only [vacuumField_apply, PiLp.toLp_apply, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]; linarith
    · have him := congrArg Complex.im hsec
      simp only [mul_im, add_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat] at him
      dsimp [g]; simp only [vacuumField_apply, PiLp.toLp_apply, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply]; linarith
  obtain ⟨R, -, hR⟩ :=
    hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸ hev_pt)
  have hg_ev : ∀ᶠ z in cocompact ℂ, ∀ i,
      (fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w i - vacuumField w i) =ᶠ[𝓝 z] g i := by
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz i
    exact Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
      fun w hw ↦ hR hw.le i
  refine ⟨g, hg_cd, hg_ev, fun {c} hc i n ↦ ?_⟩
  have hLbdd (j : ℕ) : iteratedFDeriv ℝ j L =O[cocompact ℂ] fun _ ↦ (1 : ℝ) := by
    simpa using hL_decay (by norm_num : (0 : ℝ) < 1 / 2) j
  fin_cases i
  · dsimp [g]
    have hneg : iteratedFDeriv ℝ n (fun z ↦ -fderiv ℝ L z I) =
        -iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ L z I) :=
      funext fun _ ↦ iteratedFDeriv_neg_apply
    rw [hneg]
    exact (hL.isBigO_iteratedFDeriv_fderiv_apply (by simp)
      (hL_decay hc (n + 1)) I).neg_left
  · exact hL.isBigO_iteratedFDeriv_fderiv_apply (by simp) (hL_decay hc (n + 1)) 1
  · dsimp [g]
    have hL₀ : L =O[cocompact ℂ] fun _ ↦ (1 : ℝ) :=
      (isBigO_of_le _ fun _ ↦ by simp [iteratedFDeriv_zero_eq_comp]).trans (hLbdd 0)
    have hexp := (hL.of_le (m := n) (by simp)).isBigO_iteratedFDeriv_exp_sub_one hL₀
      (fun j _ _ ↦ hLbdd j) (fun j _ ↦ hL_decay hc j)
    have hcd_exp (z : ℂ) : ContDiffAt ℝ n (fun w ↦ Real.exp (L w) - 1) z :=
      ((Real.contDiff_exp.comp hL).sub contDiff_const).contDiffAt.of_le (by simp)
    have hsmul : iteratedFDeriv ℝ n (fun z ↦ (1 / 2 : ℝ) * (Real.exp (L z) - 1)) =
        (1 / 2 : ℝ) • iteratedFDeriv ℝ n (fun w ↦ Real.exp (L w) - 1) :=
      funext fun z ↦ by
        simpa only [smul_eq_mul, Pi.smul_apply] using
          iteratedFDeriv_const_smul_apply' (a := (1 / 2 : ℝ)) (hcd_exp z)
    rw [hsmul]
    exact hexp.const_smul_left (1 / 2 : ℝ)
  · dsimp [g]
    have hzero : iteratedFDeriv ℝ n (0 : ℂ → ℝ) = 0 := by ext; simp
    rw [hzero]
    exact isBigO_zero _ _

/-- Construct globally smooth coordinate surrogates `g : Fin 4 → ℂ → ℝ` that agree locally with the
coordinates of `x - referenceField f m` outside a compact set and have `O(exp (-c |z|))` iterated
derivatives at infinity for every `c < 1 / 2`. -/
private theorem exists_contDiff_sub_referenceField_eq_and_isBigO
    (hp : ContDiff ℝ ∞ (fun w ↦ x w 2)) (hq : ContDiff ℝ ∞ (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) :
    ∃ g : Fin 4 → ℂ → ℝ, (∀ i, ContDiff ℝ ∞ (g i)) ∧
      (∀ᶠ z in cocompact ℂ, ∀ i, (fun w ↦ x w i - referenceField f m w i) =ᶠ[𝓝 z] g i) ∧
      ∀ {c : ℝ}, c < 1 / 2 → ∀ i n,
        iteratedFDeriv ℝ n (g i) =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) := by
  -- Smoothly extend `(1 / 2) log |α|²` across the compact core to define the surrogate `g`.
  obtain ⟨L, hL, hL_ev, hL_decay⟩ := exists_contDiff_eq_half_log_normSq hp hq hsol hlim
  have hLf : ContDiff ℝ ∞ (fderiv ℝ L) := hL.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have href_cd := contDiff_euclidean.1 (contDiff_referenceField f m)
  let g : Fin 4 → ℂ → ℝ := ![fun z ↦ -fderiv ℝ L z I, fun z ↦ fderiv ℝ L z 1,
    fun z ↦ (Real.exp (L z) - 1) * referenceField f m z 2,
    fun z ↦ (Real.exp (L z) - 1) * referenceField f m z 3]
  have hg_cd (i : Fin 4) : ContDiff ℝ ∞ (g i) := by
    fin_cases i
    · exact ((ContinuousLinearMap.apply ℝ ℝ I).contDiff.comp hLf).neg
    · exact (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)).contDiff.comp hLf
    · exact ((Real.contDiff_exp.comp hL).sub contDiff_const).mul (href_cd 2)
    · exact ((Real.contDiff_exp.comp hL).sub contDiff_const).mul (href_cd 3)
  -- Identify `x - referenceField f m` with `g` on an open exterior neighborhood of infinity.
  have hev_pt : ∀ᶠ z in cocompact ℂ, ∀ i, x z i - referenceField f m z i = g i z := by
    obtain ⟨R₀, -, hR₀⟩ :=
      hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸ hphase)
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop (max R₀ (max 1 f.rOut)),
      hlim.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)),
      hL_ev] with z hzR hgt hL_nhds i
    have hrOut : f.rOut ≤ ‖z‖ ^ 2 := rOut_le_norm_sq f ((le_max_right _ _).trans_lt hzR)
    have hnhds_phase : ∀ᶠ w in 𝓝 z, sectionValue x w = ‖sectionValue x w‖ * windingPhase m w :=
      Filter.eventually_of_mem
        ((isOpen_lt continuous_const continuous_norm).mem_nhds ((le_max_left _ _).trans_lt hzR))
        fun w hw ↦ hR₀ hw.le
    have hα : x z 2 ^ 2 + x z 3 ^ 2 ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hgt; linarith
    have hfderiv_L : fderiv ℝ L z =
        (1 / 2 : ℝ) • fderiv ℝ (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) z := by
      rw [hL_nhds.fderiv_eq]
      exact fderiv_const_mul (((contDiff_normSq hp hq).contDiffAt.log
        (mul_ne_zero four_ne_zero hα)).differentiableAt (by simp)) (1 / 2)
    obtain ⟨h0, h1, h2, h3⟩ := sub_referenceField_eq_of_sectionValue_eq_mul_windingPhase f hrOut
      (hp.differentiable (by simp) z) (hq.differentiable (by simp) z) hα
      (by simp [hsol z]) (by simp [hsol z]) hnhds_phase
    fin_cases i
    · dsimp [g]; rw [h0, hfderiv_L]; simp only [smul_apply, smul_eq_mul]; ring
    · dsimp [g]; rw [h1, hfderiv_L]; simp only [smul_apply, smul_eq_mul]
    · dsimp [g]; rw [h2, hL_nhds.eq_of_nhds]; ring_nf
    · dsimp [g]; rw [h3, hL_nhds.eq_of_nhds]; ring_nf
  obtain ⟨R, -, hR⟩ :=
    hasBasis_cobounded_norm.eventually_iff.mp (cobounded_eq_cocompact (α := ℂ) ▸ hev_pt)
  have hg_ev : ∀ᶠ z in cocompact ℂ, ∀ i,
      (fun w ↦ x w i - referenceField f m w i) =ᶠ[𝓝 z] g i := by
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz i
    exact Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
      fun w hw ↦ hR hw.le i
  -- Bound the iterated derivatives of each coordinate of `g` from those of `L`.
  refine ⟨g, hg_cd, hg_ev, fun {c} hc i n ↦ ?_⟩
  have hLbdd (j : ℕ) : iteratedFDeriv ℝ j L =O[cocompact ℂ] fun _ ↦ (1 : ℝ) := by
    simpa using hL_decay (by norm_num : (0 : ℝ) < 1 / 2) j
  fin_cases i
  · dsimp [g]
    have hneg : iteratedFDeriv ℝ n (fun z ↦ -fderiv ℝ L z I) =
        -iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ L z I) :=
      funext fun _ ↦ iteratedFDeriv_neg_apply
    rw [hneg]
    exact (hL.isBigO_iteratedFDeriv_fderiv_apply (by simp)
      (hL_decay hc (n + 1)) I).neg_left
  · exact hL.isBigO_iteratedFDeriv_fderiv_apply (by simp) (hL_decay hc (n + 1)) 1
  · exact isBigO_iteratedFDeriv_exp_sub_one_mul_referenceField f m hL hLbdd (hL_decay hc) 2 n
  · exact isBigO_iteratedFDeriv_exp_sub_one_mul_referenceField f m hL hLbdd (hL_decay hc) 3 n

/-! ### Exponential decay of all derivatives of an end-normalized vortex -/

/-- **Coordinate derivative decay in the winding-`m` end trivialization.** Let `x` be a plane vortex
with smooth section, `|α| → 1` at infinity, and section equal to `|α|` times `windingPhase m`
outside a compact set. Then for every rate `c < 1 / 2`, every coordinate `i`, and every order `n`,
`Dⁿ((gaugeTransform (windingPhase m)⁻¹ x)ᵢ - vacuumFieldᵢ) = O(exp (-c |z|))` at infinity. -/
theorem isBigO_iteratedFDeriv_gaugeTransform_inv_windingPhase_sub_vacuumField_apply
    (hp : ContDiff ℝ ∞ (fun w ↦ x w 2)) (hq : ContDiff ℝ ∞ (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    {c : ℝ} (hc : c < 1 / 2) (i : Fin 4) (n : ℕ) :
    iteratedFDeriv ℝ n
      (fun z ↦ gaugeTransform (windingPhase m)⁻¹ x z i - vacuumField z i) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨g, -, hg_ev, hg_decay⟩ :=
    exists_contDiff_gaugeTransform_inv_windingPhase_sub_vacuumField_eq_and_isBigO hp hq hsol hlim
      hphase
  exact (EventuallyEq.isBigO (hg_ev.mono fun _ hz ↦ ((hz i).iteratedFDeriv ℝ n).eq_of_nhds)).trans
    (hg_decay hc i n)

/-- **Derivative decay in the winding-`m` end trivialization.** Let `x` be a plane vortex with
smooth section, `|α| → 1` at infinity, and section equal to `|α|` times `windingPhase m` outside a
compact set. Then for every rate `c < 1 / 2` and every order `n`,
`Dⁿ(gaugeTransform (windingPhase m)⁻¹ x - vacuumField) = O(exp (-c |z|))` at infinity. -/
theorem isBigO_iteratedFDeriv_gaugeTransform_inv_windingPhase_sub_vacuumField
    (hp : ContDiff ℝ ∞ (fun w ↦ x w 2)) (hq : ContDiff ℝ ∞ (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    {c : ℝ} (hc : c < 1 / 2) (n : ℕ) :
    iteratedFDeriv ℝ n (gaugeTransform (windingPhase m)⁻¹ x - vacuumField) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨g, hg_cd, hg_ev, hg_decay⟩ :=
    exists_contDiff_gaugeTransform_inv_windingPhase_sub_vacuumField_eq_and_isBigO hp hq hsol hlim
      hphase
  exact isBigO_iteratedFDeriv_of_eventuallyEq_coord hg_cd hg_ev fun i ↦ hg_decay hc i n

/-- **Coordinate derivative decay for an end-normalized vortex.** Let `x` be a plane vortex with
smooth section, `|α| → 1` at infinity, and section equal to `|α|` times `windingPhase m` outside a
compact set. Then for every cutoff `f`, every rate `c < 1 / 2`, every coordinate `i`, and every
order `n`, `Dⁿ(xᵢ - (x_ref)ᵢ) = O(exp (-c |z|))` at infinity. No global regularity assumption on
the connection components of `x` is needed. -/
theorem isBigO_iteratedFDeriv_sub_referenceField_apply
    (hp : ContDiff ℝ ∞ (fun w ↦ x w 2)) (hq : ContDiff ℝ ∞ (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) (i : Fin 4) (n : ℕ) :
    iteratedFDeriv ℝ n (fun z ↦ x z i - referenceField f m z i) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨g, -, hg_ev, hg_decay⟩ :=
    exists_contDiff_sub_referenceField_eq_and_isBigO hp hq hsol hlim hphase f
  exact (EventuallyEq.isBigO (hg_ev.mono fun _ hz ↦ ((hz i).iteratedFDeriv ℝ n).eq_of_nhds)).trans
    (hg_decay hc i n)

/-- **Derivative decay of an end-normalized vortex.** Let `x` be a plane vortex with smooth
section, `|α| → 1` at infinity, and section equal to `|α|` times `windingPhase m` outside a compact
set. Then for every cutoff `f`, every rate `c < 1 / 2`, and every order `n`,
`Dⁿ(x - referenceField f m) = O(exp (-c |z|))` at infinity. -/
theorem isBigO_iteratedFDeriv_sub_referenceField
    (hp : ContDiff ℝ ∞ (fun w ↦ x w 2)) (hq : ContDiff ℝ ∞ (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) (n : ℕ) :
    iteratedFDeriv ℝ n (x - referenceField f m) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨g, hg_cd, hg_ev, hg_decay⟩ :=
    exists_contDiff_sub_referenceField_eq_and_isBigO hp hq hsol hlim hphase f
  exact isBigO_iteratedFDeriv_of_eventuallyEq_coord hg_cd hg_ev fun i ↦ hg_decay hc i n

/-- **Global exponential decay of all derivatives of a smooth end-normalized vortex.** For a smooth
plane vortex with `|α| → 1` at infinity whose section equals `|α|` times `windingPhase m` outside a
compact set, every iterated derivative of `x - referenceField f m` decays at every rate
`c < 1 / 2`: `‖Dⁿ(x - referenceField f m)(z)‖ ≤ K exp (-c |z|)`. -/
theorem exists_norm_iteratedFDeriv_sub_referenceField_le_mul_exp (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) {c : ℝ} (hc : c < 1 / 2) (n : ℕ) :
    ∃ K, ∀ z, ‖iteratedFDeriv ℝ n (x - referenceField f m) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨K, hK⟩ := (isBigO_iteratedFDeriv_sub_referenceField
    (contDiff_euclidean.1 hx 2) (contDiff_euclidean.1 hx 3) hsol hlim hphase f hc n).bound
  have hcont : Continuous fun z ↦ ‖iteratedFDeriv ℝ n (x - referenceField f m) z‖ :=
    ((hx.sub (contDiff_referenceField f m)).continuous_iteratedFDeriv (by simp)).norm
  refine exists_forall_le_mul_exp_of_eventually_le hcont (K := K) ?_
  filter_upwards [hK] with z hz
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hz

/-- **Sobolev membership of a smooth end-normalized vortex.** A smooth plane vortex with `|α| → 1`
at infinity whose section equals `|α|` times `windingPhase m` outside a compact set lies in the
affine Sobolev field space `framedFieldSpace f m s` for every cutoff `f` and real order `s`. -/
theorem mem_framedFieldSpace_of_sectionValue_eq_mul_windingPhase (hx : ContDiff ℝ ∞ x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    (f : ContDiffBump (0 : ℝ)) (s : ℝ) :
    x ∈ framedFieldSpace f m s := by
  rw [mem_framedFieldSpace, mem_sobolevFields]
  intro i
  have hcoord : ContDiff ℝ ∞ fun z ↦ (x - referenceField f m) z i :=
    (contDiff_euclidean.1 hx i).sub (contDiff_euclidean.1 (contDiff_referenceField f m) i)
  exact TemperedDistribution.mem_realSobolevFunctions_of_isBigO_iteratedFDeriv_exp hcoord
    (c := 1 / 4) (by norm_num)
    (isBigO_iteratedFDeriv_sub_referenceField_apply (contDiff_euclidean.1 hx 2)
      (contDiff_euclidean.1 hx 3) hsol hlim hphase f (by norm_num) i) s

/-! ### Smooth framed gauge representatives in `A_m^s` -/

/-- **Smooth framed gauge representative in `A_m^s` with all-order exponential decay.** Every
smooth plane vortex with the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1` has a smooth framed
gauge transform `u • x` whose section is `|α|` times `windingPhase m` outside a compact set, which
belongs to `framedFieldSpace f m s` for every cutoff `f` and real order `s`, and whose difference
from `referenceField f m` has all iterated derivatives globally bounded by multiples of
`exp (-c |z|)` for every `f` and every rate `c < 1 / 2`. -/
theorem exists_framedGaugeGroup_smul_mem_framedFieldSpace_norm_iteratedFDeriv_le_mul_exp
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup,
      (∀ᶠ z in cocompact ℂ,
        sectionValue (u • x) z = ‖sectionValue (u • x) z‖ * windingPhase m z) ∧
      (∀ (f : ContDiffBump (0 : ℝ)) (s : ℝ), u • x ∈ framedFieldSpace f m s) ∧
      ∀ (f : ContDiffBump (0 : ℝ)), ∀ c < 1 / 2, ∀ n : ℕ, ∃ K, ∀ z,
        ‖iteratedFDeriv ℝ n (u • x - referenceField f m) z‖ ≤ K * Real.exp (-(c * ‖z‖)) := by
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_sectionValue_smul_eq hx hframe
  have hy := contDiff_framedGaugeGroup_smul u hx
  have hsol' (z : ℂ) : equation (u • x) z = 0 :=
    (equation_framedGaugeGroup_smul_eq_zero_iff u
      (hx.contDiffAt.differentiableAt (by simp))).2 (hsol z)
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow
    (tendsto_sectionValue_framedGaugeGroup_smul u hframe)
  exact ⟨u, hu,
    fun f s ↦ mem_framedFieldSpace_of_sectionValue_eq_mul_windingPhase hy hsol' hlim hu f s,
    fun f _ hc n ↦ exists_norm_iteratedFDeriv_sub_referenceField_le_mul_exp hy hsol' hlim hu f hc n⟩

end TauCeti.Vortex
