/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# The Cauchy–Pompeiu formula

The Cauchy kernel `1 / (π z)` is a fundamental solution of the Cauchy–Riemann operator
`\bar∂ = (∂ₓ + i ∂ᵧ) / 2` on `ℂ`. Writing the operator as `D u = ∂ₓ u + i ∂ᵧ u = 2 \bar∂ u`, that is
`fun z ↦ fderiv ℝ u z 1 + I • fderiv ℝ u z I`, this file proves both halves of that statement for
compactly supported `C¹` maps `u : ℂ → F` into a complex Banach space.

* The **Cauchy–Pompeiu formula**: every such `u` is the Cauchy transform of `D u`,
  `u w = (2π)⁻¹ ∫ (w - z)⁻¹ • D u z`, the integral being over the whole plane. This is the
  Cauchy–Pompeiu formula on a disc containing the support of `u`, whose boundary term (the
  Cauchy integral of `u` over the boundary circle) vanishes.
* The Cauchy transform `w ↦ (2π)⁻¹ ∫ (w - z)⁻¹ • f z` of a compactly supported `C¹` map `f` is
  differentiable, its derivative is the Cauchy transform of the derivative of `f`, and
  `D` of it is `f`.

So the Cauchy transform inverts `D = 2 \bar∂` on both sides on compactly supported `C¹` maps. This
representation is the starting point of the elliptic estimates for the Cauchy–Riemann operator:
differentiating it expresses `∂ u` through `\bar∂ u` by the Beurling transform, a singular integral
operator, and the Calderón–Zygmund inequality `‖∇u‖_{Lᵖ} ≤ C ‖\bar∂ u‖_{Lᵖ}` for compactly supported
`u` is the `Lᵖ` boundedness of that operator.

The proof of the formula passes to polar coordinates `z = w + r e^{iθ}` about `w`. There the
integrand `(z - w)⁻¹ • D u z dz` becomes `∂ᵣ v + i r⁻¹ ∂_θ v` for `v (r, θ) = u (w + r e^{iθ})`.
The angular term integrates to zero over each circle, and the radial term integrates to `-u w`
along each ray.

## Main results

* `HasCompactSupport.two_pi_inv_smul_integral_sub_inv_smul_fderiv_apply_one_add_I_smul_apply_I`:
  the Cauchy–Pompeiu formula.
* `HasCompactSupport.hasFDerivAt_integral_sub_inv_smul`: the Cauchy transform of a compactly
  supported `C¹` map is differentiable, with derivative the transform of the derivative.
* `HasCompactSupport.fderiv_apply_one_add_I_smul_apply_I_two_pi_inv_smul_integral_sub_inv_smul`:
  `D = 2 \bar∂` of the Cauchy transform of a compactly supported `C¹` map `f` is `f`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.2.1 and Theorem 1.2.2.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B.2 (the Calderón–Zygmund inequality).
-/

public section

open MeasureTheory Complex Set Filter ComplexConjugate
open scoped Real Topology Convolution

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

section Algebra

/-- Rotating `L 1 + I • L I` by the conjugate of `e` gives the derivative of `L` along `e` plus
`I` times its derivative along `I * e`. With `e = e^{iθ}` and `L` the derivative of `u` at
`w + r e^{iθ}`, these are `∂ᵣ v` and `r⁻¹ ∂_θ v` for `v (r, θ) = u (w + r e^{iθ})`. -/
private lemma conj_smul_apply_one_add_I_smul_apply_I (L : ℂ →L[ℝ] F) (e : ℂ) :
    conj e • (L 1 + I • L I) = L e + I • L (I * e) := by
  have hL : ∀ z : ℂ, L z = (z.re : ℂ) • L 1 + (z.im : ℂ) • L I := fun z => by
    have hz : z = z.re • (1 : ℂ) + z.im • I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]
  have he : conj e = (e.re : ℂ) - e.im * I := by
    apply Complex.ext <;> simp
  rw [hL e, hL (I * e), he]
  simp only [mul_re, I_re, I_im, mul_im, zero_mul, one_mul, zero_sub, zero_add, ofReal_neg]
  match_scalars
  · ring
  · linear_combination -(e.im : ℂ) * I_sq

end Algebra

section Polar

/-- The unit vector `e^{iθ}`, written as in `Complex.polarCoord_symm_apply`. -/
private noncomputable abbrev expI (θ : ℝ) : ℂ := Real.cos θ + Real.sin θ * I

private lemma norm_expI (θ : ℝ) : ‖expI θ‖ = 1 := by
  rw [expI, ofReal_cos, ofReal_sin, ← Complex.exp_mul_I, Complex.norm_exp_ofReal_mul_I]

private lemma hasDerivAt_expI (θ : ℝ) : HasDerivAt expI (I * expI θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).ofReal_comp).add
    ((Real.hasDerivAt_sin θ).ofReal_comp.mul_const I)
  convert h using 1
  simp only [expI, ofReal_neg]
  linear_combination (Real.sin θ : ℂ) * I_sq

/-- A map with compact support vanishes outside some ball about any given point. -/
private lemma exists_forall_lt_norm_sub_imp_eq_zero {G : Type*} [Zero G] {g : ℂ → G}
    (hg : HasCompactSupport g) (w : ℂ) : ∃ R, ∀ z, R < ‖z - w‖ → g z = 0 := by
  obtain ⟨R, hR⟩ := hg.isCompact.isBounded.subset_closedBall w
  refine ⟨R, fun z hz => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have := hR hmem
  rw [Metric.mem_closedBall, dist_eq_norm] at this
  linarith

variable [CompleteSpace F] {u : ℂ → F}

/-- Integrating the radial derivative of a compactly supported `C¹` map along a ray from `w`
recovers `-u w`. -/
private lemma integral_Ioi_fderiv_apply_ray (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u)
    (w e : ℂ) (he : ‖e‖ = 1) :
    ∫ r in Ioi (0 : ℝ), fderiv ℝ u (w + r * e) e = -u w := by
  have hray : ∀ r : ℝ, ‖(w + r * e) - w‖ = |r| := fun r => by
    simp [he]
  have hderiv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => u (w + r * e)) (fderiv ℝ u (w + r * e) e) r :=
    fun r => by
      have h : HasDerivAt (fun r : ℝ => w + (r : ℂ) * e) e r := by
        simpa using ((hasDerivAt_id r).ofReal_comp.mul_const e).const_add w
      exact ((hu.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt r h
  obtain ⟨R, hR⟩ := exists_forall_lt_norm_sub_imp_eq_zero (hc.fderiv ℝ) w
  obtain ⟨R', hR'⟩ := exists_forall_lt_norm_sub_imp_eq_zero hc w
  have hcont : Continuous fun r : ℝ => fderiv ℝ u (w + r * e) e :=
    ((hu.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply continuous_const
  have hint : IntegrableOn (fun r : ℝ => fderiv ℝ u (w + r * e) e) (Ioi 0) := by
    refine (hcont.integrableOn_Icc (a := 0) (b := max R 0)).of_forall_sdiff_eq_zero
      measurableSet_Ioi fun r hr => ?_
    have hr' : max R 0 < r := by
      by_contra h
      exact hr.2 ⟨hr.1.le, not_lt.1 h⟩
    have hRr : R < ‖(w + r * e) - w‖ := by
      rw [hray, abs_of_pos hr.1]
      exact (le_max_left _ _).trans_lt hr'
    rw [hR _ hRr, zero_apply]
  have hlim : Tendsto (fun r : ℝ => u (w + r * e)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (max R' 0)] with r hr
    have hRr : R' < ‖(w + r * e) - w‖ := by
      rw [hray, abs_of_pos ((le_max_right _ _).trans_lt hr)]
      exact (le_max_left _ _).trans_lt hr
    rw [hR' _ hRr]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hderiv 0).continuousAt.continuousWithinAt
    (fun r _ => hderiv r) hint hlim]
  simp

/-- Integrating the angular derivative of a `C¹` map around a circle about `w` gives zero. -/
private lemma integral_Ioo_fderiv_apply_circle (hu : ContDiff ℝ 1 u) (w : ℂ) {r : ℝ}
    (hr : r ≠ 0) :
    ∫ θ in Ioo (-π) π, fderiv ℝ u (w + r * expI θ) (I * expI θ) = 0 := by
  have hderiv : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => u (w + r * expI θ))
      (r • fderiv ℝ u (w + r * expI θ) (I * expI θ)) θ := fun θ => by
    have h : HasDerivAt (fun θ : ℝ => w + r * expI θ) (r * (I * expI θ)) θ :=
      ((hasDerivAt_expI θ).const_mul (r : ℂ)).const_add w
    have hsm : fderiv ℝ u (w + r * expI θ) ((r : ℂ) * (I * expI θ)) =
        r • fderiv ℝ u (w + r * expI θ) (I * expI θ) := by
      rw [← map_smul, real_smul]
    exact hsm ▸ ((hu.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt θ h
  have hcont : Continuous fun θ : ℝ => r • fderiv ℝ u (w + r * expI θ) (I * expI θ) :=
    (((hu.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply
      (by fun_prop)).const_smul r
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
    (hcont.intervalIntegrable (-π) π)
  have hends : expI π = expI (-π) := by simp [expI]
  rw [hends, sub_self, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo, integral_smul] at hFTC
  exact (smul_eq_zero.1 hFTC).resolve_left hr

end Polar

variable [CompleteSpace F]

/-- **The Cauchy–Pompeiu formula** for a compactly supported `C¹` map `u : ℂ → F`: `u` is the
Cauchy transform of `∂ₓ u + i ∂ᵧ u = 2 \bar∂ u`,
`u w = (2π)⁻¹ ∫ (w - z)⁻¹ • (∂ₓ u z + i ∂ᵧ u z)`, the integral being over the whole plane. -/
theorem
  _root_.HasCompactSupport.two_pi_inv_smul_integral_sub_inv_smul_fderiv_apply_one_add_I_smul_apply_I
    {u : ℂ → F}
    (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u) (w : ℂ) :
    (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • (fderiv ℝ u z 1 + I • fderiv ℝ u z I) = u w := by
  set G : ℂ → F := fun z => fderiv ℝ u z 1 + I • fderiv ℝ u z I with hG
  -- Centre the integral at `w`, then pass to polar coordinates about `w`.
  have hcentre : ∫ z, (w - z)⁻¹ • G z = -∫ z, z⁻¹ • G (w + z) := by
    rw [← integral_neg, ← integral_add_left_eq_self (fun z => (w - z)⁻¹ • G z) w]
    congr 1 with z
    rw [sub_add_cancel_left, inv_neg, neg_smul]
  rw [hcentre, ← Complex.integral_comp_polarCoord_symm]
  set A : ℝ × ℝ → F := fun p => fderiv ℝ u (w + p.1 * expI p.2) (expI p.2) with hA
  set B : ℝ × ℝ → F := fun p => fderiv ℝ u (w + p.1 * expI p.2) (I * expI p.2) with hB
  have hmeas : MeasurableSet (polarCoord.target) := by
    rw [polarCoord_target]
    exact measurableSet_Ioi.prod measurableSet_Ioo
  -- In polar coordinates the integrand is `A + I • B`, with `A` radial and `B` angular.
  have hAB : EqOn (fun p : ℝ × ℝ => p.1 • ((Complex.polarCoord.symm p)⁻¹ •
      G (w + Complex.polarCoord.symm p))) (fun p => A p + I • B p) polarCoord.target := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt hr)
    have hinv : (r : ℂ) * ((r : ℂ) * expI θ)⁻¹ = conj (expI θ) := by
      calc
        (r : ℂ) * ((r : ℂ) * expI θ)⁻¹ = (expI θ)⁻¹ := by field_simp
        _ = conj (expI θ) := Complex.inv_eq_conj (norm_expI θ)
    simp only [Complex.polarCoord_symm_apply, hA, hB, hG]
    rw [← Complex.coe_smul, smul_smul, hinv, conj_smul_apply_one_add_I_smul_apply_I]
  -- Both parts are integrable: they are continuous and vanish for large radius.
  obtain ⟨R, hR⟩ := exists_forall_lt_norm_sub_imp_eq_zero (hc.fderiv ℝ) w
  have hint : ∀ v : ℝ → ℂ, Continuous v →
      IntegrableOn (fun p : ℝ × ℝ => fderiv ℝ u (w + p.1 * expI p.2) (v p.2))
        polarCoord.target := fun v hv => by
    have hcont : Continuous fun p : ℝ × ℝ => fderiv ℝ u (w + p.1 * expI p.2) (v p.2) :=
      ((hu.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply (hv.comp continuous_snd)
    refine (hcont.continuousOn.integrableOn_compact
      ((isCompact_Icc (a := 0) (b := max R 0)).prod (isCompact_Icc (a := -π) (b := π))))
      |>.of_forall_sdiff_eq_zero hmeas ?_
    rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hK⟩
    have hr' : max R 0 < r := by
      by_contra h
      exact hK ⟨⟨le_of_lt hr, not_lt.1 h⟩, ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩⟩
    have hnorm : ‖(w + r * expI θ) - w‖ = r := by
      simp only [add_sub_cancel_left, norm_mul, norm_expI, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_pos (show (0 : ℝ) < r from hr)]
    dsimp only
    rw [hR _ (by rw [hnorm]; exact (le_max_left _ _).trans_lt hr'), zero_apply]
  have hAi : IntegrableOn A polarCoord.target := hint expI (by fun_prop)
  have hBi : IntegrableOn B polarCoord.target := hint (fun θ => I * expI θ) (by fun_prop)
  have hprod : (volume : Measure (ℝ × ℝ)).restrict polarCoord.target =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π)) := by
    rw [polarCoord_target, Measure.volume_eq_prod, Measure.prod_restrict]
  -- The radial part integrates to `-u w` along each ray.
  have hAval : ∫ p in polarCoord.target, A p = -((2 * π) • u w) := by
    rw [hprod, integral_prod_symm _ (by rw [← hprod]; exact hAi)]
    simp only [hA]
    rw [setIntegral_congr_fun measurableSet_Ioo fun θ _ =>
      integral_Ioi_fderiv_apply_ray hc hu w (expI θ) (norm_expI θ)]
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), smul_neg]
    ring_nf
  -- The angular part integrates to zero around each circle.
  have hBval : ∫ p in polarCoord.target, B p = 0 := by
    rw [hprod, integral_prod _ (by rw [← hprod]; exact hBi)]
    refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
    exact integral_Ioo_fderiv_apply_circle hu w (ne_of_gt hr)
  rw [setIntegral_congr_fun hmeas hAB,
    integral_add (g := fun p => I • B p) hAi (hBi.smul I), integral_smul, hAval, hBval]
  simp only [smul_zero, add_zero, neg_neg, ← Complex.coe_smul, smul_smul]
  push_cast
  field_simp [Real.pi_ne_zero]
  simp

/-- The kernel `z ↦ (w - z)⁻¹` of the Cauchy transform is locally integrable on `ℂ`. -/
lemma locallyIntegrable_sub_inv (w : ℂ) :
    LocallyIntegrable (fun z : ℂ => (w - z)⁻¹) volume := by
  refine (locallyIntegrable_norm_sub_rpow (mu := volume) (s := -1) (by simp) w).mono
    (measurable_const.sub measurable_id).inv.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    Real.rpow_neg_one]

/-- Recentring the Cauchy transform at the evaluation point turns it into a convolution with the
kernel `t ↦ t⁻¹`. -/
private lemma integral_sub_inv_smul_eq_convolution {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] (g : ℂ → G) (w : ℂ) :
    ∫ z, (w - z)⁻¹ • g z =
      ((fun t : ℂ => t⁻¹) ⋆[ContinuousLinearMap.lsmul ℝ ℂ, volume] g) w := by
  rw [convolution_def, ← integral_sub_left_eq_self (fun z => (w - z)⁻¹ • g z) volume w]
  simp

omit [CompleteSpace F] in
/-- The Cauchy transform `w ↦ ∫ (w - z)⁻¹ • f z` of a compactly supported `C¹` map `f` is
differentiable, and its derivative is the Cauchy transform of the derivative of `f`. -/
theorem _root_.HasCompactSupport.hasFDerivAt_integral_sub_inv_smul {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (w : ℂ) :
    HasFDerivAt (fun w => ∫ z, (w - z)⁻¹ • f z) (∫ z, (w - z)⁻¹ • fderiv ℝ f z) w := by
  have hK : LocallyIntegrable (fun t : ℂ => t⁻¹) volume := by
    convert (locallyIntegrable_sub_inv 0).neg using 1
    ext t
    simp
  have h := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ) hK hf w
  rw [funext fun w => integral_sub_inv_smul_eq_convolution f w,
    integral_sub_inv_smul_eq_convolution]
  convert h using 1
  ext v
  simp only [convolution_def]
  congr 1 with t

/-- The Cauchy transform inverts `D = 2 \bar∂` from the other side: for a compactly supported
`C¹` map `f : ℂ → F`, the transform `T f w = (2π)⁻¹ ∫ (w - z)⁻¹ • f z` satisfies
`∂ₓ (T f) + i ∂ᵧ (T f) = f`, that is `2 \bar∂ (T f) = f`. -/
theorem
  _root_.HasCompactSupport.fderiv_apply_one_add_I_smul_apply_I_two_pi_inv_smul_integral_sub_inv_smul
    {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (w : ℂ) :
    fderiv ℝ (fun w => (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z) w 1 +
      I • fderiv ℝ (fun w => (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z) w I = f w := by
  have hint : ∀ v : ℂ, Integrable fun z => (w - z)⁻¹ • fderiv ℝ f z v := fun v =>
    (locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport
      ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ((hc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] F => L v) rfl)
  have hintL : Integrable fun z => (w - z)⁻¹ • fderiv ℝ f z :=
    (locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport
      (hf.continuous_fderiv one_ne_zero) (hc.fderiv ℝ)
  have hT : HasFDerivAt (fun w => (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z)
      ((2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • fderiv ℝ f z) w :=
    (hc.hasFDerivAt_integral_sub_inv_smul hf w).const_smul _
  rw [hT.fderiv]
  simp only [smul_apply, ContinuousLinearMap.integral_apply hintL]
  rw [smul_comm I, ← smul_add, ← integral_smul,
    ← integral_add (g := fun z => I • (w - z)⁻¹ • fderiv ℝ f z I) (hint 1) ((hint I).smul I)]
  conv_rhs =>
    rw [← hc.two_pi_inv_smul_integral_sub_inv_smul_fderiv_apply_one_add_I_smul_apply_I
      hf w]
  congr 2 with z
  rw [smul_add, smul_comm I]

end TauCeti
