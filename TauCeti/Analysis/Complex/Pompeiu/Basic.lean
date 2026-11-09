/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.LinearAlgebra.Complex.Module
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Complex.CauchyKernel

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
  `D` of it is `f`. With the conjugate Wirtinger derivative, `\bar∂_w ∫ (w - z)⁻¹ • f z = π f w`,
  so the transform is complex differentiable at every point where `f` vanishes, and holomorphic
  off the support of `f`.

So the Cauchy transform inverts `D = 2 \bar∂` on both sides on compactly supported `C¹` maps. This
representation is the starting point of the elliptic estimates for the Cauchy–Riemann operator:
differentiating it expresses `∂ u` through `\bar∂ u` by the Beurling transform, a singular integral
operator, and the Calderón–Zygmund inequality `‖∇u‖_{Lᵖ} ≤ C ‖\bar∂ u‖_{Lᵖ}` for compactly supported
`u` is the `Lᵖ` boundedness of that operator.

The proof of the formula passes to polar coordinates `z = w + r e^{iθ}` about `w`. There the
integrand `(z - w)⁻¹ • D u z dz` becomes `∂ᵣ v + i r⁻¹ ∂_θ v` for `v (r, θ) = u (w + r e^{iθ})`.
The angular term integrates to zero over each circle, and the radial term integrates to `-u w`
along each ray.

The normalized `TauCeti.cauchyTransform f w = π⁻¹ ∫ z, (w - z)⁻¹ • f z` inverts
`bar∂` itself. Its basic integral and convolution formulas, almost-everywhere congruence, and
compact-support left and right inverse identities are available in this module.

## Main results

* `TauCeti.cauchyTransform` and `TauCeti.cauchyTransform_apply`: the normalized integral.
* `HasCompactSupport.conjWirtingerDeriv_cauchyTransform` and
  `HasCompactSupport.cauchyTransform_conjWirtingerDeriv`: normalized right and left inverses.
* `HasCompactSupport.two_pi_inv_smul_integral_sub_inv_smul_fderiv_apply_one_add_I_smul_apply_I`:
  the Cauchy–Pompeiu formula.
* `HasCompactSupport.hasFDerivAt_integral_sub_inv_smul`: the Cauchy transform of a compactly
  supported `C¹` map is differentiable, with derivative the transform of the derivative.
* `HasCompactSupport.fderiv_cauchyTransform` and `HasCompactSupport.fderiv_cauchyTransform_apply`:
  the same commutation `D (T f) = T (D f)` for the normalized transform, also in directional form.
* `TauCeti.cauchyTransform_add` and `TauCeti.cauchyTransform_smul`: the normalized transform is
  additive on continuous compactly supported data and commutes with scalar multiplication.
* `HasCompactSupport.fderiv_apply_one_add_I_smul_apply_I_two_pi_inv_smul_integral_sub_inv_smul`:
  `D = 2 \bar∂` of the Cauchy transform of a compactly supported `C¹` map `f` is `f`.
* `HasCompactSupport.conjWirtingerDeriv_integral_sub_inv_smul_apply_one`:
  `\bar∂ (∫ (w - z)⁻¹ • f z) = π f`.
* `HasCompactSupport.differentiableAt_integral_sub_inv_smul_of_eq_zero` and
  `TauCeti.differentiableOn_integral_sub_inv_smul_compl`: holomorphy where `f` vanishes, in
  particular off `tsupport f`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.2.1 and Theorem 1.2.2.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B.2 (the Calderón–Zygmund inequality).
-/

public section

open MeasureTheory Complex Set Filter ComplexConjugate Metric Function
open scoped NNReal Real Topology Convolution

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The planar Cauchy transform with the normalization inverting `bar∂`, using the kernel
`(w - z)⁻¹`. For rough compactly supported `Lᵖ` data the integral exists almost everywhere. -/
noncomputable def cauchyTransform (f : ℂ → F) (w : ℂ) : F :=
  (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z

/-- The defining normalized integral of the Cauchy transform. -/
theorem cauchyTransform_apply (f : ℂ → F) (w : ℂ) :
    cauchyTransform f w = (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z := (rfl)

/-- In convolution coordinates the Cauchy transform uses the reciprocal kernel with the same
positive sign. The variable substitution gives `ξ⁻¹ • f (w - ξ)`. -/
theorem cauchyTransform_eq_convolution (f : ℂ → F) :
    cauchyTransform f = fun w ↦ (Real.pi : ℂ)⁻¹ •
      ((fun z : ℂ ↦ z⁻¹) ⋆[ContinuousLinearMap.lsmul ℝ ℂ] f) w := by
  funext w
  rw [cauchyTransform_apply]
  congr 1
  simpa only [ContinuousLinearMap.lsmul_apply] using
    (convolution_eq_swap (L := ContinuousLinearMap.lsmul ℝ ℂ)
      (f := fun z : ℂ ↦ z⁻¹) (g := f) (x := w)).symm

/-- A supported input may be integrated over its input disc in the Cauchy formula. -/
theorem cauchyTransform_eq_integral_closedBall {f : ℂ → F} {c : ℂ} {r : ℝ≥0}
    (hf : support f ⊆ closedBall c (r : ℝ)) (w : ℂ) :
    cauchyTransform f w =
      (Real.pi : ℂ)⁻¹ • ∫ z in closedBall c (r : ℝ), (w - z)⁻¹ • f z := by
  rw [cauchyTransform_apply, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro z hz
  rw [notMem_support.mp (fun h ↦ hz (hf h)), smul_zero]

/-- Almost-everywhere changes in the source leave the actual Cauchy integral unchanged. -/
theorem cauchyTransform_congr_ae {f g : ℂ → F} (hfg : f =ᵐ[volume] g) :
    cauchyTransform f = cauchyTransform g := by
  funext w
  simp only [cauchyTransform_apply]
  congr 1
  exact integral_congr_ae (hfg.mono fun z hz ↦ congrArg (fun v ↦ (w - z)⁻¹ • v) hz)

@[simp]
theorem cauchyTransform_zero : cauchyTransform (0 : ℂ → F) = 0 := by
  ext w
  simp only [cauchyTransform_apply, Pi.zero_apply, smul_zero, integral_zero]

/-- The Cauchy transform is additive on continuous compactly supported data. -/
theorem cauchyTransform_add {f g : ℂ → F} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    cauchyTransform (f + g) = cauchyTransform f + cauchyTransform g := by
  funext w
  simp only [cauchyTransform_apply, Pi.add_apply, smul_add]
  rw [integral_add ((locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport hf hfc)
    ((locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport hg hgc), smul_add]

/-- The Cauchy transform commutes with scalar multiplications that commute with the complex and
real actions, in particular with real and complex scalars. -/
theorem cauchyTransform_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F]
    [SMulCommClass ℂ 𝕜 F] [SMulCommClass ℝ 𝕜 F] (a : 𝕜) (f : ℂ → F) :
    cauchyTransform (a • f) = a • cauchyTransform f := by
  funext w
  simp only [cauchyTransform_apply, Pi.smul_apply]
  simp_rw [smul_comm (w - _)⁻¹ a]
  rw [integral_smul, smul_comm]

section Polar

/-- The unit vector `e^{iθ}`, written as in `Complex.polarCoord_symm_apply`. -/
private noncomputable abbrev expI (θ : ℝ) : ℂ := Real.cos θ + Real.sin θ * I

private lemma norm_expI (θ : ℝ) : ‖expI θ‖ = 1 := by
  simpa only [expI, ← ofReal_cos, ← ofReal_sin] using Complex.norm_cos_add_sin_mul_I θ

private lemma hasDerivAt_expI (θ : ℝ) : HasDerivAt expI (I * expI θ) θ := by
  have h := ((hasDerivAt_id θ).ofReal_comp.mul_const I).cexp
  simp only [id_eq, ofReal_one, one_mul, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin] at h
  exact h.congr_deriv (mul_comm _ _)

/-- In polar coordinates `(r, θ)` about `w`, the integrand `r • (r e^{iθ})⁻¹ • (L 1 + I • L I)`
of the Cauchy transform becomes `L e^{iθ} + I • L (I e^{iθ})`. For `L` the derivative of `u` at
`w + r e^{iθ}`, these are `∂ᵣ v` and `r⁻¹ ∂_θ v` for `v (r, θ) = u (w + r e^{iθ})`. -/
private lemma smul_polarCoord_symm_inv_smul {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace ℂ G] (L : ℂ →L[ℝ] G) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    r • ((Complex.polarCoord.symm (r, θ))⁻¹ • (L 1 + I • L I)) =
      L (expI θ) + I • L (I * expI θ) := by
  have hinv : (r : ℂ) * ((r : ℂ) * expI θ)⁻¹ = conj (expI θ) := by
    calc
      (r : ℂ) * ((r : ℂ) * expI θ)⁻¹ = (expI θ)⁻¹ := by field_simp [ofReal_ne_zero.2 hr]
      _ = conj (expI θ) := Complex.inv_eq_conj (norm_expI θ)
  rw [Complex.polarCoord_symm_apply, ← Complex.coe_smul, smul_smul, hinv]
  simpa only [ContinuousLinearMap.coe_coe] using
    L.toLinearMap.conj_smul_apply_one_add_I_smul_apply_I _

variable {u : ℂ → F}

/-- In polar coordinates about `w`, the derivative of a compactly supported `C¹` map `u` at
`w + r e^{iθ}`, applied to a continuous direction `v θ`, is integrable over
`polarCoord.target`: it is continuous and vanishes for large radius. -/
private lemma integrableOn_polarCoord_target_fderiv (hc : HasCompactSupport u)
    (hu : ContDiff ℝ 1 u) (w : ℂ) {v : ℝ → ℂ} (hv : Continuous v) :
    IntegrableOn (fun p : ℝ × ℝ => fderiv ℝ u (w + p.1 * expI p.2) (v p.2))
      polarCoord.target := by
  obtain ⟨R, -, hR⟩ := ((hc.fderiv ℝ).comp_homeomorph (Homeomorph.addLeft w)).exists_pos_le_norm
  have hcont : Continuous fun p : ℝ × ℝ => fderiv ℝ u (w + p.1 * expI p.2) (v p.2) :=
    ((hu.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply (hv.comp continuous_snd)
  refine (hcont.continuousOn.integrableOn_compact
    ((isCompact_Icc (a := 0) (b := R)).prod (isCompact_Icc (a := -π) (b := π))))
    |>.of_forall_sdiff_eq_zero (polarCoord_target ▸ measurableSet_Ioi.prod measurableSet_Ioo) ?_
  rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hK⟩
  have hRr : R ≤ ‖r * expI θ‖ := by
    rw [norm_mul, norm_expI, mul_one, norm_real, Real.norm_of_nonneg (le_of_lt hr)]
    by_contra h
    exact hK ⟨⟨le_of_lt hr, (not_le.1 h).le⟩, ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩⟩
  have := hR _ hRr
  simp only [Function.comp_apply, Homeomorph.coe_addLeft] at this
  simp [this]

variable [CompleteSpace F]

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
    have h := smul_polarCoord_symm_inv_smul (fderiv ℝ u (w + Complex.polarCoord.symm (r, θ)))
      (ne_of_gt hr) θ
    simp only [Complex.polarCoord_symm_apply, hA, hB, hG] at h ⊢
    exact h
  -- Both parts are integrable: they are continuous and vanish for large radius.
  have hAi : IntegrableOn A polarCoord.target :=
    integrableOn_polarCoord_target_fderiv hc hu w (v := expI) (by fun_prop)
  have hBi : IntegrableOn B polarCoord.target :=
    integrableOn_polarCoord_target_fderiv hc hu w (v := fun θ => I * expI θ) (by fun_prop)
  have hprod : (volume : Measure (ℝ × ℝ)).restrict polarCoord.target =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π)) := by
    rw [polarCoord_target, Measure.volume_eq_prod, Measure.prod_restrict]
  -- The radial part integrates to `-u w` along each ray.
  have hAval : ∫ p in polarCoord.target, A p = -((2 * π) • u w) := by
    rw [hprod, integral_prod_symm _ (by rw [← hprod]; exact hAi)]
    simp only [hA]
    rw [setIntegral_congr_fun measurableSet_Ioo fun θ _ => by
      simpa only [real_smul] using hc.integral_Ioi_fderiv_apply_ray hu w
        (e := expI θ) (norm_ne_zero_iff.1 (by rw [norm_expI]; exact one_ne_zero))]
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

omit [CompleteSpace F] in
/-- The Cauchy transform `w ↦ ∫ (w - z)⁻¹ • f z` of a compactly supported `C¹` map `f` is
differentiable, and its derivative is the Cauchy transform of the derivative of `f`. -/
theorem _root_.HasCompactSupport.hasFDerivAt_integral_sub_inv_smul {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (w : ℂ) :
    HasFDerivAt (fun w => ∫ z, (w - z)⁻¹ • f z) (∫ z, (w - z)⁻¹ • fderiv ℝ f z) w := by
  convert hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    Complex.locallyIntegrable_inv hf w using 1
  · funext z
    simp only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply]
  · rw [convolution_eq_swap]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    ext v
    simp

/-- The Cauchy transform inverts `D = 2 \bar∂` from the other side: for a compactly supported
`C¹` map `f : ℂ → F`, the transform `T f w = (2π)⁻¹ ∫ (w - z)⁻¹ • f z` satisfies
`∂ₓ (T f) + i ∂ᵧ (T f) = f`, that is `2 \bar∂ (T f) = f`. -/
theorem
  _root_.HasCompactSupport.fderiv_apply_one_add_I_smul_apply_I_two_pi_inv_smul_integral_sub_inv_smul
    {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (w : ℂ) :
    fderiv ℝ (fun w => (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z) w 1 +
      I • fderiv ℝ (fun w => (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z) w I = f w := by
  have hintL : Integrable fun z => (w - z)⁻¹ • fderiv ℝ f z :=
    (Complex.locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport
      (hf.continuous_fderiv one_ne_zero) (hc.fderiv ℝ)
  have hint (v : ℂ) : Integrable fun z => (w - z)⁻¹ • fderiv ℝ f z v := by
    simpa only [smul_apply] using hintL.apply_continuousLinearMap v
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

/-- **The Cauchy transform solves `\bar∂ u = f`.** For a compactly supported `C¹` map `f`, the
conjugate Wirtinger derivative of `w ↦ ∫ (w - z)⁻¹ • f z` is `π • f`, so the Cauchy transform
`π⁻¹ ∫ (w - z)⁻¹ • f z` satisfies `\bar∂ u = f`. -/
theorem _root_.HasCompactSupport.conjWirtingerDeriv_integral_sub_inv_smul_apply_one {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (w : ℂ) :
    conjWirtingerDeriv (fun w ↦ ∫ z, (w - z)⁻¹ • f z) w 1 = (π : ℂ) • f w := by
  have hT := hc.hasFDerivAt_integral_sub_inv_smul hf w
  have h := hc.fderiv_apply_one_add_I_smul_apply_I_two_pi_inv_smul_integral_sub_inv_smul hf w
  have hT' : HasFDerivAt (fun w ↦ (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z)
      ((2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • fderiv ℝ f z) w := hT.const_smul _
  rw [hT'.fderiv] at h
  rw [conjWirtingerDeriv_apply, hT.fderiv, smul_eq_mul, mul_one, ← h]
  simp only [FunLike.coe_smul, Pi.smul_apply]
  match_scalars <;> field_simp

/-- The Cauchy transform of a compactly supported `C¹` map `f` is complex differentiable at every
point where `f` vanishes. -/
theorem _root_.HasCompactSupport.differentiableAt_integral_sub_inv_smul_of_eq_zero {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) {w : ℂ} (hw : f w = 0) :
    DifferentiableAt ℂ (fun w ↦ ∫ z, (w - z)⁻¹ • f z) w := by
  rw [differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero
    (hc.hasFDerivAt_integral_sub_inv_smul hf w).differentiableAt,
    hc.conjWirtingerDeriv_integral_sub_inv_smul_apply_one hf, hw, smul_zero]

/-- The Cauchy transform of a `C¹` map `f` vanishing outside a compact set `k` is holomorphic on
the complement of `k`. For compactly supported `f`, taking `k = tsupport f` shows that the
transform is holomorphic off the support of `f`. Applied to a family `g p` vanishing outside a
common compact set `k`, this gives a region of holomorphy independent of the parameter `p`. -/
theorem differentiableOn_integral_sub_inv_smul_compl {f : ℂ → F} {k : Set ℂ} (hk : IsCompact k)
    (hfk : ∀ x ∉ k, f x = 0) (hf : ContDiff ℝ 1 f) :
    DifferentiableOn ℂ (fun w ↦ ∫ z, (w - z)⁻¹ • f z) kᶜ := fun w hw ↦
  ((HasCompactSupport.intro hk hfk).differentiableAt_integral_sub_inv_smul_of_eq_zero hf
    (hfk w hw)).differentiableWithinAt

omit [CompleteSpace F] in
/-- The real derivative of the Cauchy transform on compactly supported `C¹` data is obtained
by applying the same kernel to the derivative of the source. -/
theorem _root_.HasCompactSupport.hasFDerivAt_cauchyTransform {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (w : ℂ) :
    HasFDerivAt (cauchyTransform f)
      ((Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • fderiv ℝ f z) w :=
  (hc.hasFDerivAt_integral_sub_inv_smul hf w).const_smul _

omit [CompleteSpace F] in
/-- On compactly supported `C¹` data the real derivative of the Cauchy transform is the Cauchy
transform of the real derivative. -/
theorem _root_.HasCompactSupport.fderiv_cauchyTransform {f : ℂ → F} (hc : HasCompactSupport f)
    (hf : ContDiff ℝ 1 f) :
    fderiv ℝ (cauchyTransform f) = cauchyTransform (fderiv ℝ f) :=
  funext fun w ↦ by
    rw [(hc.hasFDerivAt_cauchyTransform hf w).fderiv, cauchyTransform_apply]

omit [CompleteSpace F] in
/-- The directional derivative of the Cauchy transform of compactly supported `C¹` data in the
direction `v` is the Cauchy transform of the directional derivative of the data. -/
theorem _root_.HasCompactSupport.fderiv_cauchyTransform_apply {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (w v : ℂ) :
    fderiv ℝ (cauchyTransform f) w v = cauchyTransform (fun z ↦ fderiv ℝ f z v) w := by
  have hi : Integrable fun z ↦ (w - z)⁻¹ • fderiv ℝ f z :=
    (locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport
      (hf.continuous_fderiv one_ne_zero) (hc.fderiv ℝ)
  rw [hc.fderiv_cauchyTransform hf, cauchyTransform_apply, cauchyTransform_apply,
    smul_apply, ContinuousLinearMap.integral_apply hi]
  simp only [smul_apply]

/-- On compactly supported `C¹` data the normalized Cauchy transform is a right inverse of
`bar∂ = (∂ₛ + i ∂ₜ) / 2`. -/
theorem _root_.HasCompactSupport.conjWirtingerDeriv_cauchyTransform {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (w : ℂ) :
    conjWirtingerDeriv (cauchyTransform f) w 1 = f w := by
  have hd := hc.hasFDerivAt_integral_sub_inv_smul hf w
  have he := hc.conjWirtingerDeriv_integral_sub_inv_smul_apply_one hf w
  rw [show cauchyTransform f = (fun x ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (x - z)⁻¹ • f z) from
    funext (cauchyTransform_apply f)]
  have hc0 : conjWirtingerDeriv (fun _ : ℂ ↦ (Real.pi : ℂ)⁻¹) w 1 = 0 := by
    simp
  rw [conjWirtingerDeriv_smul_apply (differentiableAt_const _) hd.differentiableAt 1, hc0,
    zero_smul, add_zero, he, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Real.pi_ne_zero),
    one_smul]

/-- The normalized Cauchy transform is also a left inverse on compactly supported `C¹` maps:
applying it to `bar∂ u` recovers `u`, with no boundary term. -/
theorem _root_.HasCompactSupport.cauchyTransform_conjWirtingerDeriv {u : ℂ → F}
    (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u) (w : ℂ) :
    cauchyTransform (fun z ↦ conjWirtingerDeriv u z 1) w = u w := by
  rw [cauchyTransform_apply]
  have heq : (fun z ↦ (w - z)⁻¹ • conjWirtingerDeriv u z 1) =
      fun z ↦ (2 : ℂ)⁻¹ • ((w - z)⁻¹ •
        (fderiv ℝ u z 1 + Complex.I • fderiv ℝ u z Complex.I)) := by
    funext z
    simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one]
    exact smul_comm _ _ _
  rw [heq, integral_smul, smul_smul]
  convert hc.two_pi_inv_smul_integral_sub_inv_smul_fderiv_apply_one_add_I_smul_apply_I hu w
    using 1
  congr 1
  field_simp

end TauCeti
