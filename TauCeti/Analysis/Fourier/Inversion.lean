/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.Inversion
public import TauCeti.Analysis.Fourier.SincKernel

import TauCeti.Analysis.Fourier.RiemannLebesgue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Fourier inversion and uniqueness

On a finite-dimensional real inner product space, a continuous integrable function whose Fourier
transform vanishes is zero. The vanishing transform is trivially integrable, so Mathlib's Fourier
inversion formula `Continuous.fourierInv_fourier_eq` applies and recovers the function as the
inverse transform of zero.

For a real source variable, the Dini criterion instead assumes integrability of a local
difference quotient. It recovers the function from symmetric finite inverse Fourier integrals even
when the Fourier transform is not integrable. If the source is differentiable with integrable
derivative, the partial inverse integrals are also bounded uniformly in the point and truncation
height, by a constant times the L1 norm of its derivative.

## Main results

* `Continuous.eq_zero_of_fourier_eq_zero`: a continuous integrable function with vanishing Fourier
  transform is zero.
* `MeasureTheory.Integrable.intervalIntegral_fourierInv_fourier_eq_integral_sinc`: the finite-height
  Dirichlet-kernel formula, for arbitrary real truncation height.
* `MeasureTheory.Integrable.tendsto_intervalIntegral_fourierInv_fourier`: pointwise norm
  convergence of symmetric truncations under the local Dini condition.
* `Real.exists_bound_intervalIntegral_fourierInv_fourier`: uniform control by the L1
  derivative norm.

## References

The finite-kernel and principal-value arguments adapt the work of Robby Sneiderman in
[PNT Laplace inversion](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/5754873e8dae73f3b50f8f2b7a4f0b15d4df58aa/PrimeNumberTheoremAnd/LaplaceInversion.lean).
The proof uses Mathlib's interval Fubini and Riemann--Lebesgue theorems and the symmetric
Dirichlet integral.
-/

public section

open MeasureTheory
open scoped FourierTransform

section Uniqueness

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : V → E}

/-- A continuous integrable function whose Fourier transform vanishes is zero. -/
theorem Continuous.eq_zero_of_fourier_eq_zero (h : Continuous f) (hf : Integrable f)
    (hF : 𝓕 f = 0) : f = 0 := by
  have hinv := h.fourierInv_fourier_eq hf (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  ext v
  simp [Real.fourierInv_eq]

end Uniqueness

open Filter Topology Real Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem integrable_kernel_prod {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℝ → F} (hf : Integrable f) (x T : ℝ) :
    Integrable
      (fun z : ℝ × ℝ ↦ Complex.exp (((2 * π * z.1 * (x - z.2) : ℝ) : ℂ) * I) • f z.2)
      ((volume.restrict (Set.uIoc (-T) T)).prod volume) := by
  let : IsFiniteMeasure (volume.restrict (Set.uIoc (-T) T)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      simpa only [Set.uIoc] using
        (measure_Ioc_lt_top (μ := volume) (a := min (-T) T) (b := max (-T) T))⟩
  have hn : Integrable (fun u ↦ ‖f u‖) :=
    hf.mono_eNorm hf.aestronglyMeasurable.norm (.of_forall fun _ ↦ by simp)
  refine (hn.comp_snd (volume.restrict (Set.uIoc (-T) T))).mono_eNorm ?_ ?_
  · exact (by fun_prop : Continuous (fun z : ℝ × ℝ ↦
      Complex.exp (((2 * π * z.1 * (x - z.2) : ℝ) : ℂ) * I)))
      |>.aestronglyMeasurable.smul hf.aestronglyMeasurable.comp_snd
  · filter_upwards with z
    rw [eNorm_le_iff_norm_le]
    simp only [norm_smul, norm_exp_ofReal_mul_I, norm_norm, one_mul, le_refl]

private theorem intervalIntegral_fourierInv_fourier_eq_integral_exp
    {f : ℝ → E} (hf : Integrable f) (x T : ℝ) :
    (∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t) =
      ∫ y, (∫ t in -T..T,
        Complex.exp (((2 * π * t * (x - y) : ℝ) : ℂ) * I)) • f y := by
  by_cases hE : CompleteSpace E
  · let : CompleteSpace E := hE
    calc
      _ = ∫ t in -T..T, ∫ y,
          Complex.exp (((2 * π * t * (x - y) : ℝ) : ℂ) * I) • f y := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        rw [Real.fourier_real_eq_integral_exp_smul, Circle.smul_def, ← MeasureTheory.integral_smul]
        apply integral_congr_ae
        filter_upwards with y
        rw [← smul_assoc, smul_eq_mul, Real.fourierChar_apply, ← Complex.exp_add]
        apply congrArg (fun z : ℂ ↦ z • f y)
        apply congrArg Complex.exp
        push_cast
        ring
      _ = ∫ y, ∫ t in -T..T,
          Complex.exp (((2 * π * t * (x - y) : ℝ) : ℂ) * I) • f y :=
        intervalIntegral_integral_swap (integrable_kernel_prod hf x T)
      _ = _ := by simp_rw [intervalIntegral.integral_smul_const]
  · simp [intervalIntegral, integral_of_not_completeSpace hE]

/-- The inverse Fourier integral over a finite symmetric frequency interval is convolution
with the sinc kernel. The formula holds for every real truncation height, with the usual
orientation of interval integrals. -/
theorem MeasureTheory.Integrable.intervalIntegral_fourierInv_fourier_eq_integral_sinc
    {f : ℝ → E} (hf : Integrable f) (x T : ℝ) :
    ∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t =
      ∫ u, TauCeti.sincKernel T u • f (x - u) := by
  rw [intervalIntegral_fourierInv_fourier_eq_integral_exp hf]
  calc
    _ = ∫ y, TauCeti.sincKernel T (x - y) • f y := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← Complex.coe_smul, TauCeti.sincKernel_apply]
      congr 1
      have heq : (fun t : ℝ ↦ Complex.exp (((2 * π * t * (x - y) : ℝ) : ℂ) * I)) =
          (fun t : ℝ ↦ Complex.exp (((t * (2 * π * (x - y)) : ℝ) : ℂ) * I)) := by
        ext t
        apply congrArg Complex.exp
        apply congrArg (fun r : ℝ ↦ (r : ℂ) * I)
        ring
      rw [heq]
      -- Factor out T so the zero-frequency phase is expressed in terms of ha.
      have hphase : 2 * π * T * (x - y) = T * (2 * π * (x - y)) := by ring
      by_cases ha : 2 * π * (x - y) = 0
      · simp [ha, hphase]
        ring
      · rw [intervalIntegral.integral_comp_mul_right
          (fun t : ℝ ↦ Complex.exp ((t : ℂ) * I)) ha,
          neg_mul, integral_exp_mul_I_eq_sinc]
        -- Match the endpoint times frequency returned by the scaled integral formula.
        rw [hphase]
        simp only [Complex.real_smul]
        push_cast
        have hxy : x - y ≠ 0 := by
          intro h
          simp [h] at ha
        have hxyc : (x : ℂ) - (y : ℂ) ≠ 0 := by exact_mod_cast hxy
        field_simp [hxyc]
    _ = _ := by
      rw [← integral_sub_left_eq_self
        (fun y : ℝ ↦ TauCeti.sincKernel T (x - y) • f y) volume x]
      simp only [sub_sub_cancel]

private theorem error_integrable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℝ → F} (hf : Integrable f) {x R : ℝ}
    (hR : 0 < R)
    (hq : IntegrableOn (fun u : ℝ ↦ (u : ℂ)⁻¹ • (f (x - u) - f x))
      (Set.Ioc (-R) R)) :
    Integrable (fun u : ℝ ↦ (Set.Ioc (-R) R).indicator
      (fun u ↦ (u : ℂ)⁻¹ • (f (x - u) - f x)) u +
      (Set.Ioc (-R) R)ᶜ.indicator (fun u ↦ (u : ℂ)⁻¹ • f (x - u)) u) := by
  have hi := (integrable_indicator_iff measurableSet_Ioc).mpr hq
  have hn : Integrable (fun u ↦ ‖f u‖) :=
    hf.mono_eNorm hf.aestronglyMeasurable.norm (.of_forall fun _ ↦ by simp)
  have hb : ∀ u : ℝ,
      ‖((Set.Ioc (-R) R)ᶜ.indicator (fun u : ℝ ↦ (u : ℂ)⁻¹) u)‖ ≤ R⁻¹ := by
    intro u
    by_cases hu : u ∈ Set.Ioc (-R) R
    · simp only [Set.mem_compl_iff, not_not, hu, Set.indicator_of_notMem, norm_zero]
      exact inv_nonneg.mpr hR.le
    · rw [Set.indicator_of_mem hu, norm_inv, norm_real, Real.norm_eq_abs]
      apply inv_anti₀ hR
      rcases not_and_or.mp hu with hu | hu
      · exact (neg_le_abs u).trans' (by linarith [not_lt.mp hu])
      · exact (le_abs_self u).trans' (not_le.mp hu).le
  have ht : Integrable (fun u : ℝ ↦
      ((Set.Ioc (-R) R)ᶜ.indicator (fun u : ℝ ↦ (u : ℂ)⁻¹) u) • f (x - u)) := by
    refine ((hn.comp_sub_left x).const_mul R⁻¹).mono_eNorm ?_ ?_
    · exact ((by fun_prop : Measurable (fun u : ℝ ↦ (u : ℂ)⁻¹)).indicator
        measurableSet_Ioc.compl).aestronglyMeasurable.smul
          (hf.1.comp_measurePreserving (volume.measurePreserving_sub_left x))
    · filter_upwards with u
      rw [eNorm_le_iff_norm_le, norm_smul, Real.norm_of_nonneg
        (mul_nonneg (inv_nonneg.mpr hR.le) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hb u) (norm_nonneg _)
  have heq : (fun u : ℝ ↦
      ((Set.Ioc (-R) R)ᶜ.indicator (fun u : ℝ ↦ (u : ℂ)⁻¹) u) • f (x - u)) =
      (Set.Ioc (-R) R)ᶜ.indicator (fun u ↦ (u : ℂ)⁻¹ • f (x - u)) := by
    ext u
    by_cases hu : u ∈ Set.Ioc (-R) R <;> simp [hu]
  rw [heq] at ht
  exact hi.add ht

private theorem sine_quotient_split {F : Type*} [AddCommGroup F] [Module ℂ F]
    (f : ℝ → F) (x R T u : ℝ) :
    (Real.sin (2 * π * T * u) : ℂ) •
      ((Set.Ioc (-R) R).indicator (fun u ↦ (u : ℂ)⁻¹ • (f (x - u) - f x)) u +
       (Set.Ioc (-R) R)ᶜ.indicator (fun u ↦ (u : ℂ)⁻¹ • f (x - u)) u) =
    (π : ℂ) • ((Real.sin (2 * π * T * u) / (π * u) : ℂ) • f (x - u) -
      (Set.Ioc (-R) R).indicator
        (fun u : ℝ ↦ (Real.sin (2 * π * T * u) / (π * u) : ℂ)) u • f x) := by
  by_cases hu : u = 0
  · simp [hu]
  have hc : (π : ℂ) * (Real.sin (2 * π * T * u) / (π * u) : ℂ) =
      (Real.sin (2 * π * T * u) : ℂ) * (u : ℂ)⁻¹ := by
    field_simp
  by_cases hs : u ∈ Set.Ioc (-R) R
  · have hsc : u ∉ (Set.Ioc (-R) R)ᶜ := by simpa using hs
    simp only [Set.indicator_of_mem hs, Set.indicator_of_notMem hsc, add_zero,
      smul_sub, ← smul_assoc, smul_eq_mul, hc]
  · have hsc : u ∈ (Set.Ioc (-R) R)ᶜ := hs
    simp only [Set.indicator_of_notMem hs, Set.indicator_of_mem hsc, zero_add,
      zero_smul, sub_zero, ← smul_assoc, smul_eq_mul, hc]

private theorem kernel_split [CompleteSpace E] {f : ℝ → E} (hf : Integrable f)
    {x R : ℝ} (hR : 0 ≤ R) (T : ℝ) :
    (∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t) =
      (π : ℂ)⁻¹ • (∫ u, (Real.sin (2 * π * T * u) : ℂ) •
        ((Set.Ioc (-R) R).indicator (fun u ↦ (u : ℂ)⁻¹ • (f (x - u) - f x)) u +
         (Set.Ioc (-R) R)ᶜ.indicator (fun u ↦ (u : ℂ)⁻¹ • f (x - u)) u)) +
      (∫ u in -R..R, TauCeti.sincKernel T u) • f x := by
  let g (u : ℝ) := (Real.sin (2 * π * T * u) : ℂ) •
    ((Set.Ioc (-R) R).indicator (fun u ↦ (u : ℂ)⁻¹ • (f (x - u) - f x)) u +
      (Set.Ioc (-R) R)ᶜ.indicator (fun u ↦ (u : ℂ)⁻¹ • f (x - u)) u)
  let K (u : ℝ) := TauCeti.sincKernel T u • f (x - u)
  let W (u : ℝ) := (Set.Ioc (-R) R).indicator (TauCeti.sincKernel T) u • f x
  have hsplit : g =ᵐ[volume] fun u ↦ (π : ℂ) • (K u - W u) := by
    filter_upwards [TauCeti.sincKernel_ae_eq_sin_div T] with u hk
    have hwindow : Complex.ofReal ((Set.Ioc (-R) R).indicator (TauCeti.sincKernel T) u) =
        (Set.Ioc (-R) R).indicator (fun v ↦ (Real.sin (2 * π * T * v) / (π * v) : ℂ)) u := by
      by_cases hu : u ∈ Set.Ioc (-R) R <;> simp [hu, hk]
    dsimp only [g, K, W]
    rw [sine_quotient_split, ← Complex.coe_smul (TauCeti.sincKernel T u),
      ← Complex.coe_smul ((Set.Ioc (-R) R).indicator (TauCeti.sincKernel T) u),
      hwindow, congrArg Complex.ofReal hk, Complex.ofReal_div, Complex.ofReal_mul]
  have hK : Integrable K := (hf.comp_sub_left x).sincKernel_smul T
  have hW : Integrable W :=
    (((TauCeti.continuous_sincKernel T).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc).smul_const (f x)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : (∫ u, g u) = (π : ℂ) • ((∫ u, K u) - ∫ u, W u) := by
    rw [integral_congr_ae hsplit, integral_smul, integral_sub hK hW]
  rw [hf.intervalIntegral_fourierInv_fourier_eq_integral_sinc,
    intervalIntegral.integral_of_le (neg_le_self hR), ← integral_smul_const,
    ← integral_indicator measurableSet_Ioc]
  simp_rw [Set.indicator_smul_const_apply]
  rw [he, ← mul_smul, inv_mul_cancel₀ hπ, one_smul, sub_add_cancel]

/-- **Dini Fourier inversion** from an integrable local difference quotient.
Neither continuity at the evaluation point nor integrability of the Fourier transform is assumed.
The value of the quotient at zero is immaterial. -/
theorem MeasureTheory.Integrable.tendsto_intervalIntegral_fourierInv_fourier
    [CompleteSpace E] {f : ℝ → E} (hf : Integrable f) {x R : ℝ}
    (hR : R ≠ 0)
    (hq : IntervalIntegrable (fun u : ℝ ↦ (u : ℂ)⁻¹ • (f (x - u) - f x))
      volume (-R) R) :
    Tendsto (fun T : ℝ ↦ ∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t) atTop (nhds (f x)) := by
  have hR' : 0 < |R| := abs_pos.mpr hR
  have hq' : IntervalIntegrable (fun u : ℝ ↦ (u : ℂ)⁻¹ • (f (x - u) - f x))
      volume (-|R|) |R| := by
    rcases lt_or_gt_of_ne hR with hneg | hpos
    · simpa only [abs_of_neg hneg, neg_neg] using hq.symm
    · simpa only [abs_of_pos hpos] using hq
  have H := ((error_integrable hf hR' hq'.1).tendsto_integral_sin_smul_atTop.const_smul
    (π : ℂ)⁻¹).add
    ((TauCeti.tendsto_intervalIntegral_neg_sincKernel hR').smul_const (f x))
  simp only [smul_zero, one_smul, zero_add] at H
  exact H.congr (fun T ↦ (kernel_split hf hR'.le T).symm)

private theorem integral_kernel_eq {f : ℝ → E} (hfd : Differentiable ℝ f)
    (hf : Integrable f) (hd : Integrable (deriv f)) (x T : ℝ) :
    (∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t) =
      ∫ u, (∫ t in 0..u, TauCeti.sincKernel T t) • deriv f (x - u) := by
  let U : ℝ → ℝ := fun u ↦ ∫ t in 0..u, TauCeti.sincKernel T t
  let V : ℝ → E := fun u ↦ f (x - u)
  let V' : ℝ → E := fun u ↦ -deriv f (x - u)
  have hu (u : ℝ) : HasDerivAt U (TauCeti.sincKernel T u) u :=
    ((TauCeti.continuous_sincKernel T).integral_hasStrictDerivAt 0 u).hasDerivAt
  have hv (u : ℝ) : HasDerivAt V (V' u) u := by
    simpa only [V, V', Function.comp_def, neg_one_smul] using!
      (hfd (x - u)).hasDerivAt.scomp u ((hasDerivAt_id u).const_sub x)
  let C := 2 * Real.sineIntegral π / π
  have hU (u : ℝ) : ‖U u‖ ≤ C := TauCeti.norm_intervalIntegral_sincKernel_le T 0 u
  have hc : Continuous U := continuous_iff_continuousAt.mpr fun u ↦ (hu u).continuousAt
  have hVi : Integrable V := hf.comp_sub_left x
  have hV'i : Integrable V' := (hd.comp_sub_left x).neg
  have hUi : Integrable (fun u ↦ U u • V u) :=
    hVi.bdd_smul (φ := U) C hc.aestronglyMeasurable (Eventually.of_forall hU)
  have hUV' : Integrable (fun u ↦ U u • V' u) :=
    hV'i.bdd_smul (φ := U) C hc.aestronglyMeasurable (Eventually.of_forall hU)
  have heq := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (fun u _ ↦ hu u) (fun u _ ↦ hv u)
    hUV' (hVi.sincKernel_smul T) hUi
  rw [hf.intervalIntegral_fourierInv_fourier_eq_integral_sinc]
  simpa only [ContinuousLinearMap.lsmul_apply, U, V, V', smul_neg, integral_neg, neg_neg] using
    (congrArg Neg.neg heq).symm

/-- Symmetric partial inverse Fourier integrals are bounded uniformly in the evaluation point
and every real truncation height by a constant times the L1 norm of the derivative.
The constant is independent of the source function. Neither source integrability nor
completeness is assumed; nonintegrable Fourier integrals use the usual totalized value. -/
theorem Real.exists_bound_intervalIntegral_fourierInv_fourier :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℝ → E}, Differentiable ℝ f → Integrable (deriv f) →
      ∀ x T : ℝ, ‖∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t‖ ≤ C * ∫ u, ‖deriv f u‖ := by
  let C := 2 * Real.sineIntegral π / π
  have hC : 0 ≤ C := (norm_nonneg _).trans (TauCeti.norm_intervalIntegral_sincKernel_le 0 0 0)
  refine ⟨C, hC, fun {f} hf hd x T ↦ ?_⟩
  by_cases hI : Integrable f
  · rw [integral_kernel_eq hf hI hd]
    have hc : Continuous (fun u : ℝ ↦ ∫ t in 0..u, TauCeti.sincKernel T t) :=
      continuous_iff_continuousAt.mpr fun u ↦
        ((TauCeti.continuous_sincKernel T).integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
    have hi : Integrable (fun u : ℝ ↦
        (∫ t in 0..u, TauCeti.sincKernel T t) • deriv f (x - u)) :=
      (hd.comp_sub_left x).bdd_smul (φ := fun u ↦ ∫ t in 0..u, TauCeti.sincKernel T t)
        C hc.aestronglyMeasurable
        (Eventually.of_forall (fun u ↦ TauCeti.norm_intervalIntegral_sincKernel_le T 0 u))
    calc
      _ ≤ ∫ u, ‖(∫ t in 0..u, TauCeti.sincKernel T t) • deriv f (x - u)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ u, C * ‖deriv f (x - u)‖ := by
        apply integral_mono hi.norm (((hd.comp_sub_left x).norm).const_mul C)
        intro u
        dsimp only
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (TauCeti.norm_intervalIntegral_sincKernel_le T 0 u)
          (norm_nonneg _)
      _ = _ := by
        rw [integral_const_mul]
        congr 1
        exact integral_sub_left_eq_self (fun u : ℝ ↦ ‖deriv f u‖) volume x
  · have hzero : 𝓕 f = 0 := by
      ext w
      apply integral_undef
      exact fun h ↦ hI ((Real.fourierIntegral_convergent_iff w).mp h)
    simpa only [hzero, Pi.zero_apply, smul_zero, intervalIntegral.integral_zero, norm_zero] using
      mul_nonneg hC (integral_nonneg fun u ↦ norm_nonneg (deriv f u))
