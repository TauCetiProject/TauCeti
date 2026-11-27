/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Inversion
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import TauCeti.Analysis.BoundedVariation.OneDimensional.Basic
import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral
import TauCeti.Analysis.Fourier.RiemannLebesgue
import TauCeti.Analysis.SpecialFunctions.SineIntegral
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Dirichlet–Jordan pointwise Fourier inversion

Symmetric inverse Fourier integrals of an integrable function converge at every point where
the function has bounded variation on a neighbourhood. The limit is the mean of the two
one-sided limits, so the formula applies at jump discontinuities and is independent of the
value at the point itself.

Near the point, integration by parts against the derivative vector measure reduces the limits
to the Dirichlet integral. Away from the point the Riemann–Lebesgue lemma applies to the
difference kernel divided by distance from the point.

## References

* E. C. Titchmarsh, *Introduction to the Theory of Fourier Integrals*, Chapter I.
* The finite-height convolution formula is
  `MeasureTheory.Integrable.intervalIntegral_fourierInv_fourier_eq_integral_sinc`.
-/

public section

open Complex Filter MeasureTheory Real Set Topology
open scoped FourierTransform

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private noncomputable def kernel (T u : ℝ) : ℝ :=
  2 * T * Real.sinc (2 * π * T * u)

private noncomputable def primitive (T u : ℝ) : ℝ :=
  Real.sineIntegral (2 * π * T * u) / π

private theorem continuous_kernel (T : ℝ) : Continuous (kernel T) := by
  unfold kernel
  fun_prop

private theorem abs_kernel_le (T u : ℝ) : |kernel T u| ≤ 2 * |T| := by
  rw [kernel, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sinc_le_one _)

private theorem integral_kernel (T y : ℝ) :
    (∫ u in (0 : ℝ)..y, kernel T u) = primitive T y := by
  have h := intervalIntegral.smul_integral_comp_mul_left (f := Real.sinc)
    (a := (0 : ℝ)) (b := y) (2 * π * T)
  rw [smul_eq_mul, mul_zero, Real.integral_sinc_eq_sub,
    Real.sineIntegral_zero, sub_zero] at h
  simp only [kernel, primitive]
  rw [intervalIntegral.integral_const_mul, ← h]
  field_simp [Real.pi_ne_zero]

private theorem tendsto_primitive {y : ℝ} (hy : 0 < y) :
    Tendsto (fun T : ℝ ↦ primitive T y) atTop (𝓝 (1 / 2)) := by
  have h := (TauCeti.Contour.tendsto_integral_sinc_atTop.comp
    (tendsto_id.const_mul_atTop (by positivity : 0 < 2 * π * y))).div_const π
  have heq : (π / 2) / π = (1 / 2 : ℝ) := by field_simp [Real.pi_ne_zero]
  rw [heq] at h
  simpa only [primitive, Real.integral_sinc_eq_sub, Real.sineIntegral_zero, sub_zero,
    Function.comp_apply, id_eq, mul_right_comm (2 * π)] using h

private theorem tendsto_setIntegral_primitive {g : ℝ → E} (hg : BoundedVariationOn g univ)
    {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun T : ℝ ↦ ∫ᵛ u in Ioc 0 b, primitive T u ∂•hg.vectorMeasure)
      atTop (𝓝 ((1 / 2 : ℝ) • (g.rightLim b - g.rightLim 0))) := by
  let ν := hg.vectorMeasure.restrict (Ioc 0 b)
  have : IsFiniteMeasure ν.variation := by
    dsimp [ν]
    rw [VectorMeasure.variation_restrict measurableSet_Ioc]
    infer_instance
  have hmem : ∀ᵐ u ∂ν.variation, u ∈ Ioc (0 : ℝ) b := by
    simpa only [ν, VectorMeasure.variation_restrict measurableSet_Ioc] using
      (ae_restrict_mem (μ := hg.vectorMeasure.variation) measurableSet_Ioc)
  have hm (T : ℝ) : AEStronglyMeasurable (primitive T) ν.variation :=
    ((Real.continuous_sineIntegral.comp (continuous_const.mul continuous_id)).div_const
      π).aestronglyMeasurable
  have hbnd (T u : ℝ) : ‖primitive T u‖ ≤ Real.sineIntegral π / π := by
    rw [Real.norm_eq_abs, primitive, abs_div, abs_of_pos Real.pi_pos]
    exact div_le_div_of_nonneg_right (Real.abs_sineIntegral_le _) Real.pi_pos.le
  have h : Tendsto (fun T : ℝ ↦ ∫ᵛ u, primitive T u ∂•ν) atTop
      (𝓝 (∫ᵛ _ : ℝ, (1 / 2 : ℝ) ∂•ν)) :=
    VectorMeasure.tendsto_integral_filter_of_norm_le_const (.of_forall hm)
      ⟨_, .of_forall fun T ↦ .of_forall (hbnd T)⟩ (hmem.mono fun _ hu ↦ tendsto_primitive hu.1)
  simpa only [VectorMeasure.integral_const, ContinuousLinearMap.lsmul_apply,
    ν, VectorMeasure.restrict_apply _ measurableSet_Ioc MeasurableSet.univ,
    univ_inter, hg.vectorMeasure_Ioc hb] using h

private theorem tendsto_integral_kernel_of_boundedVariationOn {g : ℝ → E}
    (hg : BoundedVariationOn g univ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun T : ℝ ↦ ∫ u in (0 : ℝ)..b, kernel T u • g u)
      atTop (𝓝 ((1 / 2 : ℝ) • g.rightLim 0)) := by
  have h := ((tendsto_primitive hb).smul_const (g.rightLim b)).sub
    (tendsto_setIntegral_primitive hg hb.le)
  rw [smul_sub, sub_sub_cancel] at h
  refine h.congr fun T ↦ ?_
  rw [hg.intervalIntegral_smul_eq_sub_setIntegral_vectorMeasure hb.le
    ((continuous_kernel T).intervalIntegrable _ _), integral_kernel]
  congr 1
  exact VectorMeasure.setIntegral_congr_fun fun y _ ↦ (integral_kernel T y).symm

omit [CompleteSpace E] in
private theorem tendsto_integral_kernel_compl {g : ℝ → E} (hg : Integrable g)
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun T : ℝ ↦ ∫ u in (Ioc (-R) R)ᶜ, kernel T u • g u) atTop (𝓝 0) := by
  let s := (Ioc (-R) R)ᶜ
  let q := s.indicator fun u : ℝ ↦ (π * u)⁻¹ • g u
  have hs : MeasurableSet s := measurableSet_Ioc.compl
  have hq : Integrable q := by
    apply IntegrableOn.integrable_indicator _ hs
    refine hg.integrableOn.bdd_smul (𝕜 := ℝ) (π * R)⁻¹ (by fun_prop) ?_
    filter_upwards [ae_restrict_mem (μ := volume) hs] with u hu
    rw [norm_inv, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    apply inv_anti₀ (by positivity)
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    by_contra! h
    exact hu ⟨by linarith [neg_le_abs u], (le_abs_self u).trans h.le⟩
  refine hq.tendsto_integral_sin_smul_atTop.congr fun T ↦ ?_
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ s
  · have hu0 : u ≠ 0 := by
      rintro rfl
      exact hu (by simp [hR, hR.le])
    have hk : kernel T u = Real.sin (2 * π * T * u) * (π * u)⁻¹ := by
      rw [kernel, Real.two_mul_mul_sinc_eq_sin_div hu0, div_eq_mul_inv]
    simp only [q, indicator_of_mem hu, Complex.coe_smul, smul_smul, hk]
  · simp [q, hu]

private theorem tendsto_integral_kernel_comp {f : ℝ → E} {s : Set ℝ}
    (hf : BoundedVariationOn f s) {R : ℝ} (hR : 0 < R) {p : ℝ → ℝ}
    (hp : Monotone p ∨ Antitone p) (hps : MapsTo p (Icc 0 R) s) {l : E}
    (hl : Tendsto (f ∘ p) (𝓝[>] 0) (𝓝 l)) :
    Tendsto (fun T : ℝ ↦ ∫ u in (0 : ℝ)..R, kernel T u • f (p u)) atTop
      (𝓝 ((1 / 2 : ℝ) • l)) := by
  let g := IccExtend hR.le ((f ∘ p) ∘ Subtype.val)
  have hvar : BoundedVariationOn (f ∘ p) (Icc 0 R) := by
    rcases hp with hp | hp
    · exact ((eVariationOn.comp_le_of_monotoneOn f p (hp.monotoneOn _) hps).trans_lt hf.lt_top).ne
    · exact ((eVariationOn.comp_le_of_antitoneOn f p (hp.antitoneOn _) hps).trans_lt hf.lt_top).ne
  have hg : BoundedVariationOn g univ := hvar.IccExtend hR.le
  have heq {u : ℝ} (hu : u ∈ Icc 0 R) : g u = f (p u) := IccExtend_of_mem _ _ hu
  have hlim : g.rightLim 0 = l := by
    apply rightLim_eq_of_tendsto
    refine hl.congr' ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iic_mem_nhds hR)] with u h₁ h₂
    exact (heq ⟨h₁.le, h₂⟩).symm
  rw [← hlim]
  refine (tendsto_integral_kernel_of_boundedVariationOn hg hR).congr fun T ↦ ?_
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hR.le]
  exact fun u hu ↦ congrArg (kernel T u • ·) (heq hu)

omit [CompleteSpace E] in
private theorem integrable_kernel_smul {g : ℝ → E} (hg : Integrable g) (T : ℝ) :
    Integrable (fun u ↦ kernel T u • g u) :=
  hg.bdd_smul (𝕜 := ℝ) (2 * |T|) (continuous_kernel T).aestronglyMeasurable
    (.of_forall fun u ↦ by simpa only [Real.norm_eq_abs] using abs_kernel_le T u)

private theorem tendsto_integral_kernel_window {f : ℝ → E} (hfi : Integrable f)
    {x R : ℝ} (hR : 0 < R) (hf : BoundedVariationOn f (Icc (x - R) (x + R))) :
    Tendsto (fun T : ℝ ↦ ∫ u in -R..R, kernel T u • f (x - u)) atTop
      (𝓝 ((1 / 2 : ℝ) • (f.leftLim x + f.rightLim x))) := by
  have hx : x ∈ interior (Icc (x - R) (x + R)) := by
    rw [interior_Icc]
    exact ⟨by linarith, by linarith⟩
  have hsub : Tendsto (fun u : ℝ ↦ x - u) (𝓝[>] 0) (𝓝[<] x) := by
    have hc : Continuous (fun u : ℝ ↦ x - u) := by fun_prop
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa only [sub_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact sub_lt_self _ hu
  have hadd : Tendsto (fun u : ℝ ↦ x + u) (𝓝[>] 0) (𝓝[>] x) := by
    have hc : Continuous (fun u : ℝ ↦ x + u) := by fun_prop
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa only [add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact lt_add_of_pos_right _ hu
  have hleft := tendsto_integral_kernel_comp hf hR (p := fun u ↦ x - u)
    (.inr fun _ _ huv ↦ sub_le_sub_left huv x)
    (fun u hu ↦ ⟨by linarith [hu.2], by linarith [hu.1]⟩)
    ((hf.tendsto_leftLim_of_mem_interior hx).comp hsub)
  have hright := tendsto_integral_kernel_comp hf hR (p := fun u ↦ x + u)
    (.inl fun _ _ huv ↦ add_le_add_right huv x)
    (fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    ((hf.tendsto_rightLim_of_mem_interior hx).comp hadd)
  have h := hright.add hleft
  rw [← smul_add, add_comm (f.rightLim x)] at h
  refine h.congr fun T ↦ ?_
  have hneg : (∫ u in (0 : ℝ)..R, kernel T u • f (x + u)) =
      ∫ u in -R..0, kernel T u • f (x - u) := by
    rw [← neg_zero, ← intervalIntegral.integral_comp_neg]
    simp [kernel, mul_neg, sub_neg_eq_add]
  rw [hneg]
  exact intervalIntegral.integral_add_adjacent_intervals
    (integrable_kernel_smul (hfi.comp_sub_left x) T).intervalIntegrable
    (integrable_kernel_smul (hfi.comp_sub_left x) T).intervalIntegrable

/-- **Dirichlet–Jordan Fourier inversion.** At a point where an integrable function has bounded
variation on a neighbourhood, the finite symmetric inverse Fourier integrals converge to the
mean of its left and right limits. -/
theorem _root_.MeasureTheory.Integrable.tendsto_intervalIntegral_fourierInv_of_boundedVariationOn
    {f : ℝ → E} (hf : Integrable f) {x R : ℝ} (hR : 0 < R)
    (hvar : BoundedVariationOn f (Icc (x - R) (x + R))) :
    Tendsto (fun T : ℝ ↦ ∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t) atTop
      (𝓝 ((1 / 2 : ℝ) • (f.leftLim x + f.rightLim x))) := by
  have hg := hf.comp_sub_left x
  have h := (TauCeti.tendsto_integral_kernel_window hf hR hvar).add
    (TauCeti.tendsto_integral_kernel_compl hg hR)
  rw [add_zero] at h
  refine h.congr fun T ↦ ?_
  rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R),
    integral_add_compl measurableSet_Ioc (TauCeti.integrable_kernel_smul hg T),
    hf.intervalIntegral_fourierInv_fourier_eq_integral_sinc]
  simp only [TauCeti.kernel, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.coe_smul]

end TauCeti
