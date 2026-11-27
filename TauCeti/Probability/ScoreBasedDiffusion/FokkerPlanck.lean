/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.DenoisingDiffusion.SmoothedDensity
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.PDE.HeatKernel.Derivatives
import TauCeti.Analysis.PDE.HeatKernel.HeatEquation

/-!
# The Fokker–Planck equation of a Gaussian noising path

For an arbitrary finite data measure, the Gaussian smoothed density solves the pointwise
Fokker–Planck equation along differentiable signal and noise paths. No moment hypothesis on
the data measure is needed. All formulas require nonzero noise. The noise derivative holds
for every signal, including zero. The other formulas require nonzero signal.

The forward equation is the one in Song, Sohl-Dickstein, Kingma, Kumar, Ermon and Poole,
*Score-Based Generative Modeling through Stochastic Differential Equations* (2021),
Appendix D.1, equation (35). The pointwise identities for arbitrary finite measures are
proved here by dominated differentiation of the Gaussian mixture.
-/

public section

noncomputable section

open MeasureTheory Real InnerProductSpace Laplacian Filter Set
open scoped RealInnerProductSpace ContDiff Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {μ₀ : Measure (EuclideanSpace ℝ ι)} [IsFiniteMeasure μ₀]

private def kernelDeriv (y x : EuclideanSpace ℝ ι) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (-fderiv ℝ (heatKernel p.2) (y - p.1 • x) x) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (Δ (heatKernel p.2 : EuclideanSpace ℝ ι → ℝ) (y - p.1 • x)) • ContinuousLinearMap.snd ℝ ℝ ℝ

omit [DecidableEq ι] in
private theorem hasFDerivAt_kernel (y x : EuclideanSpace ℝ ι) {p : ℝ × ℝ}
    (hp : 0 < p.2) :
    HasFDerivAt (fun q : ℝ × ℝ ↦ heatKernel q.2 (y - q.1 • x)) (kernelDeriv y x p) p := by
  classical
  have hshift : DifferentiableAt ℝ (fun q : ℝ × ℝ ↦ (q.2, y - q.1 • x)) p := by fun_prop
  have hd := (differentiableAt_heatKernel_uncurry (p := (p.2, y - p.1 • x)) hp).comp p hshift
  have h₁ := hd.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  have h₂ := hd.hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have hs := ((contDiff_heatKernel p.2 (k := ∞)).differentiable
    (by simp)).differentiableAt.hasFDerivAt
    |>.comp_hasDerivAt p.1 ((hasDerivAt_const p.1 y).sub ((hasDerivAt_id p.1).smul_const x))
  have he₁ := h₁.unique hs
  have he₂ := h₂.unique (hasDerivAt_heatKernel hp (y - p.1 • x))
  refine hd.hasFDerivAt.congr_fderiv ?_
  simp only [one_smul, id_eq, zero_sub, map_neg] at he₁
  apply ContinuousLinearMap.prod_ext <;> apply ContinuousLinearMap.ext_ring
  · simpa [kernelDeriv] using he₁
  · simpa [kernelDeriv] using he₂

omit [DecidableEq ι] in
private theorem norm_signalDerivative_le (y x : EuclideanSpace ℝ ι) {c v δ B₀ B₁ : ℝ}
    (hδ : 0 < δ) (hc : δ ≤ |c|)
    (h₀ : ‖fderiv ℝ (heatKernel v) (y - c • x)‖ ≤ |B₀|)
    (h₁ : ‖fderiv ℝ (heatKernel v) (y - c • x)‖ * ‖y - c • x‖ ≤ |B₁|) :
    ‖fderiv ℝ (heatKernel v) (y - c • x) x‖ ≤ (|B₀| * ‖y‖ + |B₁|) / δ := by
  let z := y - c • x
  have hc' : 0 < |c| := hδ.trans_le hc
  have hx : ‖x‖ ≤ (‖y‖ + ‖z‖) / |c| := by
    apply (le_div_iff₀ hc').2
    simpa [z, norm_smul, mul_comm] using norm_sub_le y (y - c • x)
  calc
    _ ≤ ‖fderiv ℝ (heatKernel v) z‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (heatKernel v) z‖ * ((‖y‖ + ‖z‖) / |c|) := by gcongr
    _ = (‖fderiv ℝ (heatKernel v) z‖ * ‖y‖ +
        ‖fderiv ℝ (heatKernel v) z‖ * ‖z‖) / |c| := by ring
    _ ≤ (|B₀| * ‖y‖ + |B₁|) / δ := by gcongr

omit [DecidableEq ι] in
private theorem exists_eventually_norm_kernelDeriv_le (y : EuclideanSpace ℝ ι)
    {p : ℝ × ℝ} (hc : p.1 ≠ 0) (ht : 0 < p.2) :
    ∃ B : ℝ, ∀ᶠ q in 𝓝 p, 0 < q.2 ∧ ∀ x, ‖kernelDeriv y x q‖ ≤ B := by
  obtain ⟨B₀, hB₀⟩ := exists_eventually_norm_iteratedFDeriv_heatKernel_mul_rpow_le
    (E := EuclideanSpace ℝ ι) ht 1 (α := 0) le_rfl
  obtain ⟨B₁, hB₁⟩ := exists_eventually_norm_iteratedFDeriv_heatKernel_mul_rpow_le
    (E := EuclideanSpace ℝ ι) ht 1 (α := 1) zero_le_one
  obtain ⟨B₂, hB₂⟩ := exists_eventually_norm_iteratedFDeriv_heatKernel_mul_rpow_le
    (E := EuclideanSpace ℝ ι) ht 2 (α := 0) le_rfl
  have hcl : 0 < |p.1| / 2 := by positivity
  have hcn : ∀ᶠ q : ℝ × ℝ in 𝓝 p, |p.1| / 2 < |q.1| :=
    (continuousAt_fst.abs).eventually (eventually_gt_nhds (by linarith : |p.1| / 2 < |p.1|))
  refine ⟨(|B₀| * ‖y‖ + |B₁|) / (|p.1| / 2) +
    Module.finrank ℝ (EuclideanSpace ℝ ι) * |B₂|, ?_⟩
  filter_upwards [continuousAt_snd.eventually hB₀, continuousAt_snd.eventually hB₁,
    continuousAt_snd.eventually hB₂, hcn,
    continuousAt_snd.eventually (eventually_gt_nhds ht)] with q h₀ h₁ h₂ hq hqt
  refine ⟨hqt, fun x ↦ ?_⟩
  let z := y - q.1 • x
  have hd₀ : ‖fderiv ℝ (heatKernel q.2) z‖ ≤ |B₀| := by
    simpa only [rpow_zero, mul_one, norm_iteratedFDeriv_one] using (h₀ z).trans (le_abs_self _)
  have hd₁ : ‖fderiv ℝ (heatKernel q.2) z‖ * ‖z‖ ≤ |B₁| := by
    simpa only [rpow_one, norm_iteratedFDeriv_one] using (h₁ z).trans (le_abs_self _)
  have hsignal := norm_signalDerivative_le y x hcl hq.le hd₀ hd₁
  have hd₂ : ‖iteratedFDeriv ℝ 2 (heatKernel q.2) z‖ ≤ |B₂| := by
    simpa only [rpow_zero, mul_one] using (h₂ z).trans (le_abs_self _)
  have hlap : ‖Δ (heatKernel q.2 : EuclideanSpace ℝ ι → ℝ) z‖ ≤
      Module.finrank ℝ (EuclideanSpace ℝ ι) * |B₂| :=
    (norm_laplacian_le_norm_iteratedFDeriv_two _ _).trans
      (mul_le_mul_of_nonneg_left hd₂ (Nat.cast_nonneg _))
  unfold kernelDeriv
  calc
    _ ≤ ‖(-fderiv ℝ (heatKernel q.2) z x) • ContinuousLinearMap.fst ℝ ℝ ℝ‖ +
        ‖(Δ (heatKernel q.2 : EuclideanSpace ℝ ι → ℝ) z) •
          ContinuousLinearMap.snd ℝ ℝ ℝ‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ (heatKernel q.2) z x‖ +
        ‖Δ (heatKernel q.2 : EuclideanSpace ℝ ι → ℝ) z‖ := by
      rw [norm_smul, norm_smul, norm_neg]
      exact add_le_add (mul_le_of_le_one_right (norm_nonneg _)
        (ContinuousLinearMap.norm_fst_le ..)) (mul_le_of_le_one_right (norm_nonneg _)
          (ContinuousLinearMap.norm_snd_le ..))
    _ ≤ _ := add_le_add hsignal hlap

omit [DecidableEq ι] in
private theorem continuous_kernelDeriv (y : EuclideanSpace ℝ ι) (p : ℝ × ℝ) :
    Continuous (fun x ↦ kernelDeriv y x p) := by
  have hD : Continuous (fderiv ℝ (heatKernel p.2 : EuclideanSpace ℝ ι → ℝ)) :=
    (contDiff_heatKernel p.2 (k := ∞)).continuous_fderiv (by simp)
  have hΔ : Continuous (Δ (heatKernel p.2 : EuclideanSpace ℝ ι → ℝ)) :=
    (contDiff_heatKernel p.2).continuous_laplacian
  unfold kernelDeriv
  exact (((hD.comp (by fun_prop)).clm_apply continuous_id).neg.smul continuous_const).add
    ((hΔ.comp (by fun_prop)).smul continuous_const)

omit [DecidableEq ι] in
private theorem hasFDerivAt_integral_kernel (y : EuclideanSpace ℝ ι)
    {p : ℝ × ℝ} (hc : p.1 ≠ 0) (ht : 0 < p.2) :
    HasFDerivAt (fun q : ℝ × ℝ ↦ ∫ x, heatKernel q.2 (y - q.1 • x) ∂μ₀)
      (∫ x, kernelDeriv y x p ∂μ₀) p := by
  obtain ⟨B, hB⟩ := exists_eventually_norm_kernelDeriv_le y hc ht
  have hint := integrable_heatKernel_comp ht
    (show AEStronglyMeasurable (fun x : EuclideanSpace ℝ ι ↦ y - p.1 • x) μ₀ by fun_prop)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q : ℝ × ℝ ↦ fun x ↦ heatKernel q.2 (y - q.1 • x))
    (F' := fun q x ↦ kernelDeriv y x q)
    (s := {q : ℝ × ℝ | 0 < q.2 ∧ ∀ x, ‖kernelDeriv y x q‖ ≤ B}) hB
    (.of_forall fun q ↦ (((contDiff_heatKernel q.2 (k := 0)).continuous).comp
      (by fun_prop)).aestronglyMeasurable) hint
    (continuous_kernelDeriv y p).aestronglyMeasurable
    (.of_forall fun x q hq ↦ hq.2 x) (integrable_const B)
    (.of_forall fun x q hq ↦ hasFDerivAt_kernel y x hq.1)

omit [DecidableEq ι] in
private theorem neg_fderiv_heatKernel_sub_smul_apply (x y : EuclideanSpace ℝ ι)
    {c v : ℝ} (hc : c ≠ 0) :
    -fderiv ℝ (heatKernel v) (y - c • x) x =
      -(1 / c) * (Module.finrank ℝ (EuclideanSpace ℝ ι) * heatKernel v (y - c • x) +
        fderiv ℝ (heatKernel v) (y - c • x) y) -
      (2 * v / c) * Δ (heatKernel v : EuclideanSpace ℝ ι → ℝ) (y - c • x) := by
  set z := y - c • x
  let D := fderiv ℝ (heatKernel v) z
  have hEuler : D z = -(Module.finrank ℝ (EuclideanSpace ℝ ι) * heatKernel v z) -
      (2 * v) * Δ (heatKernel v : EuclideanSpace ℝ ι → ℝ) z :=
    fderiv_heatKernel_apply_self v z
  have hshift : z + c • x = y := sub_add_cancel _ _
  have hDy : D z + c * D x = D y := by
    simpa only [map_add, map_smul, smul_eq_mul] using congrArg D hshift
  -- Express the signal derivative using the spatial derivative in the observation direction.
  calc
    -fderiv ℝ (heatKernel v) z x = (D z - D y) / c := by
      rw [← hDy]
      field_simp [hc]
      ring
    _ = _ := by rw [hEuler]; ring

private theorem integral_neg_fderiv_heatKernel_sub_smul_apply {c s : ℝ}
    (hc : c ≠ 0) (hs : s ≠ 0) (y : EuclideanSpace ℝ ι) :
    (∫ x, -fderiv ℝ (heatKernel (s ^ 2 / 2)) (y - c • x) x ∂μ₀) =
      -(1 / c) * (Fintype.card ι * smoothedDensity μ₀ c s y +
        ⟪y, gradient (smoothedDensity μ₀ c s) y⟫) -
      (s ^ 2 / c) * Δ (smoothedDensity μ₀ c s) y := by
  have hv : 0 < s ^ 2 / 2 := by positivity
  have hshift : AEStronglyMeasurable (fun x : EuclideanSpace ℝ ι ↦ y - c • x) μ₀ := by
    fun_prop
  have hintK := integrable_heatKernel_comp hv hshift
  have hintD := integrable_fderiv_heatKernel_comp hv hshift
  have hintDy : Integrable (fun x ↦ fderiv ℝ (heatKernel (s ^ 2 / 2)) (y - c • x) y) μ₀ :=
    (ContinuousLinearMap.apply ℝ ℝ y).integrable_comp hintD
  have hintΔ := integrable_laplacian_heatKernel_comp hv hshift
  have hvs : 2 * (s ^ 2 / 2) = s ^ 2 := by ring
  have hpoint (x : EuclideanSpace ℝ ι) :
      -fderiv ℝ (heatKernel (s ^ 2 / 2)) (y - c • x) x =
        -(1 / c) * (Fintype.card ι * heatKernel (s ^ 2 / 2) (y - c • x) +
          fderiv ℝ (heatKernel (s ^ 2 / 2)) (y - c • x) y) -
        (s ^ 2 / c) *
          Δ (heatKernel (s ^ 2 / 2) : EuclideanSpace ℝ ι → ℝ) (y - c • x) := by
    have h := neg_fderiv_heatKernel_sub_smul_apply (v := s ^ 2 / 2) x y hc
    rwa [finrank_euclideanSpace, hvs] at h
  have hintSum : Integrable (fun x ↦ (Fintype.card ι : ℝ) *
      heatKernel (s ^ 2 / 2) (y - c • x) + fderiv ℝ (heatKernel (s ^ 2 / 2)) (y - c • x) y) μ₀ :=
    (hintK.const_mul _).add hintDy
  simp_rw [hpoint]
  rw [integral_sub (hintSum.const_mul (-(1 / c))) (hintΔ.const_mul (s ^ 2 / c))]
  simp only [integral_const_mul, integral_add (hintK.const_mul (Fintype.card ι : ℝ)) hintDy]
  have hgradient :
      (∫ x, fderiv ℝ (heatKernel (s ^ 2 / 2)) (y - c • x) y ∂μ₀) =
        ⟪y, gradient (smoothedDensity μ₀ c s) y⟫ := by
    rw [← ContinuousLinearMap.integral_apply hintD, ← fderiv_smoothedDensity hs]
    rw [← inner_gradient_left, real_inner_comm y]
  rw [← smoothedDensity_eq_integral_heatKernel hs, hgradient, ← laplacian_smoothedDensity hs]

private theorem integral_kernelDeriv {c s : ℝ} (hc : c ≠ 0) (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    (∫ x, kernelDeriv y x (c, s ^ 2 / 2) ∂μ₀) =
      (-(1 / c) * (Fintype.card ι * smoothedDensity μ₀ c s y +
        ⟪y, gradient (smoothedDensity μ₀ c s) y⟫) -
        (s ^ 2 / c) * Δ (smoothedDensity μ₀ c s) y) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      Δ (smoothedDensity μ₀ c s) y • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  obtain ⟨B, hB⟩ := exists_eventually_norm_kernelDeriv_le y
    (p := (c, s ^ 2 / 2)) hc (by positivity)
  have hint : Integrable (fun x ↦ kernelDeriv y x (c, s ^ 2 / 2)) μ₀ :=
    Integrable.of_bound (continuous_kernelDeriv y _).aestronglyMeasurable B
      (.of_forall fun x ↦ hB.self_of_nhds.2 x)
  apply ContinuousLinearMap.prod_ext <;> apply ContinuousLinearMap.ext_ring
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.integral_apply hint]
    simpa [kernelDeriv] using
      integral_neg_fderiv_heatKernel_sub_smul_apply (μ₀ := μ₀) hc hs y
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.integral_apply hint]
    simpa [kernelDeriv] using (laplacian_smoothedDensity (μ₀ := μ₀) (c := c) hs y).symm

/-- **Noise derivative of the smoothed density.** This includes zero signal and negative noise
levels, since the smoothing depends on the square of the noise. -/
theorem hasDerivAt_smoothedDensity_noise {c s : ℝ} (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    HasDerivAt (fun r ↦ smoothedDensity μ₀ c r y)
      (s * Δ (smoothedDensity μ₀ c s) y) s := by
  have h := (hasDerivAt_integral_heatKernel (μ := μ₀) (z := fun x ↦ y - c • x)
    (by positivity : 0 < s ^ 2 / 2) (by fun_prop)).comp s
      (((hasDerivAt_id s).pow 2).div_const 2)
  have hd : (∫ x, Δ (heatKernel (s ^ 2 / 2) : EuclideanSpace ℝ ι → ℝ)
      (y - c • x) ∂μ₀) * (2 * s ^ (2 - 1) * 1 / 2) =
      s * Δ (smoothedDensity μ₀ c s) y := by
    rw [laplacian_smoothedDensity hs]
    ring
  exact (h.congr_deriv hd).congr_of_eventuallyEq
    ((eventually_ne_nhds hs).mono fun r hr ↦ smoothedDensity_eq_integral_heatKernel hr y)

/-- **Joint derivative in signal and noise.** This can be composed with differentiable maps
into the level parameters, without requiring any moment of the data measure. -/
theorem hasFDerivAt_smoothedDensity_level {c s : ℝ} (hc : c ≠ 0) (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun q : ℝ × ℝ ↦ smoothedDensity μ₀ q.1 q.2 y)
      ((-(1 / c) * (Fintype.card ι * smoothedDensity μ₀ c s y +
        ⟪y, gradient (smoothedDensity μ₀ c s) y⟫) -
          (s ^ 2 / c) * Δ (smoothedDensity μ₀ c s) y) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (s * Δ (smoothedDensity μ₀ c s) y) • ContinuousLinearMap.snd ℝ ℝ ℝ) (c, s) := by
  have hnoise := (((hasDerivAt_id s).pow 2).div_const 2).comp_hasFDerivAt
    (c, s) (hasFDerivAt_snd (𝕜 := ℝ))
  have hlevel := (hasFDerivAt_fst (𝕜 := ℝ)).prodMk hnoise
  have h := (hasFDerivAt_integral_kernel (μ₀ := μ₀) y
    (p := (c, s ^ 2 / 2)) hc (by positivity)).comp (c, s) hlevel
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq
    ((continuousAt_snd.eventually (eventually_ne_nhds hs)).mono fun q hq ↦
      smoothedDensity_eq_integral_heatKernel hq y)
  rw [integral_kernelDeriv hc hs]
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    add_apply, smul_apply, id_eq,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- **The Fokker–Planck equation along a Gaussian noising path.** The drift is the linear field
`y ↦ (c′ / c t) • y`. Set `g² = 2 * (s t * s′ - (s t)² * c′ / c t)`, twice the Laplacian
coefficient and the squared diffusion coefficient when nonnegative. The formula expands the
forward equation `∂ₜp = -div((c′/c) y p) + (g²/2) Δp`. -/
theorem hasDerivAt_smoothedDensity_path {c s : ℝ → ℝ} {c' s' t : ℝ}
    (hc : HasDerivAt c c' t) (hs : HasDerivAt s s' t)
    (hct : c t ≠ 0) (hst : s t ≠ 0) (y : EuclideanSpace ℝ ι) :
    HasDerivAt (fun r ↦ smoothedDensity μ₀ (c r) (s r) y)
      (-(c' / c t) * (Fintype.card ι * smoothedDensity μ₀ (c t) (s t) y +
        ⟪y, gradient (smoothedDensity μ₀ (c t) (s t)) y⟫) +
        (s t * s' - (s t) ^ 2 * c' / c t) *
          Δ (smoothedDensity μ₀ (c t) (s t)) y) t := by
  have h := (hasFDerivAt_smoothedDensity_level (μ₀ := μ₀) hct hst y).comp_hasDerivAt t
    (hc.prodMk hs)
  apply h.congr_deriv
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- **Signal derivative of the smoothed density.** No moment condition on the data is required
away from zero signal. -/
theorem hasDerivAt_smoothedDensity_signal {c s : ℝ} (hc : c ≠ 0) (hs : s ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    HasDerivAt (fun r ↦ smoothedDensity μ₀ r s y)
      (-(1 / c) * (Fintype.card ι * smoothedDensity μ₀ c s y +
        ⟪y, gradient (smoothedDensity μ₀ c s) y⟫) -
        (s ^ 2 / c) * Δ (smoothedDensity μ₀ c s) y) c := by
  exact (hasDerivAt_smoothedDensity_path (μ₀ := μ₀)
    (hasDerivAt_id c) (hasDerivAt_const c s) hc hs y).congr_deriv (by
      simp only [id_eq]
      ring)

end TauCeti.Probability
