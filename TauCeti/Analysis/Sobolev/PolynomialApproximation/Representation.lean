/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.PolynomialApproximation.AveragedTaylor
public import TauCeti.Analysis.Sobolev.PolynomialApproximation.Kernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Calculus.IteratedGradient.Taylor
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin
import TauCeti.MeasureTheory.Integral.Dilation

/-!
# Smooth and Sobolev Taylor-remainder representation formulas

Averaging the integral remainder of the degree-`m` Taylor polynomial (order `m + 1` in
Brenner–Scott) at `x` against a bounded measurable weight function `φ` with compact support in `Ω`
and unit integral expresses the error `u x - ∫ φ(y) T^m_y u(x) dy` as a double integral over `y`
and the segment parameter `s ∈ (0, 1)` evaluated at `z = x + s • (y - x)`. Applying Fubini's
theorem and the Haar homothety change of variables `y ↦ x + s • (y - x)`
(`Measure.lintegral_comp_homothety`) rewrites this remainder as a spatial integral against
`TauCeti.taylorRemainderKernel φ m x z`:

* for `u ∈ C^{m+1}(Ω)` on any open set `Ω` star-convex with respect to `tsupport φ`, the identity
  `u x - ∫ φ(y) T^m_y u(x) dμ = ∫_{z ∈ Ω} taylorRemainderKernel φ m x z (D^{m+1} u(z)) dμ` holds
  pointwise at every `x ∈ Ω`, without boundedness of `Ω` or global integrability of `D^{m+1} u`;
* on a bounded open set `Ω` star-convex with respect to `tsupport φ`, combining continuity of
  `TauCeti.Wkp.averagedTaylorEval` on `W^{m,1}(Ω)`, its agreement with the classical integral on
  `C^m` representatives, and its invariance under lowering the Sobolev exponent with Meyers–Serrin
  density (`Wkp.exists_contDiffOn_approximation`) and the `L¹(Ω) → L¹(Ω)` potential bound
  `eLpNorm_one_setIntegral_taylorRemainderKernel_le` extends the representation formula almost
  everywhere to every `u ∈ W^{m+1,p}(Ω)` (`1 ≤ p ≤ ∞`).

## Main declarations

* `TauCeti.sub_integral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel`,
  `TauCeti.sub_setIntegral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel`: pointwise
  representation formulas for `C^{m+1}` functions on star-shaped open sets.
* `TauCeti.Wkp.ae_sub_averagedTaylorEval_eq_setIntegral_taylorRemainderKernel`: the Sobolev
  representation formula on `W^{m+1,p}(Ω)` for every `1 ≤ p ≤ ∞`.
* `TauCeti.Wkp.ae_sub_setIntegral_mul_eq_setIntegral_taylorRemainderKernel`: the first-order
  (`m = 0`) specialization on `W^{1,p}(Ω)`.

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, Proposition 4.2.8, pp. 97–99.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Springer,
  §7.4.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff ENNReal Topology

namespace TauCeti

/-! ### Smooth representation formula via homothety ray change of variables -/

section SmoothRepresentation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pointwise rescaling identity relating the `(y, s)` segment integrand and the `(z, s)` spatial
ray integrand along the homothety `y ↦ x + s • (y - x)` for `s > 0`. -/
private theorem ray_integrand_comp_homothety (φ : E → ℝ) {m : ℕ} (G : E → IteratedGradient E m)
    (x y : E) {s : ℝ} (hs : 0 < s) :
    φ (x + s⁻¹ • (AffineMap.homothety x s y - x)) * s ^ (-(finrank ℝ E : ℝ) - 1) *
        IteratedGradient.fullContractL m (x - AffineMap.homothety x s y)
          (G (AffineMap.homothety x s y)) =
      (s ^ finrank ℝ E)⁻¹ * (φ y * s ^ m *
        IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x)))) := by
  set n := finrank ℝ E
  have hhom : AffineMap.homothety x s y = x + s • (y - x) := by
    simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_comm]
  have hinv : x + s⁻¹ • (x + s • (y - x) - x) = y := by
    rw [add_sub_cancel_left, inv_smul_smul₀ hs.ne', add_sub_cancel]
  have hdir : x - (x + s • (y - x)) = s • (x - y) := by
    rw [sub_add_eq_sub_sub, sub_self, zero_sub, ← smul_neg, neg_sub]
  have hexp : s ^ (-(n : ℝ) - 1) * s ^ (m + 1) = (s ^ n)⁻¹ * s ^ m := by
    rw [← Real.rpow_natCast s (m + 1), ← Real.rpow_add hs, ← Real.rpow_natCast s n,
      ← Real.rpow_neg hs.le, ← Real.rpow_natCast s m, ← Real.rpow_add hs]
    congr 1; push_cast; ring
  rw [hhom, hinv, hdir, IteratedGradient.fullContractL_smul_direction,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  calc
    φ y * s ^ (-(n : ℝ) - 1) * (s ^ (m + 1) *
        IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x)))) =
      φ y * (s ^ (-(n : ℝ) - 1) * s ^ (m + 1)) *
        IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x))) := by ring
    _ = (s ^ n)⁻¹ * (φ y * s ^ m *
        IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x)))) := by
      rw [hexp]; ring

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Product integrability of the `(y, s)` segment integrand when `φ` has compact support and both
`φ` and `G` are bounded and strongly measurable. -/
private theorem integrable_segment_prod {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) {m : ℕ}
    {G : E → IteratedGradient E m} (hG_meas : StronglyMeasurable G) {C : ℝ}
    (hG_bound : ∀ z, ‖G z‖ ≤ C) (x : E) :
    Integrable
      (fun p : E × ℝ ↦ φ p.1 * p.2 ^ m *
        IteratedGradient.fullContractL m (x - p.1) (G (x + p.2 • (p.1 - x))))
      (μ.prod ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))) := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hH_meas : StronglyMeasurable fun p : E × ℝ ↦ φ p.1 * p.2 ^ m *
      IteratedGradient.fullContractL m (x - p.1) (G (x + p.2 • (p.1 - x))) := by
    refine (((hφ_meas.comp measurable_fst).mul (measurable_snd.pow_const m)).stronglyMeasurable).mul
      ?_
    exact isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
      ((((IteratedGradient.continuous_fullContractL m).comp
        (continuous_const.sub continuous_fst)).stronglyMeasurable).prodMk
        (hG_meas.comp_measurable (measurable_const.add (measurable_snd.smul
          (measurable_fst.sub measurable_const)))))
  obtain ⟨R, hR, hR_sub⟩ := hcpt.isBounded.subset_closedBall_lt 0 x
  have hsupp : Function.support φ ⊆ closedBall x R := (subset_tsupport φ).trans hR_sub
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hφ_bound 0)
  have hdom : Integrable ((tsupport φ ×ˢ (univ : Set ℝ)).indicator
      (fun _ : E × ℝ ↦ M * R ^ (m + 1) * C)) (μ.prod ν) := by
    rw [integrable_indicator_iff (hcpt.isClosed.measurableSet.prod MeasurableSet.univ)]
    exact integrableOn_const ((Measure.prod_prod (tsupport φ) univ).trans_lt
      (ENNReal.mul_lt_top hcpt.measure_lt_top (measure_lt_top ν univ))).ne
  have hae_s : ∀ᵐ p : E × ℝ ∂μ.prod ν, p.2 ∈ Ioo (0 : ℝ) 1 := by
    have hnull : (μ.prod ν) (univ ×ˢ (Ioo (0 : ℝ) 1)ᶜ) = 0 := by
      rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioo.compl,
        compl_inter_self, measure_empty, mul_zero]
    exact Filter.eventually_of_mem (compl_mem_ae_iff.2 hnull) fun p hp ↦
      by_contra fun hnot ↦ hp ⟨mem_univ p.1, hnot⟩
  refine hdom.mono' hH_meas.aestronglyMeasurable ?_
  filter_upwards [hae_s] with p hp
  by_cases hp1 : p.1 ∈ tsupport φ
  · rw [indicator_of_mem (s := tsupport φ ×ˢ (univ : Set ℝ)) ⟨hp1, mem_univ p.2⟩,
      mul_right_comm (φ p.1) (p.2 ^ m), norm_mul]
    have hs1 : ‖p.2 ^ m‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (pow_nonneg hp.1.le m)]
      exact pow_le_one₀ hp.1.le hp.2.le
    have hfc : ‖φ p.1 * IteratedGradient.fullContractL m (x - p.1)
        (G (x + p.2 • (p.1 - x)))‖ ≤ M * R ^ (m + 1) * C :=
      (norm_mul_fullContractL_le_of_support_subset_closedBall hR.le hsupp (hφ_bound p.1) m _).trans
        (mul_le_mul_of_nonneg_left (hG_bound _) (by positivity))
    simpa only [mul_one] using mul_le_mul hfc hs1 (norm_nonneg _) ((norm_nonneg _).trans hfc)
  · rw [indicator_of_notMem (s := tsupport φ ×ˢ (univ : Set ℝ)) fun h ↦ hp1 h.1,
      image_eq_zero_of_notMem_tsupport hp1, zero_mul, zero_mul, norm_zero]

/-- For a fixed slice `s > 0`, the homothety `y ↦ x + s • (y - x)` equates both the `L¹` lower
integrals and the Bochner integrals of the `(y, s)` segment integrand and the `(z, s)` spatial ray
integrand. -/
private theorem ray_slice_homothety_eq (φ : E → ℝ) {m : ℕ} (G : E → IteratedGradient E m)
    (x : E) {s : ℝ} (hs : 0 < s) :
    (∫⁻ z, ‖φ (x + s⁻¹ • (z - x)) * s ^ (-(finrank ℝ E : ℝ) - 1) *
        IteratedGradient.fullContractL m (x - z) (G z)‖ₑ ∂μ =
      ∫⁻ y, ‖φ y * s ^ m *
        IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x)))‖ₑ ∂μ) ∧
    (∫ y, φ y * s ^ m *
        IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x))) ∂μ =
      ∫ z, φ (x + s⁻¹ • (z - x)) * s ^ (-(finrank ℝ E : ℝ) - 1) *
        IteratedGradient.fullContractL m (x - z) (G z) ∂μ) := by
  set n := finrank ℝ E
  let h : E → ℝ := fun y ↦
    φ y * s ^ m * IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x)))
  let ht : E → ℝ := fun z ↦
    φ (x + s⁻¹ • (z - x)) * s ^ (-(n : ℝ) - 1) * IteratedGradient.fullContractL m (x - z) (G z)
  have hpos : 0 < (s ^ n)⁻¹ := inv_pos.2 (pow_pos hs n)
  have hcomp : ∀ y, ht (AffineMap.homothety x s y) = (s ^ n)⁻¹ * h y :=
    fun y ↦ ray_integrand_comp_homothety φ G x y hs
  refine ⟨?_, ?_⟩
  · have hhom := Measure.lintegral_comp_homothety μ (fun z ↦ ‖ht z‖ₑ) x hs.ne'
    have hpt : ∀ y, ‖ht (AffineMap.homothety x s y)‖ₑ = ENNReal.ofReal |(s ^ n)⁻¹| * ‖h y‖ₑ :=
      fun y ↦ by rw [hcomp y, eNorm_mul, abs_of_pos hpos, Real.eNorm_eq_ofReal hpos.le]
    simp_rw [hpt] at hhom
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hhom
    exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 (abs_pos.2 hpos.ne')).ne'
      ENNReal.ofReal_ne_top).1 hhom.symm
  · apply mul_left_cancel₀ hpos.ne'
    have hboch : ∫ y, ht (x + s • (y - x)) ∂μ = (s ^ n)⁻¹ * ∫ z, ht z ∂μ := by
      rw [integral_sub_right_eq_self (fun w ↦ ht (x + s • w)) x,
        Measure.integral_comp_smul (μ := μ) (fun w ↦ ht (x + w)) s,
        integral_add_left_eq_self ht x, smul_eq_mul, abs_of_pos hpos]
    rw [← integral_const_mul, ← hboch]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    have hhom : x + s • (y - x) = AffineMap.homothety x s y := by
      simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_comm]
    exact ((congrArg ht hhom).trans (hcomp y)).symm

/-- Core Fubini-homothety identity for a strongly measurable, bounded derivative field `G`. -/
private theorem integral_segment_eq_integral_taylorRemainderKernel {φ : E → ℝ}
    (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M)
    {m : ℕ} {G : E → IteratedGradient E m} (hG_meas : StronglyMeasurable G)
    {C : ℝ} (hG_bound : ∀ z, ‖G z‖ ≤ C) (x : E) :
    Integrable (fun z ↦ taylorRemainderKernel φ m x z (G z)) μ ∧
      (m.factorial : ℝ)⁻¹ * ∫ y, φ y * (∫ s in Ioo (0 : ℝ) 1,
          s ^ m * IteratedGradient.fullContractL m (x - y) (G (x + s • (y - x)))) ∂μ =
        ∫ z, taylorRemainderKernel φ m x z (G z) ∂μ := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  let H : E × ℝ → ℝ := fun p ↦
    φ p.1 * p.2 ^ m * IteratedGradient.fullContractL m (x - p.1) (G (x + p.2 • (p.1 - x)))
  let Ht : E × ℝ → ℝ := fun p ↦
    φ (x + p.2⁻¹ • (p.1 - x)) * p.2 ^ (-(finrank ℝ E : ℝ) - 1) *
      IteratedGradient.fullContractL m (x - p.1) (G p.1)
  have hH_int : Integrable H (μ.prod ν) :=
    integrable_segment_prod hφ_meas hcpt hφ_bound hG_meas hG_bound x
  have hHt_meas : StronglyMeasurable Ht := by
    refine (((hφ_meas.comp (measurable_const.add (measurable_snd.inv.smul
        (measurable_fst.sub measurable_const)))).mul
        (measurable_snd.pow_const _)).stronglyMeasurable).mul ?_
    exact isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
      ((((IteratedGradient.continuous_fullContractL m).comp
        (continuous_const.sub continuous_fst)).stronglyMeasurable).prodMk
        (hG_meas.comp_measurable measurable_fst))
  have hHt_int : Integrable Ht (μ.prod ν) := by
    refine ⟨hHt_meas.aestronglyMeasurable, ?_⟩
    have hlint_ae : (fun s ↦ ∫⁻ z, ‖Ht (z, s)‖ₑ ∂μ) =ᵐ[ν] fun s ↦ ∫⁻ y, ‖H (y, s)‖ₑ ∂μ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (ray_slice_homothety_eq (μ := μ) φ G x hs.1).1
    rw [hasFiniteIntegral_def, lintegral_prod_symm _ hHt_meas.eNorm.aemeasurable,
      lintegral_congr_ae hlint_ae, ← lintegral_prod_symm _ hH_int.aestronglyMeasurable.eNorm]
    exact hH_int.hasFiniteIntegral
  have hz_eq :
      ∀ z, (m.factorial : ℝ)⁻¹ * ∫ s, Ht (z, s) ∂ν = taylorRemainderKernel φ m x z (G z) :=
    fun z ↦ by
      dsimp only [Ht, ν]
      rw [integral_mul_const, taylorRemainderKernel_apply, taylorRemainderWeight_def, mul_assoc]
  refine ⟨by
    simpa only [← hz_eq] using hHt_int.integral_prod_left.const_mul (m.factorial : ℝ)⁻¹, ?_⟩
  have hy_in : (∫ y, φ y * (∫ s, s ^ m * IteratedGradient.fullContractL m (x - y)
      (G (x + s • (y - x))) ∂ν) ∂μ) = ∫ y, (∫ s, H (y, s) ∂ν) ∂μ := by
    congr 1 with y; simp only [H, mul_assoc, integral_const_mul]
  rw [hy_in, integral_integral_swap hH_int,
    setIntegral_congr_fun measurableSet_Ioo fun s hs ↦ (ray_slice_homothety_eq φ G x hs.1).2,
    ← integral_integral_swap hHt_int, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall hz_eq)

/-- Compact-cone localization of `integral_segment_eq_integral_taylorRemainderKernel` to a
`C^{m+1}` function on an open set `Ω` star-convex with respect to `tsupport φ`. -/
private theorem integral_segment_iteratedGradientChain_eq_setIntegral {Ω : Set E} (hΩ : IsOpen Ω)
    {φ : E → ℝ} (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ) {M : ℝ}
    (hφ_bound : ∀ y, ‖φ y‖ ≤ M) {u : E → ℝ} {m : ℕ} (hu : ContDiffOn ℝ (m + 1) u Ω)
    {x : E} (hx : x ∈ Ω) (hstar : ∀ y ∈ tsupport φ, StarConvex ℝ y Ω) :
    IntegrableOn (fun z ↦ taylorRemainderKernel φ m x z (iteratedGradientChain u m z)) Ω μ ∧
      (m.factorial : ℝ)⁻¹ * ∫ y, φ y * (∫ s in Ioo (0 : ℝ) 1,
          s ^ m * IteratedGradient.fullContractL m (x - y)
            (iteratedGradientChain u m (x + s • (y - x)))) ∂μ =
        ∫ z in Ω, taylorRemainderKernel φ m x z (iteratedGradientChain u m z) ∂μ := by
  let L : Set E := (fun p : ℝ × E ↦ x + p.1 • (p.2 - x)) '' (Icc (0 : ℝ) 1 ×ˢ tsupport φ)
  have hL_cpt : IsCompact L := (isCompact_Icc.prod hcpt).image (by fun_prop)
  have hL_sub : L ⊆ Ω := fun _ ⟨⟨s, y⟩, ⟨hs, hy⟩, h⟩ ↦ h ▸ by
    have hcomb : s • y + (1 - s) • x = x + s • (y - x) := by module
    simpa only [hcomb] using hstar y hy hx hs.1 (sub_nonneg.2 hs.2) (add_sub_cancel s 1)
  let G : E → IteratedGradient E m := L.indicator (iteratedGradientChain u m)
  have hG_cont : ContinuousOn (iteratedGradientChain u m) L := fun z hz ↦
    (contDiffAt_iteratedGradientChain (m := (0 : ℕ∞ω))
      (hu.contDiffAt (hΩ.mem_nhds (hL_sub hz))) m (by simp)).continuousAt.continuousWithinAt
  have hG_meas : StronglyMeasurable G := by
    have h1 : L.domRestrict G = L.domRestrict (iteratedGradientChain u m) :=
      funext fun ⟨y, hy⟩ ↦ indicator_of_mem hy _
    have h0 : Lᶜ.domRestrict G = fun _ ↦ 0 :=
      funext fun ⟨y, hy⟩ ↦ indicator_of_notMem hy _
    refine stronglyMeasurable_of_restrict_of_restrict_compl hL_cpt.isClosed.measurableSet ?_ ?_
    · rw [h1]; exact hG_cont.domRestrict.stronglyMeasurable
    · rw [h0]; exact stronglyMeasurable_const
  obtain ⟨C₀, hC₀⟩ := hL_cpt.exists_bound_of_continuousOn hG_cont
  have hG_bound : ∀ z, ‖G z‖ ≤ max C₀ 0 := fun z ↦ by
    by_cases hz : z ∈ L
    · simp only [G, indicator_of_mem hz]; exact (hC₀ z hz).trans (le_max_left C₀ 0)
    · simp only [G, indicator_of_notMem hz, norm_zero]; exact le_max_right C₀ 0
  obtain ⟨hKG_int, hcore⟩ := integral_segment_eq_integral_taylorRemainderKernel (μ := μ)
    hφ_meas hcpt hφ_bound hG_meas hG_bound x
  have hK_eq : (fun z ↦ taylorRemainderKernel φ m x z (G z)) =
      Ω.indicator (fun z ↦ taylorRemainderKernel φ m x z (iteratedGradientChain u m z)) := by
    ext z; by_cases hz : z ∈ L
    · simp only [G, indicator_of_mem hz, indicator_of_mem (hL_sub hz)]
    · have hK0 : taylorRemainderKernel φ m x z = 0 := image_eq_zero_of_notMem_tsupport
        fun hts ↦ hz (tsupport_taylorRemainderKernel_subset_image hcpt m x hts)
      by_cases hzΩ : z ∈ Ω
      · simp only [hK0, zero_apply, indicator_of_mem hzΩ]
      · simp only [hK0, zero_apply, indicator_of_notMem hzΩ]
  refine ⟨by rwa [← integrable_indicator_iff hΩ.measurableSet, ← hK_eq], ?_⟩
  rw [← integral_indicator hΩ.measurableSet, ← hK_eq, ← hcore]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  by_cases hy : y ∈ tsupport φ
  · congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun s hs ↦ ?_
    dsimp only [G]
    rw [indicator_of_mem (s := L) ⟨(s, y), ⟨Ioo_subset_Icc_self hs, hy⟩, rfl⟩]
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- **Pointwise representation formula for `C^{m+1}` functions on star-shaped open sets.** Let `Ω`
be an open set, `φ` a bounded measurable function with compact support in `Ω` and `∫ φ ∂μ = 1`,
and `u` a `C^{m+1}` function on `Ω`. If `x ∈ Ω` and `Ω` is star-convex with respect to every point
of `tsupport φ`, then `z ↦ taylorRemainderKernel φ m x z (iteratedGradientChain u m z)` is
integrable on `Ω` and
`u x - ∫ y, φ y * T^m_y u(x) ∂μ = ∫ z in Ω, taylorRemainderKernel φ m x z (D^{m+1} u z) ∂μ`.
No boundedness of `Ω` or global integrability of `D^{m+1} u` is required. -/
theorem sub_integral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel {Ω : Set E}
    (hΩ : IsOpen Ω) {φ : E → ℝ} (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ Ω) (hφ_int : ∫ y, φ y ∂μ = 1) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M)
    {u : E → ℝ} {m : ℕ} (hu : ContDiffOn ℝ (m + 1) u Ω) {x : E} (hx : x ∈ Ω)
    (hstar : ∀ y ∈ tsupport φ, StarConvex ℝ y Ω) :
    IntegrableOn (fun z ↦ taylorRemainderKernel φ m x z (iteratedGradientChain u m z)) Ω μ ∧
      u x - ∫ y, φ y * (∑ j ∈ Finset.range (m + 1),
          (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j u y (fun _ ↦ x - y)) ∂μ =
        ∫ z in Ω, taylorRemainderKernel φ m x z (iteratedGradientChain u m z) ∂μ := by
  obtain ⟨hint_K, hseg_eq⟩ := integral_segment_iteratedGradientChain_eq_setIntegral (μ := μ)
    hΩ hφ_meas hcpt hφ_bound hu hx hstar
  refine ⟨hint_K, ?_⟩
  have hint_mul : ∀ ψ : E → ℝ, ContinuousOn ψ Ω → Integrable (fun y ↦ φ y * ψ y) μ := fun ψ hψ ↦
    (integrableOn_iff_integrable_of_support_subset
      ((Function.support_mul_subset_left φ ψ).trans (subset_tsupport φ))).1
      (((hψ.mono hφ_supp).integrableOn_compact hcpt).bdd_mul
        hφ_meas.aestronglyMeasurable (Eventually.of_forall hφ_bound))
  have hux : u x = ∫ y, φ y * u x ∂μ := by rw [integral_mul_const, hφ_int, one_mul]
  have hsum_cont : ContinuousOn (fun y ↦ ∑ j ∈ Finset.range (m + 1),
      (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j u y (fun _ ↦ x - y)) Ω := by
    simpa only [smul_eq_mul] using continuousOn_sum_iteratedFDeriv hΩ (hu.of_le (by simp)) x
  rw [← hseg_eq, hux, ← integral_sub (hint_mul _ continuousOn_const) (hint_mul _ hsum_cont),
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  by_cases hy : y ∈ tsupport φ
  · have hseg_Ω : ∀ s ∈ Icc (0 : ℝ) 1, x + s • (y - x) ∈ Ω := fun s hs ↦ by
      have hcomb : s • y + (1 - s) • x = x + s • (y - x) := by module
      simpa only [hcomb] using hstar y hy hx hs.1 (sub_nonneg.2 hs.2) (add_sub_cancel s 1)
    rw [← mul_sub, sub_sum_iteratedFDeriv_eq_setIntegral_fullContractL u m x y
      fun s hs ↦ hu.contDiffAt (hΩ.mem_nhds (hseg_Ω s hs))]
    ring
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- Set-integral variant of `sub_integral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel`,
writing the averaged Taylor integral over `Ω` rather than the ambient space. -/
theorem sub_setIntegral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel {Ω : Set E}
    (hΩ : IsOpen Ω) {φ : E → ℝ} (hφ_meas : Measurable φ) (hcpt : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ Ω) (hφ_int : ∫ y, φ y ∂μ = 1) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M)
    {u : E → ℝ} {m : ℕ} (hu : ContDiffOn ℝ (m + 1) u Ω) {x : E} (hx : x ∈ Ω)
    (hstar : ∀ y ∈ tsupport φ, StarConvex ℝ y Ω) :
    u x - ∫ y in Ω, φ y * (∑ j ∈ Finset.range (m + 1),
        (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j u y (fun _ ↦ x - y)) ∂μ =
      ∫ z in Ω, taylorRemainderKernel φ m x z (iteratedGradientChain u m z) ∂μ := by
  have hsupp : Function.support (fun y ↦ φ y * (∑ j ∈ Finset.range (m + 1),
      (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j u y (fun _ ↦ x - y))) ⊆ Ω :=
    (Function.support_mul_subset_left _ _).trans ((subset_tsupport φ).trans hφ_supp)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
    Function.notMem_support.1 fun h ↦ hy (hsupp h)]
  exact (sub_integral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel hΩ hφ_meas hcpt
    hφ_supp hφ_int hφ_bound hu hx hstar).2

end SmoothRepresentation

/-! ### The Sobolev representation formula -/

section SobolevRepresentation

namespace Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Convergence in `L¹(Ω)` of a derivative sequence implies convergence in measure on `Ω` of its
Taylor-remainder kernel integral. -/
private theorem tendstoInMeasure_setIntegral_taylorRemainderKernel
    (hb : Bornology.IsBounded (Omega : Set E)) {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hsupp_cl : Function.support φ ⊆ closure (Omega : Set E)) {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M)
    {m : ℕ} {g : ℕ → Lp (IteratedGradient E m) 1 (mu.restrict Omega)}
    {g₀ : Lp (IteratedGradient E m) 1 (mu.restrict Omega)} (hg : Tendsto g atTop (𝓝 g₀)) :
    TendstoInMeasure (mu.restrict Omega)
      (fun j x ↦ ∫ z in Omega, taylorRemainderKernel φ m x z (g j z) ∂mu) atTop
      (fun x ↦ ∫ z in Omega, taylorRemainderKernel φ m x z (g₀ z) ∂mu) := by
  let ν : Measure E := mu.restrict Omega
  let T : (E → IteratedGradient E m) → E → ℝ := fun G x ↦
    ∫ z in Omega, taylorRemainderKernel φ m x z (G z) ∂mu
  let C : ℝ := M * mu.real (ball (0 : E) 1) / (m + 1).factorial *
    diam (Omega : Set E) ^ (finrank ℝ E + m + 1)
  have hzero_lim : Tendsto (fun j ↦ ENNReal.ofReal C * ENNReal.ofReal ‖g j - g₀‖) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C)
      (ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.1 hg))
      (Or.inr ENNReal.ofReal_ne_top)
  refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero <|
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero_lim (fun _ ↦ zero_le)
      fun j ↦ ?_
  have hsub_ae : T (g j) - T g₀ =ᵐ[ν] T ↑(g j - g₀) := by
    filter_upwards [ae_integrableOn_taylorRemainderKernel_apply hb hφ_meas hsupp_cl hφ_bound
      (L1.integrable_coeFn (g j)),
      ae_integrableOn_taylorRemainderKernel_apply hb hφ_meas hsupp_cl hφ_bound
      (L1.integrable_coeFn g₀)] with x hxj hx0
    dsimp only [Pi.sub_apply, T]
    rw [← integral_sub hxj hx0]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (g j) g₀] with z hz
    rw [hz, Pi.sub_apply, map_sub]
  rw [eLpNorm_congr_ae hsub_ae]
  exact (eLpNorm_one_setIntegral_taylorRemainderKernel_le hb hφ_meas hsupp_cl hφ_bound
    (L1.integrable_coeFn (g j - g₀))).trans_eq (by
      rw [eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable (g j - g₀)),
        ← L1.ofReal_norm_eq_lintegral])

/-- Private `p = 1` core for the Sobolev representation formula via Meyers–Serrin density and the
`L¹(Ω) → L¹(Ω)` potential bound. -/
private theorem ae_sub_averagedTaylorEval_eq_setIntegral_taylorRemainderKernel_one
    (hb : Bornology.IsBounded (Omega : Set E)) {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) (hφ_supp : tsupport φ ⊆ Omega) (hφ_int : ∫ y, φ y ∂mu = 1)
    {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (hstar : ∀ y ∈ tsupport φ, StarConvex ℝ y Omega)
    (m : ℕ) (u : Wkp mu Omega 1 (m + 1)) :
    ∀ᵐ x ∂mu.restrict Omega,
      value (m + 1) u x - averagedTaylorEval φ m (lowerOrder m u) x =
        ∫ z in Omega, taylorRemainderKernel φ m x z (iteratedGradient m u z) ∂mu := by
  let ν : Measure E := mu.restrict Omega
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  have hsupp_cl : Function.support φ ⊆ closure (Omega : Set E) :=
    (subset_tsupport φ).trans (hφ_supp.trans subset_closure)
  obtain ⟨v, f, hf, hae_v, hv⟩ := exists_contDiffOn_approximation ENNReal.one_ne_top (m + 1) u
  have hrep_j : ∀ j, ∀ᵐ x ∂ν, value (m + 1) (v j) x -
      averagedTaylorEval φ m (lowerOrder m (v j)) x =
        ∫ z in Omega, taylorRemainderKernel φ m x z (iteratedGradient m (v j) z) ∂mu := fun j ↦ by
    have hf_m1 : ContDiffOn ℝ (m + 1) (f j) Omega := (hf j).of_le (by simp)
    have hgrad_j := iteratedGradient_ae_eq_of_contDiffOn m (v j) hf_m1 (hae_v j)
    filter_upwards [hae_v j, ae_restrict_mem Omega.isOpen.measurableSet] with x hxv hxΩ
    have hlow_j : (value m (lowerOrder m (v j)) : E → ℝ) =ᵐ[ν] f j := by
      simpa only [value_succ] using hae_v j
    rw [hxv, averagedTaylorEval_eq_setIntegral_sum_iteratedFDeriv hφ_meas hcpt hφ_supp hφ_bound m
      (lowerOrder m (v j)) ((hf j).of_le (by simp)) hlow_j x,
      sub_setIntegral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel Omega.isOpen hφ_meas
        hcpt hφ_supp hφ_int hφ_bound hf_m1 hxΩ hstar]
    refine integral_congr_ae ?_
    filter_upwards [hgrad_j] with z hz
    rw [hz]
  have hv_val : Tendsto (fun j ↦ value (m + 1) (v j)) atTop (𝓝 (value (m + 1) u)) := by
    rw [← valueL_apply (m + 1) u]
    exact (((valueL (mu := mu) (Omega := Omega) (p := 1) (m + 1)).continuous.tendsto u).comp
      hv).congr fun j ↦ valueL_apply (m + 1) (v j)
  obtain ⟨ns₁, hns₁_mono, hae_val⟩ := (tendstoInMeasure_of_tendsto_Lp hv_val).exists_seq_tendsto_ae
  have hg : Tendsto (fun j ↦ iteratedGradient m (v j)) atTop (𝓝 (iteratedGradient m u)) := by
    rw [← iteratedGradientL_apply m u]
    exact (((iteratedGradientL (mu := mu) (Omega := Omega) (p := 1) m).continuous.tendsto u).comp
      hv).congr fun j ↦ iteratedGradientL_apply m (v j)
  obtain ⟨ns₂, hns₂_mono, hae_T⟩ :=
    ((tendstoInMeasure_setIntegral_taylorRemainderKernel hb hφ_meas hsupp_cl hφ_bound hg).comp
      hns₁_mono.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hae_val, hae_T, ae_all_iff.2 hrep_j] with x hx_val hx_T hx_rep
  have hlow_x : Continuous fun w : Wkp mu Omega 1 (m + 1) ↦
      averagedTaylorEval φ m (lowerOrder m w) x :=
    ((continuous_averagedTaylorEval_one hφ_meas hcpt hφ_bound m x).comp
      (lowerOrderL (mu := mu) (Omega := Omega) (p := 1) m).continuous).congr
      fun w ↦ by dsimp only [Function.comp_apply]; rw [lowerOrderL_apply]
  have hsub_tendsto := (hx_val.comp hns₂_mono.tendsto_atTop).sub
    ((hlow_x.tendsto u).comp (hv.comp (hns₁_mono.comp hns₂_mono).tendsto_atTop))
  exact tendsto_nhds_unique hsub_tendsto
    (hx_T.congr fun k ↦ (hx_rep (ns₁ (ns₂ k))).symm)

/-- **The Sobolev representation formula** (Brenner–Scott, Proposition 4.2.8). Let `Ω` be a bounded
open set, `φ` a bounded measurable cutoff with compact support in `Ω` and `∫ φ ∂μ = 1`, and assume
`Ω` is star-convex with respect to every point of `tsupport φ`. For every `1 ≤ p ≤ ∞`, every
`m : ℕ`, and every `u ∈ W^{m+1,p}(Ω)`, almost everywhere on `Ω`,
`value (m + 1) u x - averagedTaylorEval φ m (lowerOrder m u) x =
  ∫ z in Ω, taylorRemainderKernel φ m x z (iteratedGradient m u z) ∂μ`. -/
theorem ae_sub_averagedTaylorEval_eq_setIntegral_taylorRemainderKernel
    (hb : Bornology.IsBounded (Omega : Set E)) {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) (hφ_supp : tsupport φ ⊆ Omega) (hφ_int : ∫ y, φ y ∂mu = 1)
    {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (hstar : ∀ y ∈ tsupport φ, StarConvex ℝ y Omega)
    (m : ℕ) (u : Wkp mu Omega p (m + 1)) :
    ∀ᵐ x ∂mu.restrict Omega,
      value (m + 1) u x - averagedTaylorEval φ m (lowerOrder m u) x =
        ∫ z in Omega, taylorRemainderKernel φ m x z (iteratedGradient m u z) ∂mu := by
  have : IsFiniteMeasure (mu.restrict (Omega : Set E)) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  let u₁ : Wkp mu Omega 1 (m + 1) := ofExponentLEL hp1 (m + 1) u
  have hgrad_ae := iteratedGradient_ofExponentLEL_ae hp1 m u
  filter_upwards [value_ofExponentLEL_ae hp1 (m + 1) u,
    ae_sub_averagedTaylorEval_eq_setIntegral_taylorRemainderKernel_one hb hφ_meas hcpt hφ_supp
      hφ_int hφ_bound hstar m u₁] with x hval hrep
  rw [← hval, ← averagedTaylorEval_ofExponentLEL hp1 φ m (lowerOrder m u) x,
    ← lowerOrder_ofExponentLEL hp1 m u, hrep]
  refine integral_congr_ae ?_
  filter_upwards [hgrad_ae] with z hz
  rw [hz]

/-- First-order (`m = 0`) specialization of the Sobolev representation formula on `W^{1,p}(Ω)`. -/
theorem ae_sub_setIntegral_mul_eq_setIntegral_taylorRemainderKernel
    (hb : Bornology.IsBounded (Omega : Set E)) {φ : E → ℝ} (hφ_meas : Measurable φ)
    (hcpt : HasCompactSupport φ) (hφ_supp : tsupport φ ⊆ Omega) (hφ_int : ∫ y, φ y ∂mu = 1)
    {M : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ M) (hstar : ∀ y ∈ tsupport φ, StarConvex ℝ y Omega)
    (u : Wkp mu Omega p 1) :
    ∀ᵐ x ∂mu.restrict Omega,
      value 1 u x - (∫ y in Omega, φ y * value 1 u y ∂mu) =
        ∫ z in Omega, taylorRemainderKernel φ 0 x z (iteratedGradient 0 u z) ∂mu := by
  simpa only [averagedTaylorEval_zero, value_succ, value_zero] using
    ae_sub_averagedTaylorEval_eq_setIntegral_taylorRemainderKernel hb hφ_meas hcpt hφ_supp hφ_int
      hφ_bound hstar 0 u

end Wkp

end SobolevRepresentation

/-! ### Concrete checks -/

section Examples

/-- One-dimensional first-order sign check: on `Ω = (-1, 1)` with cutoff
`φ = 1_{[-1/2, 1/2]}`, `u = id`, `m = 0`, and `x = 1/2`, the kernel integral against `D¹(id)`
evaluates to `+1/2` (`id (1/2) - ∫_{-1/2}^{1/2} y dy = 1/2`). -/
example :
    let φ : ℝ → ℝ := (Icc (-1 / 2 : ℝ) (1 / 2)).indicator fun _ ↦ 1
    ∫ z in Ioo (-1 : ℝ) 1, taylorRemainderKernel φ 0 (1 / 2) z (iteratedGradientChain id 0 z) =
      1 / 2 := by
  intro φ
  have hφ_meas : Measurable φ := measurable_const.indicator measurableSet_Icc
  have hsub_supp : Function.support φ ⊆ Icc (-1 / 2 : ℝ) (1 / 2) := fun y hy ↦
    by_contra fun hnot ↦ hy (indicator_of_notMem hnot _)
  have hcpt : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsub_supp
  have hφ_supp : tsupport φ ⊆ Ioo (-1 : ℝ) 1 :=
    (closure_minimal hsub_supp isClosed_Icc).trans fun y hy ↦
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hle : (-1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
  have hφ_int : ∫ y, φ y = 1 := by
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, intervalIntegral.integral_const]
    norm_num
  have hφ_bound : ∀ y, ‖φ y‖ ≤ 1 := fun y ↦ by
    dsimp only [φ]
    by_cases hy : y ∈ Icc (-1 / 2 : ℝ) (1 / 2)
    · rw [indicator_of_mem hy]; norm_num
    · rw [indicator_of_notMem hy]; norm_num
  have hx_mem : (1 / 2 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  have hrep := (sub_integral_sum_iteratedFDeriv_eq_setIntegral_taylorRemainderKernel isOpen_Ioo
    hφ_meas hcpt hφ_supp hφ_int hφ_bound (u := id) (m := 0) contDiffOn_id hx_mem
    fun y hy ↦ (convex_Ioo (-1 : ℝ) 1).starConvex (hφ_supp hy)).2
  have hmean : ∫ y, φ y * (∑ j ∈ Finset.range 1,
      (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j (id : ℝ → ℝ) y (fun _ ↦ 1 / 2 - y)) = 0 := by
    have heq : (fun y : ℝ ↦ φ y * (∑ j ∈ Finset.range 1,
        (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j (id : ℝ → ℝ) y (fun _ ↦ 1 / 2 - y))) =
        (Icc (-1 / 2 : ℝ) (1 / 2)).indicator fun y ↦ y := by
      ext y
      dsimp only [φ]
      by_cases hy : y ∈ Icc (-1 / 2 : ℝ) (1 / 2)
      · rw [indicator_of_mem hy, indicator_of_mem hy]; simp
      · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]
    rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, integral_id]
    norm_num
  rw [← hrep, hmean]
  norm_num

/-- Polynomial exactness check: for `u = id` and `m = 1` on `Ω = (-1, 1)`, the second iterated
gradient vanishes everywhere, so the Taylor-remainder kernel integral is `0`. -/
example (x : ℝ) :
    let φ : ℝ → ℝ := (Icc (-1 / 2 : ℝ) (1 / 2)).indicator fun _ ↦ 1
    ∫ z in Ioo (-1 : ℝ) 1,
      taylorRemainderKernel φ 1 x z (iteratedGradientChain (id : ℝ → ℝ) 1 z) = 0 := by
  intro φ
  have h1 : iteratedGradientChain (id : ℝ → ℝ) 0 = fun _ ↦ (1 : ℝ) := by
    ext y
    apply ext_inner_right ℝ fun v ↦ ?_
    rw [iteratedGradientChain_zero, gradient, InnerProductSpace.toDual_symm_apply, fderiv_id]
    simp
  have hzero : ∀ z : ℝ, iteratedGradientChain (id : ℝ → ℝ) 1 z = 0 := fun z ↦ by
    rw [iteratedGradientChain_succ, h1, fderiv_const_apply]
  simp [hzero]

end Examples

end TauCeti
