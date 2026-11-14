/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.ODE.Volterra.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Integral.Bochner.Cumulative

/-!
# Differentiation and `C¹` regularity of Volterra integral equations

This file develops differentiation under the integral sign for variable-lower-limit upper-tail
Volterra integrals and deduces differentiability, derivative error bounds, and `C¹` regularity for
solutions of Volterra integral equations (`TauCeti.Analysis.ODE.Volterra.Basic`).

When `K` extends continuously to `{p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2}` with vanishing diagonal
(`K x x = 0`) and its first partial derivative `K₁ x v` in `x` (for `x < v`) satisfies
`‖K₁ x v‖ ≤ P₁ x * Q v` with continuous `P₁` (with no sign assumption on `P₁` and no diagonal
continuity assumption on `K₁`), extending `u ↦ K u v • g v` by `0` for `u > v` produces a locally
Lipschitz family in `u`. Differentiation under the integral sign
(`TauCeti.hasDerivAt_integral_kernel_smul_Ioi_of_diag_zero`) then shows that every measurable
`O(P)` solution `h` of the Volterra equation on `I` has derivative
`∫ v in I ∩ Ioi x, K₁ x v • (J v + ψ v • h v)`, is `C¹` on `I`, and satisfies Olver's derivative
error bounds:

* `‖deriv h x‖ ≤ P₁ x * Φ x * exp (Ψ x)` (`TauCeti.norm_deriv_volterra_solution_le_on`, Olver
  Theorem 10.1), and
* `P₀ * ‖deriv h x‖ ≤ P₁ x * M * (exp (P₀ * Φ_ψ x) - 1)` when `P = P₀` is constant and
  `‖J v‖ ≤ M * ‖ψ v‖` (`TauCeti.mul_norm_deriv_volterra_solution_le_mul_exp_sub_one_on`, Olver
  Theorem 10.2).

For a general kernel whose diagonal need not vanish, splitting off a compact initial segment yields
the full Leibniz rule with boundary term `-(K x x • g x)`
(`TauCeti.hasDerivAt_integral_kernel_smul_Ioi`).

## Main declarations

* `TauCeti.hasDerivAt_integral_kernel_smul_Ioi_of_diag_zero`,
  `TauCeti.hasDerivAt_integral_kernel_smul_Ioi`: differentiation of upper-tail kernel integrals
  with and without vanishing diagonal (Leibniz's rule).
* `TauCeti.hasDerivAt_volterra_solution_on`, `TauCeti.norm_deriv_volterra_solution_le_on`,
  `TauCeti.contDiffOn_volterra_solution_on`: differentiability, `P₁ Φ exp Ψ` derivative bound, and
  `C¹` regularity on open sets `I` when `K x x = 0`.
* `TauCeti.mul_norm_deriv_volterra_solution_le_mul_exp_sub_one_on`,
  `TauCeti.mul_norm_deriv_volterra_solution_le_exp_sub_one_on`: sharper `exp (P₀ * Φ_ψ) - 1`
  derivative bounds on open sets `I` for constant `P = P₀`.
* `TauCeti.hasDerivAt_volterra_solution`, `TauCeti.norm_deriv_volterra_solution_le`,
  `TauCeti.contDiffOn_volterra_solution`, `TauCeti.mul_norm_deriv_volterra_solution_le_exp_sub_one`:
  specializations to open rays `(a, ∞)`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 6, §10, Theorems 10.1 and 10.2.
* NIST Digital Library of Mathematical Functions, §§2.7–2.8, <https://dlmf.nist.gov/2.7> and
  <https://dlmf.nist.gov/2.8>.
-/

public section

noncomputable section

open Filter MeasureTheory Set Asymptotics
open scoped Topology ContDiff

namespace TauCeti

/-! ### Differentiation under the integral sign (Leibniz rule for Volterra kernels) -/

private lemma exists_Icc_subset_of_isOpen {I : Set ℝ} (hI : IsOpen I) {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ∃ c₁ c₂, c₁ ∈ I ∧ c₂ ∈ I ∧ c₁ < x₀ ∧ x₀ < c₂ ∧ Icc c₁ c₂ ⊆ I := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hI x₀ hx₀
  have hsub : Icc (x₀ - ε / 2) (x₀ + ε / 2) ⊆ I := fun u hu => by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  exact ⟨x₀ - ε / 2, x₀ + ε / 2, hsub ⟨le_rfl, by linarith⟩, hsub ⟨by linarith, le_rfl⟩,
    by linarith, by linarith, hsub⟩

private lemma inter_Ioi_inter_Ioi_of_lt {I : Set ℝ} {c₁ x : ℝ} (hcx : c₁ < x) :
    (I ∩ Ioi c₁) ∩ Ioi x = I ∩ Ioi x := by
  rw [inter_assoc, Ioi_inter_Ioi, sup_eq_right.mpr hcx.le]

private lemma integrable_indicator_Ioi_restrict {E : Type*} [NormedAddCommGroup E]
    {I : Set ℝ} {c₁ u : ℝ} {f : ℝ → E}
    (hf : IntegrableOn f (I ∩ Ioi u)) :
    Integrable ((Ioi u).indicator f) (volume.restrict (I ∩ Ioi c₁)) := by
  rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ioi]
  exact hf.mono_set fun v hv => ⟨hv.2.1, hv.1⟩

private lemma integral_indicator_Ioi_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Set ℝ} {c₁ u : ℝ} (hcu : c₁ < u) (f : ℝ → E) :
    ∫ v, (Ioi u).indicator f v ∂(volume.restrict (I ∩ Ioi c₁)) = ∫ v in I ∩ Ioi u, f v := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_comm (Ioi u), inter_Ioi_inter_Ioi_of_lt hcu]

private lemma restrict_Ioi_eq (I : Set ℝ) (x : ℝ) :
    (volume.restrict I).restrict (Ioi x) = volume.restrict (I ∩ Ioi x) := by
  rw [Measure.restrict_restrict measurableSet_Ioi, inter_comm]

private lemma integrableOn_mul_exp_tail_on {I : Set ℝ} {w : ℝ → ℝ} {x : ℝ}
    (hw : IntegrableOn w (I ∩ Ioi x)) (c : ℝ) :
    IntegrableOn (fun s => w s * Real.exp (c * ∫ u in I ∩ Ioi s, w u)) (I ∩ Ioi x) := by
  have hw' : IntegrableOn w (Ioi x) (volume.restrict I) := by
    rwa [IntegrableOn, restrict_Ioi_eq]
  have hint := hw'.integrableOn_mul_exp_integral_Ioi c
  simpa only [IntegrableOn, restrict_Ioi_eq] using hint

private lemma mul_integral_mul_exp_tail_on {I : Set ℝ} {w : ℝ → ℝ} {x : ℝ}
    (hw : IntegrableOn w (I ∩ Ioi x)) (c : ℝ) :
    c * ∫ s in I ∩ Ioi x, w s * Real.exp (c * ∫ u in I ∩ Ioi s, w u) =
      Real.exp (c * ∫ s in I ∩ Ioi x, w s) - 1 := by
  have hw' : IntegrableOn w (Ioi x) (volume.restrict I) := by
    rwa [IntegrableOn, restrict_Ioi_eq]
  simpa only [restrict_Ioi_eq] using hw'.mul_integral_Ioi_mul_exp_integral_Ioi c

section KernelDeriv

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  {I : Set ℝ} {K K₁ : ℝ → ℝ → 𝕜} {P P₁ Q : ℝ → ℝ}

private lemma norm_image_sub_kernel_smul_le
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hK₁ : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    {c₁ c₂ M₁ Bv : ℝ} (hIcc : Icc c₁ c₂ ⊆ I) (hM₁0 : 0 ≤ M₁)
    (hK₁_bound : ∀ u ∈ Icc c₁ c₂, ∀ v ∈ I, u < v → ‖K₁ u v‖ ≤ M₁ * Q v)
    {v a b : ℝ} (hv : v ∈ I) (hab : Icc a b ⊆ Icc c₁ c₂) (hle : a ≤ b) (hbv : b ≤ v)
    (y : E) (hBv : Q v * ‖y‖ ≤ Bv) :
    ‖K b v • y - K a v • y‖ ≤ M₁ * Bv * (b - a) := by
  have hcont : ContinuousOn (fun u => K u v • y) (Icc a b) :=
    (hK.comp (continuous_id.prodMk continuous_const).continuousOn
      fun u hu => ⟨hIcc (hab hu), hv, hu.2.trans hbv⟩).smul continuousOn_const
  have hderiv : ∀ u ∈ Ico a b,
      HasDerivWithinAt (fun w => K w v • y) (K₁ u v • y) (Ici u) u := fun u hu =>
    ((hK₁ u (hIcc (hab (Ico_subset_Icc_self hu))) v hv
      (hu.2.trans_le hbv)).smul_const y).hasDerivWithinAt
  have hbd : ∀ u ∈ Ico a b, ‖K₁ u v • y‖ ≤ M₁ * Bv := fun u hu => by
    refine (norm_smul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right
      (hK₁_bound u (hab (Ico_subset_Icc_self hu)) v hv (hu.2.trans_le hbv))
      (norm_nonneg _)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hBv hM₁0
  exact norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv hbd b ⟨hle, le_rfl⟩

/-- Extending `u ↦ K u v • y` by `0` for `u > v` produces a Lipschitz map on `(c₁, c₂) ⊆ I`
whenever `K v v = 0` and `‖K₁ u v‖ ≤ M₁ * Q v` for `u < v`. -/
private lemma lipschitzOnWith_cutoff_kernel_smul
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hK₁ : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    {c₁ c₂ M₁ Bv : ℝ} (hIcc : Icc c₁ c₂ ⊆ I) (hM₁0 : 0 ≤ M₁)
    (hK₁_bound : ∀ u ∈ Icc c₁ c₂, ∀ v ∈ I, u < v → ‖K₁ u v‖ ≤ M₁ * Q v)
    {v : ℝ} (hv : v ∈ I) (hQ0 : 0 ≤ Q v) (y : E) (hBv : Q v * ‖y‖ ≤ Bv) :
    LipschitzOnWith (Real.nnabs (M₁ * Bv))
      (fun u => if u ≤ v then K u v • y else 0) (Ioo c₁ c₂) := by
  set B : ℝ := M₁ * Bv
  have hB0 : 0 ≤ B := mul_nonneg hM₁0 ((mul_nonneg hQ0 (norm_nonneg _)).trans hBv)
  have hpair : ∀ {u₁ u₂ : ℝ}, u₁ ∈ Ioo c₁ c₂ → u₂ ∈ Ioo c₁ c₂ → u₁ ≤ u₂ →
      ‖(if u₂ ≤ v then K u₂ v • y else 0) - (if u₁ ≤ v then K u₁ v • y else 0)‖ ≤
        B * (u₂ - u₁) := by
    intro u₁ u₂ hu₁ hu₂ h12
    have hsub12 : Icc u₁ u₂ ⊆ Icc c₁ c₂ := fun w hw =>
      ⟨hu₁.1.le.trans hw.1, hw.2.trans hu₂.2.le⟩
    by_cases hv1 : v ≤ u₁
    · rcases eq_or_lt_of_le hv1 with rfl | hv1_lt
      · rcases eq_or_lt_of_le h12 with rfl | h12_lt
        · simp
        · simp only [not_le.mpr h12_lt, ite_false, le_refl, ite_true, hKdiag v hv, zero_smul,
            sub_zero, norm_zero]
          positivity
      · simp only [not_le.mpr hv1_lt, not_le.mpr (hv1_lt.trans_le h12), ite_false, sub_self,
          norm_zero]
        positivity
    · have hu₁v : u₁ < v := not_le.mp hv1
      by_cases h2v : u₂ ≤ v
      · simpa [hu₁v.le, h2v] using
          norm_image_sub_kernel_smul_le hK hK₁ hIcc hM₁0 hK₁_bound hv hsub12 h12 h2v y hBv
      · have hvu₂ : v < u₂ := not_le.mp h2v
        have hvIcc : Icc u₁ v ⊆ Icc c₁ c₂ := fun w hw =>
          ⟨hu₁.1.le.trans hw.1, hw.2.trans (hvu₂.le.trans hu₂.2.le)⟩
        have hstep :=
          norm_image_sub_kernel_smul_le hK hK₁ hIcc hM₁0 hK₁_bound hv hvIcc hu₁v.le le_rfl y hBv
        rw [hKdiag v hv, zero_smul, zero_sub, norm_neg] at hstep
        simp only [not_le.mpr hvu₂, ite_false, hu₁v.le, ite_true, zero_sub, norm_neg]
        exact hstep.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hvu₂.le u₁) hB0)
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro u₁ hu₁ u₂ hu₂
  rw [Real.coe_nnabs, abs_of_nonneg hB0]
  rcases le_total u₁ u₂ with h12 | h21
  · rw [dist_eq_norm, dist_comm u₁ u₂, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h12),
      norm_sub_rev]
    exact hpair hu₁ hu₂ h12
  · rw [dist_eq_norm, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h21)]
    exact hpair hu₂ hu₁ h21

omit [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  [IsScalarTower ℝ 𝕜 E] in
private lemma cutoff_ae_eq_indicator (s : Set ℝ) (u : ℝ) (f : ℝ → E) :
    (fun v => if u ≤ v then f v else 0) =ᵐ[volume.restrict s] (Ioi u).indicator f := by
  have hne : ∀ᵐ v ∂(volume.restrict s), v ≠ u := by
    simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using
      measure_singleton (μ := volume.restrict s) u
  filter_upwards [hne] with v hvne
  by_cases huv : u < v
  · simp [huv.le, huv]
  · have hvu : ¬ u ≤ v := fun h => hvne (le_antisymm (not_lt.mp huv) h)
    simp [huv, hvu]

private lemma hasDerivAt_integral_kernel_smul_Ioi_of_diag_zero_of_le (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hK₁ : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hP₁ : ContinuousOn P₁ I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK₁_le : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    {g : ℝ → E} (hg : AEStronglyMeasurable g (volume.restrict I))
    {B : ℝ → ℝ} (hB_le : ∀ v ∈ I, Q v * ‖g v‖ ≤ B v)
    (hB_int : ∀ x ∈ I, IntegrableOn B (I ∩ Ioi x))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    HasDerivAt (fun x => ∫ v in I ∩ Ioi x, K x v • g v)
      (∫ v in I ∩ Ioi x₀, K₁ x₀ v • g v) x₀ := by
  obtain ⟨c₁, c₂, hc₁, _, hc₁x₀, hx₀c₂, hIcc⟩ := exists_Icc_subset_of_isOpen hI hx₀
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP₁.mono hIcc)
  set M₁' : ℝ := max M₁ 0
  have hK₁_bd : ∀ u ∈ Icc c₁ c₂, ∀ v ∈ I, u < v → ‖K₁ u v‖ ≤ M₁' * Q v := fun u hu v hv huv =>
    (hK₁_le u (hIcc hu) v hv huv).trans <|
      mul_le_mul_of_nonneg_right ((le_abs_self _).trans
        ((Real.norm_eq_abs _ ▸ hM₁ u hu).trans (le_max_left _ _))) (hQ0 v hv)
  set ν : Measure ℝ := volume.restrict (I ∩ Ioi c₁)
  have hImeas : MeasurableSet (I ∩ Ioi c₁) := hI.measurableSet.inter measurableSet_Ioi
  set F : ℝ → ℝ → E := fun u v => if u ≤ v then K u v • g v else 0
  set F' : ℝ → E := (Ioi x₀).indicator fun v => K₁ x₀ v • g v
  have hF_eq : ∀ u ∈ Ioo c₁ c₂, ∫ v, F u v ∂ν = ∫ v in I ∩ Ioi u, K u v • g v := fun u hu =>
    (integral_congr_ae (cutoff_ae_eq_indicator _ u _)).trans
      (integral_indicator_Ioi_restrict hu.1 _)
  have hF_int_u : ∀ u ∈ Ioo c₁ c₂, Integrable (F u) ν := fun u hu => by
    have huI : u ∈ I := hIcc (Ioo_subset_Icc_self hu)
    exact (integrable_indicator_Ioi_restrict (integrableOn_kernel_smul_Ioi_of_le hI
      (hK.mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.le⟩) hQ0
      (fun w hw v hv hwv => hKle w hw v hv hwv.le) hg huI
      (fun v hv _ => hB_le v hv) (hB_int u huI))).congr
      (cutoff_ae_eq_indicator _ u _).symm
  have hF'_int : Integrable F' ν := integrable_indicator_Ioi_restrict
    (integrableOn_kernel_smul_Ioi_of_le hI hK₁_cont hQ0 hK₁_le hg hx₀
      (fun v hv _ => hB_le v hv) (hB_int x₀ hx₀))
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_lip (μ := ν)
    (F := F) (F' := F') (bound := fun v => M₁' * B v)
    (Ioo_mem_nhds hc₁x₀ hx₀c₂) ?_ (hF_int_u x₀ ⟨hc₁x₀, hx₀c₂⟩) hF'_int.aestronglyMeasurable
    ?_ ((hB_int c₁ hc₁).const_mul M₁') ?_).2
  · rw [integral_indicator_Ioi_restrict hc₁x₀] at hmain
    exact hmain.congr_of_eventuallyEq
      (Filter.eventually_of_mem (Ioo_mem_nhds hc₁x₀ hx₀c₂) fun u hu => (hF_eq u hu).symm)
  · filter_upwards [Ioo_mem_nhds hc₁x₀ hx₀c₂] with u hu using (hF_int_u u hu).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hImeas] with v hv
    exact lipschitzOnWith_cutoff_kernel_smul hK hKdiag hK₁ hIcc (le_max_right _ _) hK₁_bd hv.1
      (hQ0 v hv.1) (g v) (hB_le v hv.1)
  · have hne : ∀ᵐ v ∂ν, v ≠ x₀ := by
      simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using measure_singleton (μ := ν) x₀
    filter_upwards [ae_restrict_mem hImeas, hne] with v hv hvne
    rcases lt_or_gt_of_ne hvne with hvx₀ | hx₀v
    · rw [show F' v = 0 from indicator_of_notMem (not_lt.mpr hvx₀.le) _]
      refine (hasDerivAt_const x₀ (0 : E)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hvx₀] with u hu
      simp [F, not_le.mpr (mem_Ioi.mp hu)]
    · rw [show F' v = K₁ x₀ v • g v from indicator_of_mem hx₀v _]
      refine ((hK₁ x₀ hx₀ v hv.1 hx₀v).smul_const (g v)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hx₀v] with u hu
      simp [F, (mem_Iio.mp hu).le]

/-- **Differentiation of upper-tail kernel integrals with vanishing diagonal.** If `K x x = 0` on
`I` and `K · v` has derivative `K₁ x v` for `x < v` bounded by `P₁ x * Q v` with continuous `P₁`,
then `x ↦ ∫ v in I ∩ Ioi x, K x v • g v` has derivative
`∫ v in I ∩ Ioi x₀, K₁ x₀ v • g v` at every `x₀ ∈ I`. -/
theorem hasDerivAt_integral_kernel_smul_Ioi_of_diag_zero (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hK₁ : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hP₁ : ContinuousOn P₁ I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK₁_le : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    {g : ℝ → E} (hg : AEStronglyMeasurable g (volume.restrict I))
    (hg_int : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖g v‖) (I ∩ Ioi x))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    HasDerivAt (fun x => ∫ v in I ∩ Ioi x, K x v • g v)
      (∫ v in I ∩ Ioi x₀, K₁ x₀ v • g v) x₀ :=
  hasDerivAt_integral_kernel_smul_Ioi_of_diag_zero_of_le hI hK hKdiag hK₁ hK₁_cont hP₁ hQ0 hKle
    hK₁_le hg (fun _ _ => le_rfl) hg_int hx₀

omit [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [IsScalarTower ℝ 𝕜 E] in
/-- Fundamental theorem of calculus for `x ↦ ∫ v in Ioo c₁ c₂ ∩ Ioi x, f v`. -/
private lemma hasDerivAt_integral_Ioo_inter_Ioi [CompleteSpace E] {c₁ c₂ x₀ : ℝ}
    (hc₁x₀ : c₁ < x₀) (hx₀c₂ : x₀ < c₂) {f : ℝ → E} (hf : ContinuousOn f (Icc c₁ c₂)) :
    HasDerivAt (fun x => ∫ v in Ioo c₁ c₂ ∩ Ioi x, f v) (-f x₀) x₀ := by
  have hf_int : IntegrableOn f (Icc c₁ c₂) := hf.integrableOn_compact isCompact_Icc
  have hftc : HasDerivAt (fun x => -(∫ v in x₀..x, f v)) (-f x₀) x₀ :=
    (intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
        hf_int.aestronglyMeasurable (Icc_mem_nhds hc₁x₀ hx₀c₂))
      (hf.continuousAt (Icc_mem_nhds hc₁x₀ hx₀c₂))).neg
  have heq : (fun x => (∫ v in x₀..c₂, f v) + -(∫ v in x₀..x, f v)) =ᶠ[𝓝 x₀]
      (fun x => ∫ v in Ioo c₁ c₂ ∩ Ioi x, f v) := by
    filter_upwards [Ioo_mem_nhds hc₁x₀ hx₀c₂] with x hx
    have h1 : IntervalIntegrable f volume x₀ x :=
      (hf.mono (uIcc_subset_Icc ⟨hc₁x₀.le, hx₀c₂.le⟩ (Ioo_subset_Icc_self hx))).intervalIntegrable
    have h2 : IntervalIntegrable f volume x c₂ :=
      (hf.mono (uIcc_subset_Icc (Ioo_subset_Icc_self hx)
        ⟨hc₁x₀.le.trans hx₀c₂.le, le_rfl⟩)).intervalIntegrable
    rw [← sub_eq_add_neg, ← intervalIntegral.integral_add_adjacent_intervals h1 h2,
      add_sub_cancel_left, intervalIntegral.integral_of_le hx.2.le,
      Ioo_inter_Ioi, max_eq_right hx.1.le, setIntegral_congr_set Ioo_ae_eq_Ioc]
  exact (hftc.const_add (∫ v in x₀..c₂, f v)).congr_of_eventuallyEq heq.symm

omit [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [IsScalarTower ℝ 𝕜 E] in
/-- Splitting `∫ v in I ∩ Ioi x, f v` at `c₂` for `x ∈ Ioo c₁ c₂` with `Icc c₁ c₂ ⊆ I`. -/
private lemma integral_Ioo_inter_Ioi_add_tail (hI : IsOpen I) {c₁ c₂ x : ℝ}
    (hIcc : Icc c₁ c₂ ⊆ I) (hx : x ∈ Ioo c₁ c₂) {f : ℝ → E}
    (hf : IntegrableOn f (I ∩ Ioi x)) :
    (∫ v in Ioo c₁ c₂ ∩ Ioi x, f v) + (∫ v in I ∩ Ioi c₂, f v) = ∫ v in I ∩ Ioi x, f v := by
  have hdisj : Disjoint (Ioc x c₂) (I ∩ Ioi c₂) :=
    disjoint_left.mpr fun v hv₁ hv₂ => hv₂.2.not_ge hv₁.2
  have hunion : Ioc x c₂ ∪ (I ∩ Ioi c₂) = I ∩ Ioi x := by
    ext v
    simp only [mem_union, mem_Ioc, mem_inter_iff, mem_Ioi]
    refine ⟨?_, fun ⟨hvI, hxv⟩ => (le_or_gt v c₂).imp (⟨hxv, ·⟩) (⟨hvI, ·⟩)⟩
    rintro (⟨hxv, hvc₂⟩ | ⟨hvI, hc₂v⟩)
    · exact ⟨hIcc ⟨hx.1.le.trans hxv.le, hvc₂⟩, hxv⟩
    · exact ⟨hvI, hx.2.trans hc₂v⟩
  rw [Ioo_inter_Ioi, max_eq_right hx.1.le, setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← setIntegral_union hdisj (hI.measurableSet.inter measurableSet_Ioi)
      (hf.mono_set (hunion ▸ subset_union_left)) (hf.mono_set (hunion ▸ subset_union_right)),
    hunion]

/-- Differentiation under the integral sign on a fixed strict tail `I ∩ Ioi c₂`. -/
private lemma hasDerivAt_integral_kernel_smul_Ioi_tail (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hK₁ : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hP₁ : ContinuousOn P₁ I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK₁_le : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    {g : ℝ → E} (hg : AEStronglyMeasurable g (volume.restrict I))
    (hg_int : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖g v‖) (I ∩ Ioi x))
    {c₁ c₂ x₀ : ℝ} (hc₂ : c₂ ∈ I) (hc₁x₀ : c₁ < x₀) (hx₀c₂ : x₀ < c₂)
    (hIcc : Icc c₁ c₂ ⊆ I) :
    HasDerivAt (fun x => ∫ v in I ∩ Ioi c₂, K x v • g v)
      (∫ v in I ∩ Ioi c₂, K₁ x₀ v • g v) x₀ := by
  have hx₀ : x₀ ∈ I := hIcc ⟨hc₁x₀.le, hx₀c₂.le⟩
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP₁.mono hIcc)
  set M₁' : ℝ := max M₁ 0
  have hI₂meas : MeasurableSet (I ∩ Ioi c₂) := hI.measurableSet.inter measurableSet_Ioi
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (I ∩ Ioi c₂))
    (F := fun x v => K x v • g v) (F' := fun x v => K₁ x v • g v)
    (bound := fun v => M₁' * (Q v * ‖g v‖))
    (Ioo_mem_nhds hc₁x₀ hx₀c₂) ?_ ?_ ?_ ?_ ((hg_int c₂ hc₂).const_mul M₁') ?_).2
  · filter_upwards [Ioo_mem_nhds hc₁x₀ hx₀c₂] with x hx
    have hxI : x ∈ I := hIcc (Ioo_subset_Icc_self hx)
    exact ((integrableOn_kernel_smul_Ioi hI (hK.mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.le⟩)
      (fun u hu v hv huv => hKle u hu v hv huv.le) hg hxI (hg_int x hxI)).mono_set
      (inter_subset_inter_right _ (Ioi_subset_Ioi hx.2.le))).aestronglyMeasurable
  · exact (integrableOn_kernel_smul_Ioi hI (hK.mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.le⟩)
      (fun u hu v hv huv => hKle u hu v hv huv.le) hg hx₀ (hg_int x₀ hx₀)).mono_set
      (inter_subset_inter_right _ (Ioi_subset_Ioi hx₀c₂.le))
  · exact ((integrableOn_kernel_smul_Ioi hI hK₁_cont hK₁_le hg hx₀ (hg_int x₀ hx₀)).mono_set
      (inter_subset_inter_right _ (Ioi_subset_Ioi hx₀c₂.le))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hI₂meas] with v hv x hx
    have hxIcc := Ioo_subset_Icc_self hx
    have hM₁x : P₁ x ≤ M₁' := (le_abs_self _).trans
      ((Real.norm_eq_abs _ ▸ hM₁ x hxIcc).trans (le_max_left _ _))
    have hK₁v : ‖K₁ x v • g v‖ ≤ P₁ x * (Q v * ‖g v‖) := by
      rw [← mul_assoc]
      exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right
        (hK₁_le x (hIcc hxIcc) v hv.1 (hx.2.trans hv.2)) (norm_nonneg _))
    exact hK₁v.trans (mul_le_mul_of_nonneg_right hM₁x (mul_nonneg (hQ0 v hv.1) (norm_nonneg _)))
  · filter_upwards [ae_restrict_mem hI₂meas] with v hv x hx
    exact (hK₁ x (hIcc (Ioo_subset_Icc_self hx)) v hv.1 (hx.2.trans hv.2)).smul_const (g v)

/-- Zero-diagonal component `K x v - K v v` on a compactly contained open subinterval
`Ioo c₁ c₂`. -/
private lemma hasDerivAt_integral_sub_diag_Ioo
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hK₁ : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hP : ContinuousOn P I) (hP₁ : ContinuousOn P₁ I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK₁_le : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    {g : ℝ → E} (hg : ContinuousOn g I)
    (hg_int : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖g v‖) (I ∩ Ioi x))
    {c₁ c₂ x₀ : ℝ} (hc₁x₀ : c₁ < x₀) (hx₀c₂ : x₀ < c₂) (hIcc : Icc c₁ c₂ ⊆ I) :
    HasDerivAt (fun x => ∫ v in Ioo c₁ c₂ ∩ Ioi x, (K x v - K v v) • g v)
      (∫ v in Ioo c₁ c₂ ∩ Ioi x₀, K₁ x₀ v • g v) x₀ := by
  have hJ₀_sub : Ioo c₁ c₂ ⊆ I := Ioo_subset_Icc_self.trans hIcc
  obtain ⟨MP, hMP⟩ := isCompact_Icc.exists_bound_of_continuousOn (hP.mono hIcc)
  set MP' : ℝ := max MP 0
  have hPx_le : ∀ u ∈ Icc c₁ c₂, P u ≤ MP' := fun u hu =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hMP u hu).trans (le_max_left _ _))
  have hKdiag_cont : ContinuousOn (fun v => K v v) I :=
    hK.comp (continuous_id.prodMk continuous_id).continuousOn fun v hv => ⟨hv, hv, le_rfl⟩
  have hK₀_cont : ContinuousOn (Function.uncurry fun x v => K x v - K v v)
      {p : ℝ × ℝ | p.1 ∈ Ioo c₁ c₂ ∧ p.2 ∈ Ioo c₁ c₂ ∧ p.1 ≤ p.2} :=
    ContinuousOn.sub (hK.mono fun p hp => ⟨hJ₀_sub hp.1, hJ₀_sub hp.2.1, hp.2.2⟩)
      (hKdiag_cont.comp continuous_snd.continuousOn fun p hp => hJ₀_sub hp.2.1)
  refine hasDerivAt_integral_kernel_smul_Ioi_of_diag_zero isOpen_Ioo hK₀_cont
    (fun x _ => sub_self _)
    (fun x hx v hv hxv => (hK₁ x (hJ₀_sub hx) v (hJ₀_sub hv) hxv).sub_const _)
    (hK₁_cont.mono fun p hp => ⟨hJ₀_sub hp.1, hJ₀_sub hp.2.1, hp.2.2⟩)
    (hP₁.mono hJ₀_sub) (fun v hv => hQ0 v (hJ₀_sub hv))
    (P := fun _ => 2 * MP') (fun x hx v hv hxv => ?_)
    (fun x hx v hv hxv => hK₁_le x (hJ₀_sub hx) v (hJ₀_sub hv) hxv)
    ((hg.mono hJ₀_sub).aestronglyMeasurable isOpen_Ioo.measurableSet)
    (fun x hx => (hg_int x (hJ₀_sub hx)).mono_set (inter_subset_inter_left _ hJ₀_sub))
    ⟨hc₁x₀, hx₀c₂⟩
  calc ‖K x v - K v v‖ ≤ ‖K x v‖ + ‖K v v‖ := norm_sub_le _ _
    _ ≤ P x * Q v + P v * Q v := add_le_add (hKle x (hJ₀_sub hx) v (hJ₀_sub hv) hxv)
        (hKle v (hJ₀_sub hv) v (hJ₀_sub hv) le_rfl)
    _ ≤ MP' * Q v + MP' * Q v := add_le_add
        (mul_le_mul_of_nonneg_right (hPx_le x (Ioo_subset_Icc_self hx)) (hQ0 v (hJ₀_sub hv)))
        (mul_le_mul_of_nonneg_right (hPx_le v (Ioo_subset_Icc_self hv)) (hQ0 v (hJ₀_sub hv)))
    _ = 2 * MP' * Q v := by ring

/-- **General Leibniz rule for upper-tail kernel integrals.** Without requiring `K x x = 0`, if `g`
is continuous on `I` and `P` is continuous on `I`, differentiating
`x ↦ ∫ v in I ∩ Ioi x, K x v • g v` at `x₀ ∈ I` yields the boundary term `-(K x₀ x₀ • g x₀)` plus
the integral of `K₁ x₀ v • g v`. -/
theorem hasDerivAt_integral_kernel_smul_Ioi [CompleteSpace E] (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hK₁ : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hP : ContinuousOn P I) (hP₁ : ContinuousOn P₁ I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK₁_le : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    {g : ℝ → E} (hg : ContinuousOn g I)
    (hg_int : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖g v‖) (I ∩ Ioi x))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    HasDerivAt (fun x => ∫ v in I ∩ Ioi x, K x v • g v)
      (-(K x₀ x₀ • g x₀) + ∫ v in I ∩ Ioi x₀, K₁ x₀ v • g v) x₀ := by
  obtain ⟨c₁, c₂, _, hc₂, hc₁x₀, hx₀c₂, hIcc⟩ := exists_Icc_subset_of_isOpen hI hx₀
  set J₀ : Set ℝ := Ioo c₁ c₂
  have hJ₀_sub : J₀ ⊆ I := Ioo_subset_Icc_self.trans hIcc
  have hdiag_cont : ContinuousOn (fun v => K v v • g v) (Icc c₁ c₂) :=
    ((hK.comp (continuous_id.prodMk continuous_id).continuousOn fun v hv =>
      ⟨hv, hv, le_rfl⟩).mono hIcc).smul (hg.mono hIcc)
  have hd_zero := hasDerivAt_integral_sub_diag_Ioo hK hK₁ hK₁_cont hP hP₁ hQ0 hKle hK₁_le hg
    hg_int hc₁x₀ hx₀c₂ hIcc
  have hd_diag := hasDerivAt_integral_Ioo_inter_Ioi hc₁x₀ hx₀c₂ hdiag_cont
  have hd_tail := hasDerivAt_integral_kernel_smul_Ioi_tail hI hK hK₁ hK₁_cont hP₁ hQ0 hKle hK₁_le
    (hg.aestronglyMeasurable hI.measurableSet) hg_int hc₂ hc₁x₀ hx₀c₂ hIcc
  have hsplit_eq : ∀ x ∈ Ioo c₁ c₂,
      (∫ v in J₀ ∩ Ioi x, (K x v - K v v) • g v) + (∫ v in J₀ ∩ Ioi x, K v v • g v) +
        (∫ v in I ∩ Ioi c₂, K x v • g v) = ∫ v in I ∩ Ioi x, K x v • g v := by
    intro x hx
    have hxI : x ∈ I := hIcc (Ioo_subset_Icc_self hx)
    have hintK : IntegrableOn (fun v => K x v • g v) (I ∩ Ioi x) :=
      integrableOn_kernel_smul_Ioi hI (hK.mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.le⟩)
        (fun u hu v hv huv => hKle u hu v hv huv.le)
        (hg.aestronglyMeasurable hI.measurableSet) hxI (hg_int x hxI)
    have hint_diag : IntegrableOn (fun v => K v v • g v) (J₀ ∩ Ioi x) :=
      (hdiag_cont.integrableOn_compact isCompact_Icc).mono_set
        (inter_subset_left.trans Ioo_subset_Icc_self)
    have hint_K₀ : IntegrableOn (fun v => (K x v - K v v) • g v) (J₀ ∩ Ioi x) :=
      ((hintK.mono_set (inter_subset_inter_left _ hJ₀_sub)).sub hint_diag).congr_fun
        (fun v _ => (sub_smul (K x v) (K v v) (g v)).symm)
        (isOpen_Ioo.measurableSet.inter measurableSet_Ioi)
    rw [← integral_add hint_K₀ hint_diag]
    simp_rw [sub_smul, sub_add_cancel]
    exact integral_Ioo_inter_Ioi_add_tail hI hIcc hx hintK
  have hjoin := integral_Ioo_inter_Ioi_add_tail hI hIcc ⟨hc₁x₀, hx₀c₂⟩
    (integrableOn_kernel_smul_Ioi hI hK₁_cont hK₁_le
      (hg.aestronglyMeasurable hI.measurableSet) hx₀ (hg_int x₀ hx₀))
  have hderiv_sum : (∫ v in J₀ ∩ Ioi x₀, K₁ x₀ v • g v) + -(K x₀ x₀ • g x₀) +
      (∫ v in I ∩ Ioi c₂, K₁ x₀ v • g v) =
        -(K x₀ x₀ • g x₀) + ∫ v in I ∩ Ioi x₀, K₁ x₀ v • g v := by
    rw [← hjoin]; abel
  rw [← hderiv_sum]
  exact ((hd_zero.add hd_diag).add hd_tail).congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds hc₁x₀ hx₀c₂) fun x hx => (hsplit_eq x hx).symm)

end KernelDeriv

/-! ### Differentiability, derivative bounds, and `C¹` regularity of Volterra solutions -/

section SolutionDeriv

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  {I : Set ℝ} {K K₁ : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P P₁ Q : ℝ → ℝ}

omit [NormedAlgebra ℝ 𝕜] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- Local integrable majorant for `Q v * ‖J v + ψ v • h v‖` on a strict right subinterval
`I ∩ Ioi c₁` when `h =O[𝓟 (I ∩ Ici c₁)] P`. -/
private lemma exists_volterra_rhs_bound_on_Ioi (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} {c₁ : ℝ} (hhO : h =O[𝓟 (I ∩ Ici c₁)] P) :
    ∃ B : ℝ → ℝ,
      (∀ v ∈ I ∩ Ioi c₁, Q v * ‖J v + ψ v • h v‖ ≤ B v) ∧
      (∀ x ∈ I ∩ Ioi c₁, IntegrableOn B ((I ∩ Ioi c₁) ∩ Ioi x)) := by
  obtain ⟨c, hc⟩ := hhO.bound
  rw [eventually_principal] at hc
  set C : ℝ := max c 0
  refine ⟨fun v => Q v * ‖J v‖ + C * (P v * Q v * ‖ψ v‖), fun v hv => ?_, fun x hx => ?_⟩
  · have hhv : ‖h v‖ ≤ C * P v :=
      (hc v ⟨hv.1, hv.2.le⟩).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
        |>.trans_eq (by rw [Real.norm_of_nonneg (hP0 v hv.1)])
    calc Q v * ‖J v + ψ v • h v‖
        ≤ Q v * (‖J v‖ + ‖ψ v‖ * ‖h v‖) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
            (add_le_add_right (norm_smul_le _ _) _)) (hQ0 v hv.1)
      _ ≤ Q v * (‖J v‖ + ‖ψ v‖ * (C * P v)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add_right (mul_le_mul_of_nonneg_left hhv (norm_nonneg _)) _) (hQ0 v hv.1)
      _ = Q v * ‖J v‖ + C * (P v * Q v * ‖ψ v‖) := by ring
  · rw [inter_Ioi_inter_Ioi_of_lt hx.2]
    exact (hΦ x hx.1).add ((hΨ x hx.1).const_mul C)

/-- **Differentiability of Volterra solutions with vanishing diagonal (Olver, Theorem 10.1).**
When `K x x = 0` on `I` and `K · v` has derivative `K₁ x v` bounded by `P₁ x * Q v` with continuous
`P₁`, every measurable `O(P)` solution `h` of the Volterra equation on `I` has derivative
`∫ v in I ∩ Ioi x₀, K₁ x₀ v • (J v + ψ v • h v)` at every `x₀ ∈ I`. -/
theorem hasDerivAt_volterra_solution_on (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hK₁ : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hP₁ : ContinuousOn P₁ I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK₁_le : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict I))
    (hh_eq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hhO : ∀ x ∈ I, h =O[𝓟 (I ∩ Ici x)] P)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    HasDerivAt h (∫ v in I ∩ Ioi x₀, K₁ x₀ v • (J v + ψ v • h v)) x₀ := by
  obtain ⟨c₁, _, hc₁, _, hc₁x₀, _, _⟩ := exists_Icc_subset_of_isOpen hI hx₀
  set I₁ : Set ℝ := I ∩ Ioi c₁
  have hI₁ : IsOpen I₁ := hI.inter isOpen_Ioi
  obtain ⟨B, hB_le, hB_int⟩ := exists_volterra_rhs_bound_on_Ioi hP0 hQ0 hΦ hΨ (hhO c₁ hc₁)
  have hd := hasDerivAt_integral_kernel_smul_Ioi_of_diag_zero_of_le
    (g := fun v => J v + ψ v • h v) hI₁
    (hK.mono fun p hp => ⟨hp.1.1, hp.2.1.1, hp.2.2⟩) (fun x hx => hKdiag x hx.1)
    (fun x hx v hv hxv => hK₁ x hx.1 v hv.1 hxv)
    (hK₁_cont.mono fun p hp => ⟨hp.1.1, hp.2.1.1, hp.2.2⟩)
    (hP₁.mono inter_subset_left) (fun v hv => hQ0 v hv.1)
    (fun x hx v hv hxv => hKle x hx.1 v hv.1 hxv)
    (fun x hx v hv hxv => hK₁_le x hx.1 v hv.1 hxv)
    ((hJ.add (hψ.smul hh)).mono_set inter_subset_left) hB_le hB_int ⟨hx₀, hc₁x₀⟩
  rw [inter_Ioi_inter_Ioi_of_lt hc₁x₀] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hI₁.mem_nhds ⟨hx₀, hc₁x₀⟩] with x hx
  dsimp only [I₁]
  rw [hh_eq x hx.1, inter_Ioi_inter_Ioi_of_lt hx.2]

/-- **Derivative error bound for Volterra solutions (Olver, Theorem 10.1).** Under the hypotheses
of `hasDerivAt_volterra_solution_on`, the derivative of any measurable `O(P)` solution satisfies
`‖deriv h x₀‖ ≤ P₁ x₀ * Φ x₀ * exp (Ψ x₀)` for every `x₀ ∈ I`. -/
theorem norm_deriv_volterra_solution_le_on (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hK₁ : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hP₁ : ContinuousOn P₁ I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK₁_le : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict I))
    (hh_eq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hhO : ∀ x ∈ I, h =O[𝓟 (I ∩ Ici x)] P)
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    ‖deriv h x₀‖ ≤
      P₁ x₀ * (∫ v in I ∩ Ioi x₀, Q v * ‖J v‖) *
        Real.exp (∫ v in I ∩ Ioi x₀, P v * Q v * ‖ψ v‖) := by
  set Φ₀ : ℝ := ∫ v in I ∩ Ioi x₀, Q v * ‖J v‖
  set w : ℝ → ℝ := fun v => P v * Q v * ‖ψ v‖
  set Ψ : ℝ → ℝ := fun x => ∫ v in I ∩ Ioi x, w v
  have hd := hasDerivAt_volterra_solution_on hI hK hKdiag hK₁ hK₁_cont hJ hψ hP0 hP₁ hQ0 hKle
    hK₁_le hΦ hΨ hh hh_eq hhO hx₀
  rw [hd.deriv]
  have hint_K₁ : IntegrableOn (fun v => K₁ x₀ v • (J v + ψ v • h v)) (I ∩ Ioi x₀) := by
    obtain ⟨c₁, _, hc₁, _, hc₁x₀, _, _⟩ := exists_Icc_subset_of_isOpen hI hx₀
    obtain ⟨B₁, hB₁_le, hB₁_int⟩ := exists_volterra_rhs_bound_on_Ioi hP0 hQ0 hΦ hΨ (hhO c₁ hc₁)
    have hB₁_x₀ := hB₁_int x₀ ⟨hx₀, hc₁x₀⟩
    rw [inter_Ioi_inter_Ioi_of_lt hc₁x₀] at hB₁_x₀
    exact integrableOn_kernel_smul_Ioi_of_le hI hK₁_cont hQ0 hK₁_le (hJ.add (hψ.smul hh)) hx₀
      (fun v hv hxv => hB₁_le v ⟨hv, hc₁x₀.trans hxv⟩) hB₁_x₀
  have hexp_int : IntegrableOn (fun v => w v * Real.exp (Ψ v)) (I ∩ Ioi x₀) := by
    simpa only [one_mul, Ψ] using integrableOn_mul_exp_tail_on (hΨ x₀ hx₀) 1
  set M : ℝ → ℝ := fun v => P₁ x₀ * (Q v * ‖J v‖) + P₁ x₀ * Φ₀ * (w v * Real.exp (Ψ v))
  have hM_int : IntegrableOn M (I ∩ Ioi x₀) :=
    ((hΦ x₀ hx₀).const_mul (P₁ x₀)).add (hexp_int.const_mul (P₁ x₀ * Φ₀))
  have hpt : ∀ᵐ v ∂(volume.restrict (I ∩ Ioi x₀)), ‖K₁ x₀ v • (J v + ψ v • h v)‖ ≤ M v := by
    filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
    have hPQ0 : 0 ≤ P₁ x₀ * Q v := (norm_nonneg _).trans (hK₁_le x₀ hx₀ v hv.1 hv.2)
    have hh_v : ‖h v‖ ≤ P v * Φ₀ * Real.exp (Ψ v) := by
      refine (norm_volterra_solution_le_on hI (hK.mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.le⟩)
        hJ hψ hP0 hQ0 (fun u hu t ht hut => hKle u hu t ht hut.le) hΦ hΨ hh hh_eq hhO hv.1).trans ?_
      have hΦ_le : ∫ u in I ∩ Ioi v, Q u * ‖J u‖ ≤ Φ₀ := by
        refine setIntegral_mono_set (hΦ x₀ hx₀) ?_
          (ae_of_all _ (inter_subset_inter_right _ (Ioi_subset_Ioi hv.2.le)))
        filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with u hu
        exact mul_nonneg (hQ0 u hu.1) (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hΦ_le (hP0 v hv.1)) (Real.exp_nonneg _)
    calc ‖K₁ x₀ v • (J v + ψ v • h v)‖
        ≤ P₁ x₀ * Q v * ‖J v + ψ v • h v‖ :=
          (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right (hK₁_le x₀ hx₀ v hv.1 hv.2)
            (norm_nonneg _))
      _ ≤ P₁ x₀ * Q v * (‖J v‖ + ‖ψ v‖ * (P v * Φ₀ * Real.exp (Ψ v))) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
            (add_le_add le_rfl ((norm_smul_le _ _).trans
              (mul_le_mul_of_nonneg_left hh_v (norm_nonneg _))))) hPQ0
      _ = M v := by simp only [M, w]; ring
  have hexp_id := mul_integral_mul_exp_tail_on (hΨ x₀ hx₀) 1
  simp only [one_mul] at hexp_id
  calc ‖∫ v in I ∩ Ioi x₀, K₁ x₀ v • (J v + ψ v • h v)‖
      ≤ ∫ v in I ∩ Ioi x₀, M v :=
        (norm_integral_le_integral_norm _).trans (integral_mono_ae hint_K₁.norm hM_int hpt)
    _ = P₁ x₀ * Φ₀ + P₁ x₀ * Φ₀ * (Real.exp (Ψ x₀) - 1) := by
        simp only [M]
        rw [integral_add ((hΦ x₀ hx₀).const_mul _) (hexp_int.const_mul _),
          integral_const_mul, integral_const_mul, hexp_id]
    _ = P₁ x₀ * Φ₀ * Real.exp (Ψ x₀) := by ring

/-- **`C¹` regularity of Volterra solutions with vanishing diagonal.** Under the exact hypotheses
of `hasDerivAt_volterra_solution_on` — without assuming `K₁` extends continuously to the diagonal —
every measurable `O(P)` solution `h` of the Volterra equation on `I` is `C¹` on `I`. -/
theorem contDiffOn_volterra_solution_on (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hK₁ : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hP₁ : ContinuousOn P₁ I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK₁_le : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict I))
    (hh_eq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hhO : ∀ x ∈ I, h =O[𝓟 (I ∩ Ici x)] P) :
    ContDiffOn ℝ 1 h I := by
  have hd : ∀ x ∈ I, HasDerivAt h (∫ v in I ∩ Ioi x, K₁ x v • (J v + ψ v • h v)) x :=
    fun _ hx => hasDerivAt_volterra_solution_on hI hK hKdiag hK₁ hK₁_cont hJ hψ hP0 hP₁ hQ0 hKle
      hK₁_le hΦ hΨ hh hh_eq hhO hx
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hI]
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  intro x₀ hx₀
  obtain ⟨c₁, _, hc₁, _, hc₁x₀, _, _⟩ := exists_Icc_subset_of_isOpen hI hx₀
  set I₁ : Set ℝ := I ∩ Ioi c₁
  have hI₁ : IsOpen I₁ := hI.inter isOpen_Ioi
  obtain ⟨B, hB_le, hB_int⟩ := exists_volterra_rhs_bound_on_Ioi hP0 hQ0 hΦ hΨ (hhO c₁ hc₁)
  have hcont_I₁ := continuousOn_integral_kernel_smul_Ioi_of_le (g := fun v => J v + ψ v • h v) hI₁
    (hK₁_cont.mono fun p hp => ⟨hp.1.1, hp.2.1.1, hp.2.2⟩)
    (hP₁.mono inter_subset_left) (fun v hv => hQ0 v hv.1)
    (fun x hx v hv hxv => hK₁_le x hx.1 v hv.1 hxv)
    ((hJ.add (hψ.smul hh)).mono_set inter_subset_left) hB_le hB_int
  have hcongr : EqOn (fun x => ∫ v in I₁ ∩ Ioi x, K₁ x v • (J v + ψ v • h v)) (deriv h) I₁ :=
    fun x hx => by dsimp only [I₁]; rw [inter_Ioi_inter_Ioi_of_lt hx.2, ← (hd x hx.1).deriv]
  exact ((hcont_I₁.congr hcongr.symm).continuousAt (hI₁.mem_nhds ⟨hx₀, hc₁x₀⟩)).continuousWithinAt

end SolutionDeriv


/-! ### Sharper derivative bounds when `P` is constant (Olver, Theorem 10.2) -/

section DerivBound

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  {I : Set ℝ} {K K₁ : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P₁ Q : ℝ → ℝ}

private lemma hasDerivAt_and_integrableOn_of_const_bound_on (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hK₁ : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    {P₀ M : ℝ} (hP₁ : ContinuousOn P₁ I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P₀ * Q v)
    (hK₁_le : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hJψ : ∀ v ∈ I, ‖J v‖ ≤ M * ‖ψ v‖)
    (hΦψ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict I))
    (hh_eq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hhO : ∀ x ∈ I, h =O[𝓟 (I ∩ Ici x)] (fun _ => (1 : ℝ)))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    HasDerivAt h (∫ v in I ∩ Ioi x₀, K₁ x₀ v • (J v + ψ v • h v)) x₀ ∧
      IntegrableOn (fun v => K₁ x₀ v • (J v + ψ v • h v)) (I ∩ Ioi x₀) := by
  obtain ⟨c₁, _, hc₁, _, hc₁x₀, _, _⟩ := exists_Icc_subset_of_isOpen hI hx₀
  obtain ⟨c, hc⟩ := (hhO c₁ hc₁).bound
  rw [eventually_principal] at hc
  have hB₁_le : ∀ v ∈ I ∩ Ioi c₁,
      Q v * ‖J v + ψ v • h v‖ ≤ (|M| + max c 0) * (Q v * ‖ψ v‖) := fun v hv => by
    have hhv : ‖h v‖ ≤ max c 0 := (by simpa using hc v ⟨hv.1, hv.2.le⟩ : ‖h v‖ ≤ c).trans
      (le_max_left _ _)
    calc Q v * ‖J v + ψ v • h v‖
        ≤ Q v * (|M| * ‖ψ v‖ + ‖ψ v‖ * max c 0) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add
            ((hJψ v hv.1).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg _)))
            ((norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left hhv (norm_nonneg _)))))
            (hQ0 v hv.1)
      _ = (|M| + max c 0) * (Q v * ‖ψ v‖) := by ring
  have hd_I₁ := hasDerivAt_integral_kernel_smul_Ioi_of_diag_zero_of_le
    (g := fun v => J v + ψ v • h v) (hI.inter isOpen_Ioi)
    (hK.mono fun p hp => ⟨hp.1.1, hp.2.1.1, hp.2.2⟩)
    (fun x hx => hKdiag x hx.1) (fun x hx v hv hxv => hK₁ x hx.1 v hv.1 hxv)
    (hK₁_cont.mono fun p hp => ⟨hp.1.1, hp.2.1.1, hp.2.2⟩)
    (hP₁.mono inter_subset_left) (fun v hv => hQ0 v hv.1)
    (P := fun _ => P₀) (fun x hx v hv hxv => hKle x hx.1 v hv.1 hxv)
    (fun x hx v hv hxv => hK₁_le x hx.1 v hv.1 hxv)
    ((hJ.add (hψ.smul hh)).mono_set inter_subset_left) hB₁_le
    (fun x hx => by
      rw [inter_Ioi_inter_Ioi_of_lt hx.2]
      exact (hΦψ x hx.1).const_mul _) ⟨hx₀, hc₁x₀⟩
  rw [inter_Ioi_inter_Ioi_of_lt hc₁x₀] at hd_I₁
  refine ⟨hd_I₁.congr_of_eventuallyEq (Filter.eventually_of_mem
    ((hI.inter isOpen_Ioi).mem_nhds ⟨hx₀, hc₁x₀⟩)
    fun x hx => by dsimp only; rw [hh_eq x hx.1, inter_Ioi_inter_Ioi_of_lt hx.2]), ?_⟩
  exact integrableOn_kernel_smul_Ioi_of_le hI hK₁_cont hQ0 hK₁_le (hJ.add (hψ.smul hh))
    hx₀ (fun v hv hxv => hB₁_le v ⟨hv, hc₁x₀.trans hxv⟩) ((hΦψ x₀ hx₀).const_mul _)

/-- **Sharper derivative bound for constant `P = P₀` (Olver, Theorem 10.2).** Under `K x x = 0`,
`‖K x v‖ ≤ P₀ * Q v`, `‖K₁ x v‖ ≤ P₁ x * Q v`, and `‖J v‖ ≤ M * ‖ψ v‖`,
`P₀ * ‖deriv h x₀‖ ≤ P₁ x₀ * M * (exp (P₀ * Φ_ψ x₀) - 1)`. -/
theorem mul_norm_deriv_volterra_solution_le_mul_exp_sub_one_on (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hK₁ : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict I))
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    {P₀ M : ℝ} (hP₀ : 0 ≤ P₀) (hP₁ : ContinuousOn P₁ I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P₀ * Q v)
    (hK₁_le : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hJψ : ∀ v ∈ I, ‖J v‖ ≤ M * ‖ψ v‖)
    (hΦψ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict I))
    (hh_eq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v))
    (hhO : ∀ x ∈ I, h =O[𝓟 (I ∩ Ici x)] (fun _ => (1 : ℝ)))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    P₀ * ‖deriv h x₀‖ ≤
      P₁ x₀ * M * (Real.exp (P₀ * ∫ v in I ∩ Ioi x₀, Q v * ‖ψ v‖) - 1) := by
  set w : ℝ → ℝ := fun v => Q v * ‖ψ v‖
  set Φ : ℝ → ℝ := fun x => ∫ v in I ∩ Ioi x, w v
  obtain ⟨hd, hint_K₁⟩ := hasDerivAt_and_integrableOn_of_const_bound_on hI hK hKdiag hK₁ hK₁_cont
    hJ hψ hP₁ hQ0 hKle hK₁_le hJψ hΦψ hh hh_eq hhO hx₀
  rw [hd.deriv]
  have hpt : ∀ᵐ v ∂(volume.restrict (I ∩ Ioi x₀)),
      P₀ * ‖K₁ x₀ v • (J v + ψ v • h v)‖ ≤ P₁ x₀ * M * P₀ * (w v * Real.exp (P₀ * Φ v)) := by
    filter_upwards [ae_restrict_mem (hI.measurableSet.inter measurableSet_Ioi)] with v hv
    have hPQ0 : 0 ≤ P₁ x₀ * Q v := (norm_nonneg _).trans (hK₁_le x₀ hx₀ v hv.1 hv.2)
    have hh_v := norm_volterra_solution_le_mul_exp_sub_one_on hI
      (hK.mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.le⟩) hJ hψ hP₀ hQ0
      (fun u hu t ht hut => hKle u hu t ht hut.le) hJψ hΦψ hh hh_eq hhO hv.1
    have hrhs_v : ‖J v + ψ v • h v‖ ≤ M * ‖ψ v‖ * Real.exp (P₀ * Φ v) := by
      calc ‖J v + ψ v • h v‖ ≤ M * ‖ψ v‖ + ‖ψ v‖ * (M * (Real.exp (P₀ * Φ v) - 1)) :=
            (norm_add_le _ _).trans (add_le_add (hJψ v hv.1)
              ((norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left hh_v (norm_nonneg _))))
        _ = M * ‖ψ v‖ * Real.exp (P₀ * Φ v) := by ring
    calc P₀ * ‖K₁ x₀ v • (J v + ψ v • h v)‖
        ≤ P₀ * (P₁ x₀ * Q v * (M * ‖ψ v‖ * Real.exp (P₀ * Φ v))) :=
          mul_le_mul_of_nonneg_left (((norm_smul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hK₁_le x₀ hx₀ v hv.1 hv.2) (norm_nonneg _))).trans
              (mul_le_mul_of_nonneg_left hrhs_v hPQ0)) hP₀
      _ = P₁ x₀ * M * P₀ * (w v * Real.exp (P₀ * Φ v)) := by simp only [w]; ring
  calc P₀ * ‖∫ v in I ∩ Ioi x₀, K₁ x₀ v • (J v + ψ v • h v)‖
      ≤ ∫ v in I ∩ Ioi x₀, P₀ * ‖K₁ x₀ v • (J v + ψ v • h v)‖ := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hP₀
    _ ≤ ∫ v in I ∩ Ioi x₀, P₁ x₀ * M * P₀ * (w v * Real.exp (P₀ * Φ v)) :=
        integral_mono_ae (hint_K₁.norm.const_mul P₀)
          ((integrableOn_mul_exp_tail_on (hΦψ x₀ hx₀) P₀).const_mul _) hpt
    _ = P₁ x₀ * M * (P₀ * ∫ v in I ∩ Ioi x₀, w v * Real.exp (P₀ * Φ v)) := by
        rw [integral_const_mul, mul_assoc]
    _ = P₁ x₀ * M * (Real.exp (P₀ * Φ x₀) - 1) := by
        rw [mul_integral_mul_exp_tail_on (hΦψ x₀ hx₀) P₀]

/-- Scalar/algebra specialization (`J = ψ`, `M = 1`) of
`mul_norm_deriv_volterra_solution_le_mul_exp_sub_one_on`:
`P₀ * ‖deriv h x₀‖ ≤ P₁ x₀ * (exp (P₀ * Φ_ψ x₀) - 1)`. -/
theorem mul_norm_deriv_volterra_solution_le_exp_sub_one_on {𝕜 : Type*} [NormedRing 𝕜]
    [NormedAlgebra ℝ 𝕜] {I : Set ℝ} {K K₁ : ℝ → ℝ → 𝕜} {ψ : ℝ → 𝕜} {P₁ Q : ℝ → ℝ}
    (hI : IsOpen I)
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hK₁ : ∀ x ∈ I, ∀ v ∈ I, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 < p.2})
    (hψ : AEStronglyMeasurable ψ (volume.restrict I))
    {P₀ : ℝ} (hP₀ : 0 ≤ P₀) (hP₁ : ContinuousOn P₁ I) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖K x v‖ ≤ P₀ * Q v)
    (hK₁_le : ∀ x ∈ I, ∀ v ∈ I, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦψ : ∀ x ∈ I, IntegrableOn (fun v => Q v * ‖ψ v‖) (I ∩ Ioi x))
    {h : ℝ → 𝕜} (hh : AEStronglyMeasurable h (volume.restrict I))
    (hh_eq : ∀ x ∈ I, h x = ∫ v in I ∩ Ioi x, K x v * (ψ v + ψ v * h v))
    (hhO : ∀ x ∈ I, h =O[𝓟 (I ∩ Ici x)] (fun _ => (1 : ℝ)))
    {x₀ : ℝ} (hx₀ : x₀ ∈ I) :
    P₀ * ‖deriv h x₀‖ ≤ P₁ x₀ * (Real.exp (P₀ * ∫ v in I ∩ Ioi x₀, Q v * ‖ψ v‖) - 1) := by
  simpa only [mul_one, one_mul] using
    mul_norm_deriv_volterra_solution_le_mul_exp_sub_one_on (E := 𝕜) hI hK hKdiag hK₁ hK₁_cont hψ
      hψ hP₀ hP₁ hQ0 hKle hK₁_le (M := 1) (fun v _ => by rw [one_mul]) hΦψ hh hh_eq hhO hx₀

end DerivBound


/-! ### Specializations of derivative bounds and `C¹` regularity to rays `(a, ∞)` -/

section RayDeriv

private lemma Ioi_inter_Ioi_of_le {a x : ℝ} (hax : a ≤ x) : Ioi a ∩ Ioi x = Ioi x := by
  rw [Ioi_inter_Ioi, sup_eq_right.mpr hax]

private lemma Ioi_inter_Ici_of_lt {a x : ℝ} (hax : a < x) : Ioi a ∩ Ici x = Ici x :=
  inter_eq_right.mpr fun _ hv => hax.trans_le hv

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [IsScalarTower ℝ 𝕜 E]
  {a : ℝ} {K K₁ : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P P₁ Q : ℝ → ℝ}

/-- Differentiability of Volterra solutions with `K x x = 0` on `(a, ∞)`. -/
theorem hasDerivAt_volterra_solution
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x > a, K x x = 0)
    (hK₁ : ∀ x > a, ∀ v, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | a < p.1 ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict (Ioi a)))
    (hψ : AEStronglyMeasurable ψ (volume.restrict (Ioi a)))
    (hP0 : ∀ x > a, 0 ≤ P x) (hP₁ : ContinuousOn P₁ (Ioi a)) (hQ0 : ∀ v > a, 0 ≤ Q v)
    (hKle : ∀ x > a, ∀ v, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK₁_le : ∀ x > a, ∀ v, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x > a, IntegrableOn (fun v => Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x > a, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict (Ioi a)))
    (hh_eq : ∀ x > a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hhO : ∀ x > a, h =O[𝓟 (Ici x)] P) {x₀ : ℝ} (hx₀ : a < x₀) :
    HasDerivAt h (∫ v in Ioi x₀, K₁ x₀ v • (J v + ψ v • h v)) x₀ := by
  simpa only [Ioi_inter_Ioi_of_le hx₀.le] using
    hasDerivAt_volterra_solution_on isOpen_Ioi
      (hK.mono fun p hp => ⟨hp.1, hp.2.2⟩) hKdiag
      (fun x hx v _ hxv => hK₁ x hx v hxv)
      (hK₁_cont.mono fun p hp => ⟨hp.1, hp.2.2⟩) hJ hψ hP0 hP₁ hQ0
      (fun x hx v _ hxv => hKle x hx v hxv)
      (fun x hx v _ hxv => hK₁_le x hx v hxv)
      (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΦ x hx)
      (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΨ x hx) hh
      (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hh_eq x hx)
      (fun x hx => by rw [Ioi_inter_Ici_of_lt hx]; exact hhO x hx) hx₀

/-- Derivative error bound `‖deriv h x₀‖ ≤ P₁ x₀ * Φ x₀ * exp (Ψ x₀)` on `(a, ∞)`. -/
theorem norm_deriv_volterra_solution_le
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x > a, K x x = 0)
    (hK₁ : ∀ x > a, ∀ v, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | a < p.1 ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict (Ioi a)))
    (hψ : AEStronglyMeasurable ψ (volume.restrict (Ioi a)))
    (hP0 : ∀ x > a, 0 ≤ P x) (hP₁ : ContinuousOn P₁ (Ioi a)) (hQ0 : ∀ v > a, 0 ≤ Q v)
    (hKle : ∀ x > a, ∀ v, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK₁_le : ∀ x > a, ∀ v, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x > a, IntegrableOn (fun v => Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x > a, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict (Ioi a)))
    (hh_eq : ∀ x > a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hhO : ∀ x > a, h =O[𝓟 (Ici x)] P) {x₀ : ℝ} (hx₀ : a < x₀) :
    ‖deriv h x₀‖ ≤
      P₁ x₀ * (∫ v in Ioi x₀, Q v * ‖J v‖) *
        Real.exp (∫ v in Ioi x₀, P v * Q v * ‖ψ v‖) := by
  simpa only [Ioi_inter_Ioi_of_le hx₀.le] using
    norm_deriv_volterra_solution_le_on isOpen_Ioi
      (hK.mono fun p hp => ⟨hp.1, hp.2.2⟩) hKdiag
      (fun x hx v _ hxv => hK₁ x hx v hxv)
      (hK₁_cont.mono fun p hp => ⟨hp.1, hp.2.2⟩) hJ hψ hP0 hP₁ hQ0
      (fun x hx v _ hxv => hKle x hx v hxv)
      (fun x hx v _ hxv => hK₁_le x hx v hxv)
      (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΦ x hx)
      (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΨ x hx) hh
      (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hh_eq x hx)
      (fun x hx => by rw [Ioi_inter_Ici_of_lt hx]; exact hhO x hx) hx₀

/-- `C¹` regularity of Volterra solutions with `K x x = 0` on `(a, ∞)`. -/
theorem contDiffOn_volterra_solution
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x > a, K x x = 0)
    (hK₁ : ∀ x > a, ∀ v, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | a < p.1 ∧ p.1 < p.2})
    (hJ : AEStronglyMeasurable J (volume.restrict (Ioi a)))
    (hψ : AEStronglyMeasurable ψ (volume.restrict (Ioi a)))
    (hP0 : ∀ x > a, 0 ≤ P x) (hP₁ : ContinuousOn P₁ (Ioi a)) (hQ0 : ∀ v > a, 0 ≤ Q v)
    (hKle : ∀ x > a, ∀ v, x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hK₁_le : ∀ x > a, ∀ v, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x > a, IntegrableOn (fun v => Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x > a, IntegrableOn (fun v => P v * Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → E} (hh : AEStronglyMeasurable h (volume.restrict (Ioi a)))
    (hh_eq : ∀ x > a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (hhO : ∀ x > a, h =O[𝓟 (Ici x)] P) :
    ContDiffOn ℝ 1 h (Ioi a) :=
  contDiffOn_volterra_solution_on isOpen_Ioi
    (hK.mono fun p hp => ⟨hp.1, hp.2.2⟩) hKdiag
    (fun x hx v _ hxv => hK₁ x hx v hxv)
    (hK₁_cont.mono fun p hp => ⟨hp.1, hp.2.2⟩) hJ hψ hP0 hP₁ hQ0
    (fun x hx v _ hxv => hKle x hx v hxv)
    (fun x hx v _ hxv => hK₁_le x hx v hxv)
    (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΦ x hx)
    (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΨ x hx) hh
    (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hh_eq x hx)
    (fun x hx => by rw [Ioi_inter_Ici_of_lt hx]; exact hhO x hx)

/-- **Sharper derivative bound on `(a, ∞)` (Olver, Theorem 10.2):**
`P₀ * ‖deriv h x₀‖ ≤ P₁ x₀ * (exp (P₀ * Φ_ψ x₀) - 1)`. -/
theorem mul_norm_deriv_volterra_solution_le_exp_sub_one {𝕜 : Type*} [NormedRing 𝕜]
    [NormedAlgebra ℝ 𝕜] {a P₀ : ℝ} {K K₁ : ℝ → ℝ → 𝕜} {ψ : ℝ → 𝕜} {P₁ Q : ℝ → ℝ}
    (hK : ContinuousOn (Function.uncurry K) {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2})
    (hKdiag : ∀ x > a, K x x = 0)
    (hK₁ : ∀ x > a, ∀ v, x < v → HasDerivAt (fun u => K u v) (K₁ x v) x)
    (hK₁_cont : ContinuousOn (Function.uncurry K₁) {p : ℝ × ℝ | a < p.1 ∧ p.1 < p.2})
    (hψ : AEStronglyMeasurable ψ (volume.restrict (Ioi a)))
    (hP₀ : 0 ≤ P₀) (hP₁ : ContinuousOn P₁ (Ioi a)) (hQ0 : ∀ v > a, 0 ≤ Q v)
    (hKle : ∀ x > a, ∀ v, x ≤ v → ‖K x v‖ ≤ P₀ * Q v)
    (hK₁_le : ∀ x > a, ∀ v, x < v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    (hΦψ : ∀ x > a, IntegrableOn (fun v => Q v * ‖ψ v‖) (Ioi x))
    {h : ℝ → 𝕜} (hh : AEStronglyMeasurable h (volume.restrict (Ioi a)))
    (hh_eq : ∀ x > a, h x = ∫ v in Ioi x, K x v * (ψ v + ψ v * h v))
    (hhO : ∀ x > a, h =O[𝓟 (Ici x)] (fun _ => (1 : ℝ))) {x₀ : ℝ} (hx₀ : a < x₀) :
    P₀ * ‖deriv h x₀‖ ≤ P₁ x₀ * (Real.exp (P₀ * ∫ v in Ioi x₀, Q v * ‖ψ v‖) - 1) := by
  simpa only [Ioi_inter_Ioi_of_le hx₀.le] using
    mul_norm_deriv_volterra_solution_le_exp_sub_one_on isOpen_Ioi
      (hK.mono fun p hp => ⟨hp.1, hp.2.2⟩) hKdiag
      (fun x hx v _ hxv => hK₁ x hx v hxv)
      (hK₁_cont.mono fun p hp => ⟨hp.1, hp.2.2⟩) hψ hP₀ hP₁ hQ0
      (fun x hx v _ hxv => hKle x hx v hxv)
      (fun x hx v _ hxv => hK₁_le x hx v hxv)
      (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hΦψ x hx) hh
      (fun x hx => by rw [Ioi_inter_Ioi_of_le hx.le]; exact hh_eq x hx)
      (fun x hx => by rw [Ioi_inter_Ici_of_lt hx]; exact hhO x hx) hx₀

end RayDeriv

end TauCeti
