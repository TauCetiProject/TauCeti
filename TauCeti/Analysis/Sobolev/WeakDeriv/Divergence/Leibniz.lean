/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Basic
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Distribution.TestFunction.Approximation
import TauCeti.Analysis.Distribution.TestFunction.Gradient
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# The product rule for the weak divergence

For a field `u` with weak divergence `g` on an open set `Ω` and a scalar `χ` that is `C¹` on `Ω`,
the field `χ u` has weak divergence

`div (χ u) = χ div u + ⟪∇χ, u⟫`

on `Ω` (`TauCeti.HasWeakDivergenceOn.contDiffOn_smul`). Nothing is assumed about `χ` off `Ω`, and
the measure is arbitrary. For a solenoidal `u` this reads `div (χ u) = ⟪∇χ, u⟫`
(`TauCeti.IsSolenoidalOn.hasWeakDivergenceOn_contDiffOn_smul`): multiplying a divergence-free
field by a cutoff produces exactly this error term, which is the quantity a divergence-free
cutoff argument has to correct.

Since `χ φ` is only `C¹` for a test function `φ`, the rule rests on extending the defining
identity of the weak divergence from `𝓓(Ω, ℝ)` to `C¹` functions compactly supported in `Ω`
(`TauCeti.HasWeakDivergenceOn.integral_inner_gradient_eq_neg_integral_mul_of_contDiff`), by
approximating them in `C¹` by test functions supported in one compact subset of `Ω`.

## Main results

* `TauCeti.HasWeakDivergenceOn.integral_inner_gradient_eq_neg_integral_mul_of_contDiff`: the
  identity `∫ ⟪u, ∇φ⟫ = -∫ φ g` for `C¹` functions `φ` compactly supported in `Ω`.
* `TauCeti.hasWeakDivergenceOn_iff_contDiff_one`: the weak divergence is characterized by these
  `C¹` test functions.
* `TauCeti.HasWeakDivergenceOn.contDiffOn_smul`: the product rule
  `div (χ u) = χ div u + ⟪∇χ, u⟫` for `χ` of class `C¹` on `Ω`.
* `TauCeti.IsSolenoidalOn.hasWeakDivergenceOn_contDiffOn_smul`: its solenoidal case.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §3.1 (the Leibniz
  rule for the product of a distribution and a smooth function).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.3, Theorem 1(iv).
-/

public section

namespace TauCeti

open _root_.MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Gradient InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} {Ω : Opens E} {u : E → E}
  {g : E → ℝ}

/-- If a test function `ψ` is within `η` of a `C¹` function `φ` in `C¹`, both supported in a
compact `K ⊆ Ω`, then `φ` satisfies the defining identity of the weak divergence up to an error
`η (∫_K ‖u‖ + ∫_K ‖g‖)`. -/
private theorem HasWeakDivergenceOn.norm_integral_inner_gradient_add_integral_mul_le
    (hu : HasWeakDivergenceOn μ Ω u g) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφK : tsupport φ ⊆ K) {ψ : 𝓓(Ω, ℝ)}
    (hψK : tsupport ψ ⊆ K) {η : ℝ}
    (hψ : ∀ x, dist (ψ x) (φ x) ≤ η ∧ dist (fderiv ℝ ψ x) (fderiv ℝ φ x) ≤ η) :
    ‖(∫ x, ⟪u x, ∇ φ x⟫_ℝ ∂μ) + ∫ x, φ x * g x ∂μ‖ ≤
      η * ((∫ x in K, ‖u x‖ ∂μ) + ∫ x in K, ‖g x‖ ∂μ) := by
  -- The gradient of a `C¹` function supported in `K` pairs integrably with `u`.
  have hint : ∀ f : E → ℝ, ContDiff ℝ 1 f → tsupport f ⊆ K →
      Integrable (fun x ↦ ⟪u x, ∇ f x⟫_ℝ) μ := fun f hf hfK ↦ by
    have hsupp : tsupport (∇ f) ⊆ K := by
      rw [gradient_eq_toDual_symm_comp_fderiv]
      exact (tsupport_comp_subset (map_zero _) _).trans ((tsupport_fderiv_subset ℝ).trans hfK)
    simpa only [real_inner_comm] using
      hu.locallyIntegrableOn.integrable_inner_left_of_hasCompactSupport (𝕜 := ℝ)
        (hf.continuous_gradient one_ne_zero).continuousOn
        (hK.of_isClosed_subset (isClosed_tsupport _) hsupp) (hsupp.trans hKΩ)
  -- The gradient terms differ by at most `η ∫_K ‖u‖`.
  have h1 : ‖(∫ x, ⟪u x, ∇ φ x⟫_ℝ ∂μ) - ∫ x, ⟪u x, ∇ (ψ : E → ℝ) x⟫_ℝ ∂μ‖ ≤
      η * ∫ x in K, ‖u x‖ ∂μ := by
    have hKint : ∫ x in K, ⟪u x, ∇ φ x - ∇ (ψ : E → ℝ) x⟫_ℝ ∂μ =
        ∫ x, ⟪u x, ∇ φ x - ∇ (ψ : E → ℝ) x⟫_ℝ ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [gradient_of_notMem_tsupport (hx <| hφK ·),
          gradient_of_notMem_tsupport (hx <| hψK ·), sub_zero, inner_zero_right]
    rw [← integral_sub (hint φ hφ hφK) (hint ψ (ψ.contDiff.of_le (by simp)) hψK)]
    simp_rw [← inner_sub_right]
    rw [← hKint, ← integral_const_mul]
    refine norm_integral_le_of_norm_le
      ((hu.locallyIntegrableOn.integrableOn_compact_subset hKΩ hK).norm.const_mul η)
      (.of_forall fun x ↦ ?_)
    rw [mul_comm η]
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [norm_gradient_sub_gradient_eq_norm_fderiv_sub, ← dist_eq_norm, dist_comm]
    exact (hψ x).2
  -- The divergence terms differ by at most `η ∫_K ‖g‖`.
  have h2 : ‖(∫ x, φ x * g x ∂μ) - ∫ x, (ψ : E → ℝ) x * g x ∂μ‖ ≤
      η * ∫ x in K, ‖g x‖ ∂μ := by
    simpa only [smul_eq_mul] using MeasureTheory.norm_integral_smul_sub_le hK
      (hu.locallyIntegrableOn_divergence.integrableOn_compact_subset hKΩ hK)
      hφ.continuous.continuousOn ψ.continuous.continuousOn hφK hψK fun x _ ↦ by
        simpa only [dist_comm] using (hψ x).1
  rw [mul_add]
  refine le_trans (le_of_eq ?_) ((norm_add_le _ _).trans (add_le_add h1 h2))
  rw [hu.integral_inner_gradient_eq_neg_integral_mul ψ]
  abel_nf

/-- **Weak divergence against `C¹` functions.** The defining identity `∫ ⟪u, ∇φ⟫ = -∫ φ g` of a
weak divergence holds for every `C¹` function `φ` compactly supported in `Ω`, not only for test
functions. -/
theorem HasWeakDivergenceOn.integral_inner_gradient_eq_neg_integral_mul_of_contDiff
    (hu : HasWeakDivergenceOn μ Ω u g) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) :
    ∫ x, ⟪u x, ∇ φ x⟫_ℝ ∂μ = -∫ x, φ x * g x ∂μ := by
  by_cases hfd : FiniteDimensional ℝ E
  swap
  · obtain rfl := (hφc.eq_zero_or_finiteDimensional ℝ hφ.continuous).resolve_right hfd
    simp
  -- Approximate `φ` in `C¹` by test functions supported in a compact thickening `K ⊆ Ω`.
  obtain ⟨δ, hδ, hδΩ⟩ := hφc.isCompact.exists_cthickening_subset_open Ω.isOpen hφs
  set C := (∫ x in cthickening δ (tsupport φ), ‖u x‖ ∂μ) +
    ∫ x in cthickening δ (tsupport φ), ‖g x‖ ∂μ
  have hC : 0 ≤ C := by positivity
  rw [eq_neg_iff_add_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨ψ, hψK, hψ⟩ := hφ.exists_testFunction_dist_le_and_dist_fderiv_le
    hφc.isCompact subset_rfl hδ hδΩ (div_pos hε (by linarith : (0 : ℝ) < C + 1))
  refine (hu.norm_integral_inner_gradient_add_integral_mul_le hφc.isCompact.cthickening hδΩ hφ
    (self_subset_cthickening _) hψK hψ).trans ?_
  rw [zero_add, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

/-- The weak divergence is characterized by integration by parts against all `C¹` functions
compactly supported in `Ω`. -/
theorem hasWeakDivergenceOn_iff_contDiff_one (hu : LocallyIntegrableOn u Ω μ)
    (hg : LocallyIntegrableOn g Ω μ) :
    HasWeakDivergenceOn μ Ω u g ↔
      ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        ∫ x, ⟪u x, ∇ φ x⟫_ℝ ∂μ = -∫ x, φ x * g x ∂μ := by
  refine ⟨fun h φ hφ hφc hφs ↦
    h.integral_inner_gradient_eq_neg_integral_mul_of_contDiff hφ hφc hφs,
    fun h ↦ hasWeakDivergenceOn_iff.mpr ⟨hu, hg, fun φ ↦ ?_⟩⟩
  exact h φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset

variable [FiniteDimensional ℝ E]

/-- **The product rule for the weak divergence.** If `u` has weak divergence `g` on `Ω` and `χ`
is `C¹` on `Ω`, then `χ u` has weak divergence `χ g + ⟪∇χ, u⟫` on `Ω`. -/
theorem HasWeakDivergenceOn.contDiffOn_smul (hu : HasWeakDivergenceOn μ Ω u g) {χ : E → ℝ}
    (hχ : ContDiffOn ℝ 1 χ Ω) :
    HasWeakDivergenceOn μ Ω (fun x ↦ χ x • u x) (fun x ↦ χ x * g x + ⟪∇ χ x, u x⟫_ℝ) := by
  have hχu : LocallyIntegrableOn (fun x ↦ χ x • u x) Ω μ :=
    hu.locallyIntegrableOn.continuousOn_smul_of_isOpen Ω.isOpen hχ.continuousOn
  have hχg : LocallyIntegrableOn (fun x ↦ χ x * g x) Ω μ := by
    simpa only [smul_eq_mul] using
      hu.locallyIntegrableOn_divergence.continuousOn_smul_of_isOpen Ω.isOpen hχ.continuousOn
  have hdχ : LocallyIntegrableOn (fun x ↦ ⟪∇ χ x, u x⟫_ℝ) Ω μ := by
    simpa only [inner_gradient_left] using hu.locallyIntegrableOn.continuousOn_clm_apply
      Ω.isOpen.isLocallyClosed (hχ.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl)
  refine hasWeakDivergenceOn_iff.mpr ⟨hχu, hχg.add hdχ, fun φ ↦ ?_⟩
  -- `χ φ` is a `C¹` function compactly supported in `Ω`.
  set ψ : E → ℝ := fun x ↦ χ x * φ x
  have hψ : ContDiff ℝ 1 ψ := (ContinuousLinearMap.mul ℝ ℝ).contDiff_of_tsupport_subset_right hχ
    (φ.contDiff.of_le (by simp)).contDiffOn Ω.isOpen φ.tsupport_subset
  have hψφ : tsupport ψ ⊆ tsupport φ := tsupport_mul_subset_right
  -- The classical product rule `χ ∇φ = ∇(χ φ) - φ ∇χ`, paired with `u`.
  have hpt : ∀ x, ⟪χ x • u x, ∇ (φ : E → ℝ) x⟫_ℝ + φ x * ⟪∇ χ x, u x⟫_ℝ = ⟪u x, ∇ ψ x⟫_ℝ := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hxΩ := Ω.isOpen.mem_nhds (φ.tsupport_subset hx)
      rw [gradient_fun_mul ((hχ.differentiableOn one_ne_zero).differentiableAt hxΩ)
        (φ.contDiff.differentiable (by simp) x)]
      simp only [RCLike.conj_to_real, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, real_inner_comm (u x)]
    · rw [gradient_of_notMem_tsupport hx, gradient_of_notMem_tsupport (hx <| hψφ ·),
        image_eq_zero_of_notMem_tsupport hx]
      simp
  have hint1 : Integrable (fun x ↦ ⟪χ x • u x, ∇ (φ : E → ℝ) x⟫_ℝ) μ := by
    simpa only [real_inner_comm, TestFunction.gradientCLM_apply] using
      (TestFunction.gradientCLM φ).integrable_inner hχu
  have hint2 : Integrable (fun x ↦ φ x * ⟪∇ χ x, u x⟫_ℝ) μ := by
    simpa only [smul_eq_mul] using φ.integrable_smul hdχ
  have hint3 : Integrable (fun x ↦ φ x * (χ x * g x)) μ := by
    simpa only [smul_eq_mul] using φ.integrable_smul hχg
  have hsum : (∫ x, ⟪χ x • u x, ∇ (φ : E → ℝ) x⟫_ℝ ∂μ) + ∫ x, φ x * ⟪∇ χ x, u x⟫_ℝ ∂μ =
      -∫ x, φ x * (χ x * g x) ∂μ := by
    rw [← integral_add hint1 hint2, integral_congr_ae (.of_forall hpt),
      hu.integral_inner_gradient_eq_neg_integral_mul_of_contDiff hψ
        φ.hasCompactSupport.mul_left (hψφ.trans φ.tsupport_subset)]
    congr 1
    exact integral_congr_ae (.of_forall fun x ↦ by simp only [ψ]; ring)
  simp only [mul_add]
  rw [integral_add hint3 hint2]
  linarith

/-- **The product rule for a solenoidal field.** If `u` is solenoidal on `Ω` and `χ` is `C¹` on
`Ω`, then `χ u` has weak divergence `⟪∇χ, u⟫` on `Ω`. -/
theorem IsSolenoidalOn.hasWeakDivergenceOn_contDiffOn_smul (hu : IsSolenoidalOn μ Ω u)
    {χ : E → ℝ} (hχ : ContDiffOn ℝ 1 χ Ω) :
    HasWeakDivergenceOn μ Ω (fun x ↦ χ x • u x) (fun x ↦ ⟪∇ χ x, u x⟫_ℝ) := by
  simpa only [Pi.zero_apply, mul_zero, zero_add] using
    (isSolenoidalOn_iff_hasWeakDivergenceOn.mp hu).contDiffOn_smul hχ

end TauCeti
