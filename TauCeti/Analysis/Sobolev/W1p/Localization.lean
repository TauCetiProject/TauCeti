/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Extension
public import TauCeti.Analysis.Sobolev.W1p.Extension
public import TauCeti.Analysis.Sobolev.W1p.Multiplication
public import TauCeti.Analysis.Sobolev.W1p.Restriction

/-!
# Sobolev localization across a chart boundary

For open sets `U ≤ Ω` and a smooth bounded multiplier `ψ` with bounded gradient, assume
`Ω ∩ tsupport ψ ⊆ U`. Multiplication by `ψ` followed by zero extension defines the bounded
operator `TauCeti.W1p.localizeL : W^{1,p}(U) →L[ℝ] W^{1,p}(Ω)`. Its norm is at most `2 M`
when both multiplier bounds are `M`, for every `1 ≤ p ≤ ∞`.

This localizes a function from a boundary-chart intersection to the original domain. The
support condition avoids the artificial boundary of the chart, while allowing nonzero
values at the physical boundary of `Ω`. Restricting the result to `U` recovers `ψ u`,
and localizing the restriction of a function on `Ω` equals multiplication by `ψ` there.
These identities allow local boundary constructions to be assembled with a partition of
unity.

The construction reuses `TauCeti.W1p.contDiffSMulL` and zero extension of the ambient
value-gradient jet; admissibility follows from
`TauCeti.HasWeakFDerivOn.indicator_of_isClosed`. The localization argument is the one in
L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.4 (extension by boundary charts).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal Gradient

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {U Ω : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {ψ : E → ℝ} {M : ℝ}

private theorem localize_mem (hU : U ≤ Ω) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ U, |ψ x| ≤ M) (hgM : ∀ x ∈ U, ‖∇ ψ x‖ ≤ M)
    (hs : (Ω : Set E) ∩ tsupport ψ ⊆ U) (u : W1p μ U p) :
    Sobolev1JetLp.extendByZeroₗᵢ hU
      (W1p.contDiffSMul ψ hψ hM hψM hgM u : Sobolev1JetLp μ U p) ∈
      w1pSubmodule μ Ω p := by
  let w := W1p.contDiffSMul ψ hψ hM hψM hgM u
  have hv : ∀ᵐ x ∂μ.restrict U, x ∉ tsupport ψ → W1p.value w x = 0 := by
    filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM hgM u] with x hx hxs
    simp [w, hx, image_eq_zero_of_notMem_tsupport hxs]
  have hg : ∀ᵐ x ∂μ.restrict U, x ∉ tsupport ψ → innerSL ℝ (W1p.gradient w x) = 0 := by
    filter_upwards [W1p.gradient_contDiffSMul_ae hψ hM hψM hgM u] with x hx hxs
    have hgrad : ∇ ψ x = 0 := by
      rw [gradient, fderiv_of_notMem_tsupport ℝ hxs, map_zero]
    simp [w, hx, image_eq_zero_of_notMem_tsupport hxs, hgrad]
  have hw := (W1p.hasWeakFDerivOn w).indicator_of_isClosed (isClosed_tsupport ψ) hs hv hg
  rw [mem_w1pSubmodule_iff_hasWeakFDerivOn]
  have hvalue := coeFn_extendByZeroLpₗᵢ ℝ U.isOpen.measurableSet
    (SetLike.coe_subset_coe.mpr hU) (W1p.value w)
  have hgradient := coeFn_extendByZeroLpₗᵢ ℝ U.isOpen.measurableSet
    (SetLike.coe_subset_coe.mpr hU) (W1p.gradient w)
  simp only [Sobolev1JetLp.value_extendByZeroₗᵢ, ← W1p.value_coe]
  refine (hw.congr_ae hvalue.symm).congr_ae_deriv ?_
  filter_upwards [hgradient] with x hx
  dsimp only [w] at hx ⊢
  ext v
  simp only [Sobolev1JetLp.candidateWeakFDeriv_apply,
    Sobolev1JetLp.gradient_extendByZeroₗᵢ, ← W1p.gradient_coe]
  by_cases hxU : x ∈ (U : Set E) <;>
    simp [hx, hxU, real_inner_comm]

/-- Multiply a Sobolev function on `U` by a smooth cutoff, then extend it by zero to `Ω`.
The relative support condition permits nonzero values on the physical boundary of `Ω`.
The operator is bounded for every `1 ≤ p ≤ ∞`, including both endpoints. -/
def W1p.localizeL (hU : U ≤ Ω) (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ U, |ψ x| ≤ M) (hgM : ∀ x ∈ U, ‖∇ ψ x‖ ≤ M)
    (hs : (Ω : Set E) ∩ tsupport ψ ⊆ U) : W1p μ U p →L[ℝ] W1p μ Ω p :=
  ContinuousLinearMap.codRestrict
    ((Sobolev1JetLp.extendByZeroₗᵢ hU).toContinuousLinearMap.comp
      ((w1pSubmodule μ U p).toSubmodule.subtypeL.comp (W1p.contDiffSMulL ψ hψ hM hψM hgM)))
    (w1pSubmodule μ Ω p).toSubmodule (by
      intro u
      simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        W1p.contDiffSMulL_apply, LinearIsometry.coe_toContinuousLinearMap,
        ClosedSubmodule.mem_toSubmodule_iff] using
        localize_mem (μ := μ) (p := p) hU hψ hM hψM hgM hs u)

/-- The ambient jet of a localized function is the zero extension of its cutoff product. -/
@[simp]
theorem W1p.coe_localizeL (hU : U ≤ Ω) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ U, |ψ x| ≤ M) (hgM : ∀ x ∈ U, ‖∇ ψ x‖ ≤ M)
    (hs : (Ω : Set E) ∩ tsupport ψ ⊆ U) (u : W1p μ U p) :
    (W1p.localizeL hU ψ hψ hM hψM hgM hs u : Sobolev1JetLp μ Ω p) =
      Sobolev1JetLp.extendByZeroₗᵢ hU
        (W1p.contDiffSMul ψ hψ hM hψM hgM u : Sobolev1JetLp μ U p) := by
  simp [W1p.localizeL]

/-- The value of a localized function is `ψ u` on `U` and zero outside `U`. -/
theorem W1p.value_localizeL_ae (hU : U ≤ Ω) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ U, |ψ x| ≤ M) (hgM : ∀ x ∈ U, ‖∇ ψ x‖ ≤ M)
    (hs : (Ω : Set E) ∩ tsupport ψ ⊆ U) (u : W1p μ U p) :
    W1p.value (W1p.localizeL hU ψ hψ hM hψM hgM hs u) =ᵐ[μ.restrict Ω]
      (U : Set E).indicator (fun x => ψ x • W1p.value u x) := by
  rw [W1p.value_coe, W1p.coe_localizeL, Sobolev1JetLp.value_extendByZeroₗᵢ, ← W1p.value_coe]
  exact (coeFn_extendByZeroLpₗᵢ ℝ U.isOpen.measurableSet _ _).trans
    (ae_restrict_of_ae ((ae_eq_restrict_iff_indicator_ae_eq U.isOpen.measurableSet).1
      (W1p.value_contDiffSMul_ae hψ hM hψM hgM u)))

/-- The weak gradient of localization is the zero extension of `ψ ∇u + u ∇ψ`. -/
theorem W1p.gradient_localizeL_ae (hU : U ≤ Ω) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ U, |ψ x| ≤ M) (hgM : ∀ x ∈ U, ‖∇ ψ x‖ ≤ M)
    (hs : (Ω : Set E) ∩ tsupport ψ ⊆ U) (u : W1p μ U p) :
    W1p.gradient (W1p.localizeL hU ψ hψ hM hψM hgM hs u) =ᵐ[μ.restrict Ω]
      (U : Set E).indicator (fun x => ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) := by
  rw [W1p.gradient_coe, W1p.coe_localizeL, Sobolev1JetLp.gradient_extendByZeroₗᵢ,
    ← W1p.gradient_coe]
  exact (coeFn_extendByZeroLpₗᵢ ℝ U.isOpen.measurableSet _ _).trans
    (ae_restrict_of_ae ((ae_eq_restrict_iff_indicator_ae_eq U.isOpen.measurableSet).1
      (W1p.gradient_contDiffSMul_ae hψ hM hψM hgM u)))

/-- Localization has the same norm as the cutoff product on the source domain. -/
@[simp]
theorem W1p.norm_localizeL (hU : U ≤ Ω) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ U, |ψ x| ≤ M) (hgM : ∀ x ∈ U, ‖∇ ψ x‖ ≤ M)
    (hs : (Ω : Set E) ∩ tsupport ψ ⊆ U) (u : W1p μ U p) :
    ‖W1p.localizeL hU ψ hψ hM hψM hgM hs u‖ = ‖W1p.contDiffSMul ψ hψ hM hψM hgM u‖ := by
  rw [← Submodule.norm_coe, W1p.coe_localizeL, LinearIsometry.norm_map, Submodule.norm_coe]

/-- The explicit cutoff bound `‖localizeL u‖ ≤ 2 M ‖u‖`. -/
theorem W1p.norm_localizeL_le (hU : U ≤ Ω) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ U, |ψ x| ≤ M) (hgM : ∀ x ∈ U, ‖∇ ψ x‖ ≤ M)
    (hs : (Ω : Set E) ∩ tsupport ψ ⊆ U) (u : W1p μ U p) :
    ‖W1p.localizeL hU ψ hψ hM hψM hgM hs u‖ ≤ 2 * M * ‖u‖ := by
  rw [W1p.norm_localizeL]
  exact W1p.norm_contDiffSMul_le hψ hM hψM hgM u

/-- The localization operator has norm at most `2 M`. -/
theorem W1p.opNorm_localizeL_le (hU : U ≤ Ω) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ U, |ψ x| ≤ M) (hgM : ∀ x ∈ U, ‖∇ ψ x‖ ≤ M)
    (hs : (Ω : Set E) ∩ tsupport ψ ⊆ U) :
    ‖W1p.localizeL (μ := μ) (p := p) hU ψ hψ hM hψM hgM hs‖ ≤ 2 * M :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (W1p.norm_localizeL_le hU hψ hM hψM hgM hs)

/-- Restricting localization back to the source domain recovers multiplication by the cutoff. -/
@[simp]
theorem W1p.restrictL_localizeL (hU : U ≤ Ω) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ U, |ψ x| ≤ M) (hgM : ∀ x ∈ U, ‖∇ ψ x‖ ≤ M)
    (hs : (Ω : Set E) ∩ tsupport ψ ⊆ U) (u : W1p μ U p) :
    W1p.restrictL hU (W1p.localizeL hU ψ hψ hM hψM hgM hs u) =
      W1p.contDiffSMul ψ hψ hM hψM hgM u := by
  apply W1p.ext_value
  apply Lp.ext
  refine (W1p.value_restrictL_ae hU _).trans ?_
  rw [W1p.value_coe, W1p.coe_localizeL, Sobolev1JetLp.value_extendByZeroₗᵢ, ← W1p.value_coe]
  exact coeFn_extendByZeroLpₗᵢ_restrict ℝ U.isOpen.measurableSet _ _

/-- Localizing the restriction of a Sobolev function equals its cutoff product on `Ω`. -/
@[simp]
theorem W1p.localizeL_restrictL (hU : U ≤ Ω) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : (Ω : Set E) ∩ tsupport ψ ⊆ U) (u : W1p μ Ω p) :
    W1p.localizeL hU ψ hψ hM (fun x hx => hψM x (hU hx))
      (fun x hx => hgM x (hU hx)) hs (W1p.restrictL hU u) =
      W1p.contDiffSMul ψ hψ hM hψM hgM u := by
  apply W1p.ext_value
  apply Lp.ext
  filter_upwards [W1p.value_localizeL_ae hU hψ hM _ _ hs (W1p.restrictL hU u),
    W1p.value_contDiffSMul_ae hψ hM hψM hgM u,
    ((ae_restrict_iff' U.isOpen.measurableSet).1 (W1p.value_restrictL_ae hU u)).filter_mono
      (ae_mono Measure.restrict_le_self), ae_restrict_mem Ω.isOpen.measurableSet]
    with x hx hy hz hxΩ
  rw [hx, hy]
  by_cases hxU : x ∈ (U : Set E)
  · rw [indicator_of_mem hxU, hz hxU]
  · have hxψ : x ∉ tsupport ψ := fun hxs => hxU (hs ⟨hxΩ, hxs⟩)
    simp [indicator_of_notMem hxU, image_eq_zero_of_notMem_tsupport hxψ]

end TauCeti
