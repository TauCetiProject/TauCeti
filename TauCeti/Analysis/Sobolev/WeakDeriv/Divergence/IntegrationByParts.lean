/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Basic
public import TauCeti.Analysis.Sobolev.Mollification.TestField
public import TauCeti.Analysis.Sobolev.Leibniz
public import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero

/-!
# Weak divergence tested against Sobolev functions

A field `u` with weak divergence `g` on an open set `Ω` satisfies `∫ ⟪u, ∇φ⟫ = -∫ φ g` for test
functions `φ` by definition. This file extends the identity to weakly differentiable scalar
functions `ψ` with weak derivative `Dψ`, where the pairing `⟪u, ∇ψ⟫` reads `Dψ x (u x)`:

* `TauCeti.HasWeakDivergenceOn.setIntegral_apply_eq_neg_integral_mul_of_hasCompactSupport`:
  if `ψ` is supported in a compact subset of `Ω`, with `ψ ∈ Lᵗ` and `Dψ ∈ Lˢ`, and `u` and `g`
  are locally in the conjugate exponents `s'` and `t'` on `Ω`, then
  `∫_Ω Dψ (u) = -∫ ψ g`.
* `TauCeti.HasWeakDivergenceOn.integral_apply_eq_neg_integral_mul`: on the whole space the
  support condition is replaced by integrability of `Dψ (u)`, `ψ g` and `ψ u`.

The first statement mollifies `ψ` into test functions
(`TauCeti.HasWeakFDerivOn.exists_seq_testFunction_convolution_normed`) and passes to the limit in
both pairings by Hölder's inequality. The second multiplies `ψ` by the expanding cutoffs of
`TauCeti.exists_expanding_cutoff`, whose gradients are `O(1 / n)`, and passes to the limit by
dominated convergence. Integration by parts against products of Sobolev fields, such as the
antisymmetry of the convective form `∫ ⟪(u · ∇) v, w⟫` for divergence-free `u`, rests on the
second statement.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal Gradient InnerProductSpace Topology Convolution ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Opens E} {u : E → E} {g : E → ℝ} {ψ : E → ℝ} {Dψ : E → E →L[ℝ] ℝ}
  {s s' t t' : ℝ≥0∞}

/-- **Weak divergence against a compactly supported Sobolev function.** Let `u` have weak
divergence `g` on `Ω`, and let `ψ` have a weak derivative `Dψ` on `Ω`, with support in a compact
subset of `Ω`. If `ψ ∈ Lᵗ`, `Dψ ∈ Lˢ(Ω)`, and `u` and `g` lie in the conjugate exponents `s'`
and `t'` on compact subsets of `Ω`, then `∫_Ω Dψ (u) = -∫ ψ g`. -/
theorem HasWeakDivergenceOn.setIntegral_apply_eq_neg_integral_mul_of_hasCompactSupport
    [s.HolderConjugate s'] [t.HolderConjugate t'] (hu : HasWeakDivergenceOn μ Ω u g)
    (hψ : HasWeakFDerivOn μ Ω ψ Dψ) (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω)
    (hψt : MemLp ψ t μ) (hDψ : MemLp Dψ s (μ.restrict Ω))
    (huK : ∀ K, IsCompact K → K ⊆ Ω → MemLp u s' (μ.restrict K))
    (hgK : ∀ K, IsCompact K → K ⊆ Ω → MemLp g t' (μ.restrict K)) :
    ∫ x in Ω, Dψ x (u x) ∂μ = -∫ x, ψ x * g x ∂μ := by
  obtain ⟨K', hK'c, hK'm, hK'Ω, hψK', ρ, φ, hρ, hφ, hφs, hderiv⟩ :=
    hψ.exists_seq_testFunction_convolution_normed hψc hψΩ hψt
      (ENNReal.HolderConjugate.one_le t t') hDψ (ENNReal.HolderConjugate.one_le s s')
  have hK'n : ∀ n, ∀ x ∉ K', (φ n : E → ℝ) x = 0 ∧ fderiv ℝ (φ n : E → ℝ) x = 0 :=
    fun n x hx ↦ ⟨image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφs n h),
      fderiv_of_notMem_tsupport ℝ fun h ↦ hx (hφs n h)⟩
  -- The pairings with the gradients of the mollifications converge.
  have hL : Tendsto (fun n ↦ ∫ x, ⟪u x, ∇ (φ n : E → ℝ) x⟫_ℝ ∂μ) atTop
      (𝓝 (∫ x in Ω, Dψ x (u x) ∂μ)) := by
    have hDψ' : MemLp ((Ω : Set E).indicator Dψ) s μ :=
      (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).2 hDψ
    have hu' : MemLp (K'.indicator u) s' μ :=
      (memLp_indicator_iff_restrict hK'm.nullMeasurableSet).2 (huK K' hK'c hK'Ω)
    have := (ContinuousLinearMap.apply ℝ ℝ : E →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ)
      |>.tendsto_integral_bilin_normed_convolution hρ hu' hDψ'
    convert this using 1
    · funext n
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      by_cases hx : x ∈ K'
      · simp [inner_gradient_right, hderiv n x hx, indicator_of_mem hx]
      · simp [inner_gradient_right, (hK'n n x hx).2, indicator_of_notMem hx]
    · congr 1
      rw [← integral_indicator Ω.isOpen.measurableSet]
      have hae := (ae_restrict_iff' Ω.isOpen.measurableSet).1 hψ.ae_eq_zero_of_notMem_tsupport
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      by_cases hxK : x ∈ K'
      · simp [indicator_of_mem hxK, indicator_of_mem (hK'Ω hxK)]
      · by_cases hxΩ : x ∈ (Ω : Set E)
        · simp [indicator_of_notMem hxK, indicator_of_mem hxΩ, hx hxΩ fun h ↦ hxK (hψK' h)]
        · simp [indicator_of_notMem hxK, indicator_of_notMem hxΩ]
  -- The pairings of the mollifications with the divergence converge.
  have hR : Tendsto (fun n ↦ ∫ x, (φ n : E → ℝ) x * g x ∂μ) atTop (𝓝 (∫ x, ψ x * g x ∂μ)) := by
    have hg' : MemLp (K'.indicator g) t' μ :=
      (memLp_indicator_iff_restrict hK'm.nullMeasurableSet).2 (hgK K' hK'c hK'Ω)
    have := (ContinuousLinearMap.mul ℝ ℝ).tendsto_integral_bilin_normed_convolution hρ hg' hψt
    convert this using 1
    · funext n
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      by_cases hx : x ∈ K'
      · simp [← hφ n, indicator_of_mem hx, mul_comm]
      · simp [(hK'n n x hx).1, indicator_of_notMem hx]
    · congr 1
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      by_cases hx : x ∈ K'
      · simp [indicator_of_mem hx, mul_comm]
      · simp [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport fun h ↦ hx (hψK' h)]
  exact tendsto_nhds_unique hL (hR.neg.congr fun n ↦
    (hu.integral_inner_gradient_eq_neg_integral_mul (φ n)).symm)

/-- The whole-space identity localized by a cutoff: for a smooth compactly supported `χ` with
`|χ| ≤ 1` and `‖Dχ‖ ≤ C`, `∫ χ Dψ (u) + ∫ Dχ (u) ψ = -∫ χ ψ g`. -/
private theorem HasWeakDivergenceOn.integral_mul_apply_add_integral_fderiv_apply_mul
    [s.HolderConjugate s'] [t.HolderConjugate t'] (hu : HasWeakDivergenceOn μ ⊤ u g)
    (hψ : HasWeakFDerivOn μ ⊤ ψ Dψ) (hst : s ≤ t)
    (hψt : ∀ K, IsCompact K → MemLp ψ t (μ.restrict K))
    (hDψ : ∀ K, IsCompact K → MemLp Dψ s (μ.restrict K))
    (huK : ∀ K, IsCompact K → MemLp u s' (μ.restrict K))
    (hgK : ∀ K, IsCompact K → MemLp g t' (μ.restrict K))
    (hDψu : Integrable (fun x ↦ Dψ x (u x)) μ) {χ : E → ℝ} {C : ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχ1 : ∀ x, ‖χ x‖ ≤ 1) (hdχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ C)
    (hdχi : Integrable (fun x ↦ fderiv ℝ χ x (u x) * ψ x) μ) :
    ∫ x, χ x * Dψ x (u x) ∂μ + ∫ x, fderiv ℝ χ x (u x) * ψ x ∂μ =
      -∫ x, χ x * (ψ x * g x) ∂μ := by
  have hKc : IsCompact (tsupport χ) := hχc
  have hKm : NullMeasurableSet (tsupport χ) μ :=
    (isClosed_tsupport χ).measurableSet.nullMeasurableSet
  have : IsFiniteMeasure (μ.restrict (tsupport χ)) :=
    isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
  have hoff (x : E) (hx : x ∉ tsupport χ) : χ x = 0 ∧ fderiv ℝ χ x = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport hx, fderiv_of_notMem_tsupport ℝ hx⟩
  -- `χ ψ ∈ Lᵗ` and its weak derivative `χ Dψ + Dχ ⊗ ψ` is in `Lˢ`.
  have hψχ : MemLp (fun x ↦ χ x • ψ x) t μ := by
    refine MemLp.of_restrict_of_support_subset hKm ((hψt _ hKc).of_le
      (hχ.continuous.aestronglyMeasurable.smul (hψt _ hKc).aestronglyMeasurable)
      (.of_forall fun x ↦ ?_)) fun x hx ↦ by_contra fun h ↦ hx (by simp [(hoff x h).1])
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 x)
  have hDψχ : MemLp (fun x ↦ χ x • Dψ x + (fderiv ℝ χ x).smulRight (ψ x)) s
      (μ.restrict (⊤ : Opens E)) := by
    rw [Opens.coe_top, Measure.restrict_univ]
    have heq : (fun x ↦ (fderiv ℝ χ x).smulRight (ψ x)) = fun x ↦ ψ x • fderiv ℝ χ x := by
      ext x y
      simp [mul_comm]
    have h₁ : MemLp (fun x ↦ χ x • Dψ x) s (μ.restrict (tsupport χ)) :=
      (hDψ _ hKc).of_le (hχ.continuous.aestronglyMeasurable.smul (hDψ _ hKc).aestronglyMeasurable)
        (.of_forall fun x ↦ by
          rw [norm_smul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 x))
    have h₂ : MemLp (fun x ↦ (fderiv ℝ χ x).smulRight (ψ x)) s (μ.restrict (tsupport χ)) := by
      refine ((hψt _ hKc).mono_exponent hst).of_le_mul (c := C) ?_ (.of_forall fun x ↦ ?_)
      · rw [heq]
        exact (hψt _ hKc).aestronglyMeasurable.smul
          (hχ.continuous_fderiv (by simp)).aestronglyMeasurable
      · rw [ContinuousLinearMap.norm_smulRight_apply]
        exact mul_le_mul_of_nonneg_right (hdχ x) (norm_nonneg _)
    exact MemLp.of_restrict_of_support_subset hKm (h₁.add h₂) fun x hx ↦ by_contra fun h ↦
      hx (by simp [(hoff x h).1, (hoff x h).2])
  have h := hu.setIntegral_apply_eq_neg_integral_mul_of_hasCompactSupport
    (hψ.contDiff_smul hχ) hχc.smul_right (by simp) hψχ hDψχ
    (fun K hK _ ↦ huK K hK) (fun K hK _ ↦ hgK K hK)
  simp only [Opens.coe_top, Measure.restrict_univ, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul] at h
  rw [integral_add (hDψu.bdd_mul hχ.continuous.aestronglyMeasurable (.of_forall hχ1)) hdχi] at h
  simpa only [mul_assoc] using h

/-- **Weak divergence against a Sobolev function on the whole space.** Let `u` have weak
divergence `g` on the whole space, and let `ψ` have a weak derivative `Dψ`. Suppose that `ψ` and
`g` lie locally in conjugate exponents `t` and `t'`, that `Dψ` and `u` lie locally in conjugate
exponents `s ≤ t` and `s'`, and that `Dψ (u)`, `ψ g` and `ψ u` are integrable. Then
`∫ Dψ (u) = -∫ ψ g`.

The condition `s ≤ t` loses nothing: if `ψ` is locally in `Lˢ` and `Lᵗ`, it is locally in
`L^{max s t}`, and the conjugate of `max s t` is at most `t'`. -/
theorem HasWeakDivergenceOn.integral_apply_eq_neg_integral_mul
    [s.HolderConjugate s'] [t.HolderConjugate t'] (hu : HasWeakDivergenceOn μ ⊤ u g)
    (hψ : HasWeakFDerivOn μ ⊤ ψ Dψ) (hst : s ≤ t)
    (hψt : ∀ K, IsCompact K → MemLp ψ t (μ.restrict K))
    (hDψ : ∀ K, IsCompact K → MemLp Dψ s (μ.restrict K))
    (huK : ∀ K, IsCompact K → MemLp u s' (μ.restrict K))
    (hgK : ∀ K, IsCompact K → MemLp g t' (μ.restrict K))
    (hDψu : Integrable (fun x ↦ Dψ x (u x)) μ) (hψg : Integrable (fun x ↦ ψ x * g x) μ)
    (hψu : Integrable (fun x ↦ ψ x • u x) μ) :
    ∫ x, Dψ x (u x) ∂μ = -∫ x, ψ x * g x ∂μ := by
  obtain ⟨χ, C, hC, hχ, hlim⟩ := exists_expanding_cutoff (E := E)
  have hum : AEStronglyMeasurable u μ := by
    simpa using hu.locallyIntegrableOn.aestronglyMeasurable
  have hψm : AEStronglyMeasurable ψ μ := by
    simpa using hψ.locallyIntegrableOn.aestronglyMeasurable
  -- The cutoff term is bounded by `C n ‖ψ u‖`.
  have hdχb (n : ℕ) (x : E) : ‖fderiv ℝ (χ n) x (u x) * ψ x‖ ≤ C n * ‖ψ x • u x‖ := by
    rw [norm_mul, norm_smul, mul_comm ‖ψ x‖, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (((fderiv ℝ (χ n) x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((hχ n).2.2 x).2 (norm_nonneg _))) (norm_nonneg _)
  have hdχi (n : ℕ) : Integrable (fun x ↦ fderiv ℝ (χ n) x (u x) * ψ x) μ :=
    (hψu.norm.const_mul (C n)).mono' (((ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).continuous₂
      |>.comp_aestronglyMeasurable₂ (((hχ n).1.continuous_fderiv (by simp)).aestronglyMeasurable)
        hum).mul hψm) (.of_forall (hdχb n))
  -- Pass to the limit `n → ∞` in the three terms of the localized identity.
  have T₁ : Tendsto (fun n ↦ ∫ x, χ n x * Dψ x (u x) ∂μ) atTop (𝓝 (∫ x, Dψ x (u x) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖Dψ x (u x)‖)
      (fun n ↦ (hχ n).1.continuous.aestronglyMeasurable.mul hDψu.1) hDψu.norm
      (fun n ↦ .of_forall fun x ↦ ?_) (.of_forall fun x ↦ ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) ((hχ n).2.2 x).1
    · simpa using (hlim x).mul_const (Dψ x (u x))
  have T₂ : Tendsto (fun n ↦ ∫ x, fderiv ℝ (χ n) x (u x) * ψ x ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n ↦ ?_) (by simpa using hC.mul_const (∫ x, ‖ψ x • u x‖ ∂μ))
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le (hψu.norm.const_mul _) (.of_forall (hdχb n))
  have T₃ : Tendsto (fun n ↦ ∫ x, χ n x * (ψ x * g x) ∂μ) atTop (𝓝 (∫ x, ψ x * g x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖ψ x * g x‖)
      (fun n ↦ (hχ n).1.continuous.aestronglyMeasurable.mul hψg.1) hψg.norm
      (fun n ↦ .of_forall fun x ↦ ?_) (.of_forall fun x ↦ ?_)
    · rw [norm_mul (χ n x)]
      exact mul_le_of_le_one_left (norm_nonneg _) ((hχ n).2.2 x).1
    · simpa using (hlim x).mul_const (ψ x * g x)
  exact tendsto_nhds_unique (by simpa using T₁.add T₂) (T₃.neg.congr fun n ↦
    (hu.integral_mul_apply_add_integral_fderiv_apply_mul hψ hst hψt hDψ huK hgK hDψu (hχ n).1
      (hχ n).2.1 (fun x ↦ ((hχ n).2.2 x).1) (fun x ↦ ((hχ n).2.2 x).2) (hdχi n)).symm)

end TauCeti
