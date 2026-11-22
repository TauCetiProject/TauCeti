/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Diagonal.Basic
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Eigenbasis
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure.Basic
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.SpectralIntegral
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Map
import TauCeti.Analysis.InnerProductSpace.LinearPMap.Spectral.Cutoff
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion

/-!
# Eigenbasis functional calculus for compact resolvent

For a self-adjoint partial linear map `A` with compact resolvent on a Hilbert space `H`, any
function `f : ℝ → ℂ` defines a closed partial operator `A.eigenCalculus hA h f` and any bounded
`f : ℝ → ℂ` defines a bounded operator `A.boundedEigenCalculus hA h f hf`, backed by the spectral
projection-valued measure `A.spectralPVM hA` (`ProjValMeasure.spectralIntegral` and
`ProjValMeasure.integral`) restricted to the countable eigenvalue set of `A`.

Because `A.spectralPVM hA` concentrates on the countable set of eigenvalues, every function
`f : ℝ → ℂ` is measurable on that set and agrees `P_A`-almost everywhere with `f` itself whenever
`f` is measurable (`LinearPMap.eigenCalculus_eq_spectralIntegral`,
`LinearPMap.boundedEigenCalculus_eq_integral`). Algebraic, closedness, adjoint, and norm-bound
laws therefore come directly from `TauCeti.ProjValMeasure.spectralIntegral` and
`TauCeti.ProjValMeasure.integral`.

## Main definitions

* `LinearPMap.eigenCalculus`: the unbounded eigenbasis functional calculus `f(A)`.
* `LinearPMap.boundedEigenCalculus`: the bounded eigenbasis functional calculus `f(A)`.

## Main results

* `LinearPMap.eigenCalculus_eq_spectralIntegral`,
  `LinearPMap.boundedEigenCalculus_eq_integral`: agreement with `spectralPVM` integration for
  measurable symbols.
* `LinearPMap.eigenCalculus_eq_diagonalPMap`, `LinearPMap.eigenCalculus_id`: diagonal
  characterization in any eigenbasis.
* `LinearPMap.boundedEigenCalculus_eq_diagonal`,
  `LinearPMap.isCompactOperator_boundedEigenCalculus`,
  `LinearPMap.boundedEigenCalculus_conj`,
  `LinearPMap.mul_boundedEigenCalculus_of_anticommute`,
  `LinearPMap.commute_boundedEigenCalculus_of_anticommute`.
-/

public section

noncomputable section

open Filter MeasureTheory TauCeti Topology
open scoped ENNReal InnerProductSpace lp

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

section EigenCalculus

variable (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)

private def chosenIndex (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) : Type :=
  (hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent h).choose

private def chosenBasis (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    HilbertBasis (chosenIndex hA h) ℂ H :=
  (hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent h).choose_spec.choose

private def chosenEigval (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    chosenIndex hA h → ℝ :=
  (hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent
    h).choose_spec.choose_spec.choose

private theorem chosenBasis_spec (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)
    (k : chosenIndex hA h) :
    ∃ hk : chosenBasis hA h k ∈ A.domain,
      A ⟨chosenBasis hA h k, hk⟩ = (chosenEigval hA h k : ℂ) • chosenBasis hA h k :=
  (hA.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent
    h).choose_spec.choose_spec.choose_spec k

private theorem countable_chosenIndex (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    Countable (chosenIndex hA h) :=
  h.countable_of_eigenbasis (chosenBasis hA h) (chosenBasis_spec hA h)

private def eigvalRange (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) : Set ℝ :=
  Set.range (chosenEigval hA h)

private theorem countable_eigvalRange (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    (eigvalRange hA h).Countable := by
  have := countable_chosenIndex hA h
  exact Set.countable_range _

private theorem measurableSet_eigvalRange (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    MeasurableSet (eigvalRange hA h) :=
  (countable_eigvalRange hA h).measurableSet

private theorem measurable_indicator_eigvalRange (hA : IsSelfAdjoint A)
    (h : A.HasCompactResolvent) (f : ℝ → ℂ) :
    Measurable ((eigvalRange hA h).indicator f) := by
  have hcount := countable_eigvalRange hA h
  intro U _
  by_cases h0 : (0 : ℂ) ∈ U
  · have hcompl : ((eigvalRange hA h).indicator f ⁻¹' U)ᶜ =
        eigvalRange hA h ∩ {t | f t ∉ U} := by
      ext t
      by_cases ht : t ∈ eigvalRange hA h <;> simp [ht, h0]
    rw [← MeasurableSet.compl_iff, hcompl]
    exact (hcount.mono Set.inter_subset_left).measurableSet
  · have hpre : (eigvalRange hA h).indicator f ⁻¹' U =
        eigvalRange hA h ∩ {t | f t ∈ U} := by
      ext t
      by_cases ht : t ∈ eigvalRange hA h <;> simp [ht, h0]
    rw [hpre]
    exact (hcount.mono Set.inter_subset_left).measurableSet

private theorem mem_eigvalRange_of_apply_eq_smul (hA : IsSelfAdjoint A)
    (h : A.HasCompactResolvent) (x : A.domain) {r : ℝ}
    (hx : A x = (r : ℂ) • (x : H)) (hx0 : (x : H) ≠ 0) :
    r ∈ eigvalRange hA h := by
  by_contra hr
  refine hx0 ((chosenBasis hA h).repr.injective (lp.ext (funext fun k ↦ ?_)))
  rw [(chosenBasis hA h).repr_apply_apply, (chosenBasis hA h).repr.map_zero,
    lp.coeFn_zero, Pi.zero_apply]
  obtain ⟨hk, hAk⟩ := chosenBasis_spec hA h k
  exact hA.isFormalAdjoint.inner_eq_zero_of_apply_eq_smul hAk hx
    (Complex.ofReal_injective.ne fun hkr ↦ hr ⟨k, hkr⟩)

private theorem spectralPVM_diag_eq_smul_dirac (hA : IsSelfAdjoint A) (x : A.domain) {r : ℝ}
    (hx : A x = (r : ℂ) • (x : H)) :
    (A.spectralPVM hA).diag (x : H) = ENNReal.ofReal (‖(x : H)‖ ^ 2) • Measure.dirac r := by
  have : IsFiniteMeasure (ENNReal.ofReal (‖(x : H)‖ ^ 2) • Measure.dirac r) := ⟨by simp⟩
  refine Measure.ext_of_resolventTransform fun z hz ↦ ?_
  have hzA : z ∈ A.resolventSet := hA.mem_resolventSet_of_im_ne_zero hz.ne'
  have hkernel (μ : Measure ℝ) :
      MeasureTheory.resolventTransform μ z = -∫ s : ℝ, (z - s)⁻¹ ∂μ := by
    rw [MeasureTheory.resolventTransform_apply, ← MeasureTheory.integral_neg]
    congr 1 with s
    rw [_root_.resolvent, Ring.inverse_eq_inv', ← inv_neg, neg_sub, Complex.coe_algebraMap]
  rw [hkernel, hkernel, ← hA.inner_resolvent_apply_eq_integral hzA (x : H),
    resolvent_apply_of_apply_eq_smul hzA x hx, inner_smul_right, inner_self_eq_norm_sq_to_K,
    MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul,
    MeasureTheory.integral_dirac _ r, mul_comm]
  simp only [Complex.ofReal_pow]
  rfl

private theorem spectralPVM_integral_apply_of_apply_eq_smul (hA : IsSelfAdjoint A)
    (g : BoundedBorelFunction ℝ) (x : A.domain) {r : ℝ} (hx : A x = (r : ℂ) • (x : H)) :
    (A.spectralPVM hA).integral g (x : H) = g r • (x : H) := by
  have halg : g r • (x : H) =
      ((A.spectralPVM hA).integral (algebraMap ℂ (BoundedBorelFunction ℝ) (g r))) (x : H) := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [← sub_eq_zero, halg, ← _root_.sub_apply, ← _root_.map_sub,
    ProjValMeasure.integral_apply_eq_zero_iff]
  rw [Filter.EventuallyEq, Filter.eventually_iff, MeasureTheory.mem_ae_iff,
    spectralPVM_diag_eq_smul_dirac hA x hx, _root_.smul_apply, smul_eq_mul,
    MeasureTheory.Measure.dirac_apply, Set.indicator_of_notMem (by simp)]
  simp

private theorem spectralPVM_spectralIntegral_apply_of_apply_eq_smul (hA : IsSelfAdjoint A)
    {f : ℝ → ℂ} (hf : Measurable f) (x : A.domain) {r : ℝ} (hx : A x = (r : ℂ) • (x : H)) :
    ∃ hmem : (x : H) ∈ ((A.spectralPVM hA).spectralIntegral f hf).domain,
      (A.spectralPVM hA).spectralIntegral f hf ⟨x, hmem⟩ = f r • (x : H) := by
  have hxdom : (x : H) ∈ ((A.spectralPVM hA).spectralIntegral f hf).domain := by
    rw [ProjValMeasure.mem_spectralIntegral_domain_iff, spectralPVM_diag_eq_smul_dirac hA x hx,
      MeasureTheory.lintegral_smul_measure,
      MeasureTheory.lintegral_dirac' _ (hf.eNorm.pow_const 2)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top eNorm_lt_top)
  refine ⟨hxdom, tendsto_nhds_unique
    ((A.spectralPVM hA).tendsto_integral_truncate_spectralIntegral hf ⟨x, hxdom⟩) ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ‖f r‖] with M hM
  rw [spectralPVM_integral_apply_of_apply_eq_smul hA _ x hx]
  simp [BoundedBorelFunction.truncate_apply, hM]

private theorem spectralPVM_spectralIntegral_eq_diagonalPMap (hA : IsSelfAdjoint A)
    {ι : Type*} (b : HilbertBasis ι ℂ H) {lam : ι → ℝ}
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i)
    {f : ℝ → ℂ} (hf : Measurable f) :
    (A.spectralPVM hA).spectralIntegral f hf = b.diagonalPMap fun i ↦ f (lam i) := by
  set P := A.spectralPVM hA
  refine le_antisymm ?_ ((P.isClosed_spectralIntegral hf).diagonalPMap_le fun i ↦ ?_)
  · refine (b.le_diagonalPMap_iff _).2 fun x i ↦ ?_
    obtain ⟨hi, hAi⟩ := hb i
    have hsf : Measurable (star f) := continuous_star.measurable.comp hf
    obtain ⟨hmem, happly⟩ :=
      spectralPVM_spectralIntegral_apply_of_apply_eq_smul hA hsf ⟨b i, hi⟩ hAi
    have hmem_adj : b i ∈ (P.spectralIntegral f hf)†.domain := by
      rw [P.adjoint_spectralIntegral hf]; exact hmem
    have hadj := (adjoint_isFormalAdjoint (P.dense_spectralIntegral_domain hf))
      ⟨b i, hmem_adj⟩ x
    have hbi : (P.spectralIntegral f hf)† ⟨b i, hmem_adj⟩ = star (f (lam i)) • b i := by
      rw [LinearPMap.congr_fun (P.adjoint_spectralIntegral hf) _ hmem]
      exact happly
    rw [← hadj, hbi, inner_smul_left, starRingEnd_apply, star_star]
  · obtain ⟨hi, hAi⟩ := hb i
    exact spectralPVM_spectralIntegral_apply_of_apply_eq_smul hA hf ⟨b i, hi⟩ hAi

private theorem ae_mem_eigvalRange (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    ∀ᶠ t in (A.spectralPVM hA).ae, t ∈ eigvalRange hA h := by
  set P := A.spectralPVM hA
  have hB := measurableSet_eigvalRange hA h
  have hfix : ∀ k, P.proj (eigvalRange hA h) hB (chosenBasis hA h k) = chosenBasis hA h k := by
    intro k
    rw [P.proj_apply_eq_self_iff]
    obtain ⟨hk, hAk⟩ := chosenBasis_spec hA h k
    rw [spectralPVM_diag_eq_smul_dirac hA ⟨chosenBasis hA h k, hk⟩ hAk, _root_.smul_apply,
      smul_eq_mul, MeasureTheory.Measure.dirac_apply' _ hB.compl,
      Set.indicator_of_notMem (by simp [eigvalRange])]
    simp
  have hproj : P.proj (eigvalRange hA h) hB = 1 :=
    (chosenBasis hA h).ext_inner_apply (chosenBasis hA h) fun i j ↦ by
      rw [hfix j, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
  have hcompl : P.proj (eigvalRange hA h)ᶜ hB.compl = 0 := by
    rw [P.proj_compl (eigvalRange hA h) hB, hproj, ContinuousLinearMap.one_def, sub_self]
  exact show eigvalRange hA h ∈ P.ae from
    by simpa only [compl_compl] using (P.proj_eq_zero_iff_compl_mem_ae _ _).1 hcompl

/-- **Unbounded eigenbasis functional calculus.** For a self-adjoint operator `A` with compact
resolvent and any function `f : ℝ → ℂ`, `A.eigenCalculus hA h f` is the unbounded spectral integral
`(A.spectralPVM hA).spectralIntegral` of `f` restricted to the countable eigenvalue set of `A`.
On any orthonormal eigenbasis it acts diagonally by `f (λᵢ)`
(`LinearPMap.eigenCalculus_eq_diagonalPMap`). -/
def eigenCalculus (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)
    (f : ℝ → ℂ) : H →ₗ.[ℂ] H :=
  (A.spectralPVM hA).spectralIntegral ((eigvalRange hA h).indicator f)
    (measurable_indicator_eigvalRange hA h f)

/-- For a measurable symbol `f : ℝ → ℂ`, `eigenCalculus` agrees with the unbounded spectral
integral against `A.spectralPVM hA`. -/
theorem eigenCalculus_eq_spectralIntegral {f : ℝ → ℂ} (hf : Measurable f) :
    A.eigenCalculus hA h f = (A.spectralPVM hA).spectralIntegral f hf :=
  (A.spectralPVM hA).spectralIntegral_congr_ae _ hf
    ((ae_mem_eigvalRange hA h).mono fun _ ht ↦ Set.indicator_of_mem ht _)

/-- Characterization of `eigenCalculus` in any orthonormal eigenbasis of `A`. -/
theorem eigenCalculus_eq_diagonalPMap {ι : Type*} (b : HilbertBasis ι ℂ H) {lam : ι → ℝ}
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i) (f : ℝ → ℂ) :
    A.eigenCalculus hA h f = b.diagonalPMap fun i ↦ f (lam i) := by
  have hind : (fun k ↦ (eigvalRange hA h).indicator f (chosenEigval hA h k)) =
      fun k ↦ f (chosenEigval hA h k) :=
    funext fun k ↦ Set.indicator_of_mem (Set.mem_range_self k) _
  have hdiag : A.eigenCalculus hA h f =
      (chosenBasis hA h).diagonalPMap fun k ↦ f (chosenEigval hA h k) := by
    rw [eigenCalculus, spectralPVM_spectralIntegral_eq_diagonalPMap hA (chosenBasis hA h)
      (chosenBasis_spec hA h), hind]
  exact hdiag.trans (hA.isFormalAdjoint.diagonalPMap_eq_diagonalPMap (chosenBasis_spec hA h) hb f)

/-- Applying the eigenbasis functional calculus to the identity function recovers `A`. -/
@[simp]
theorem eigenCalculus_id : A.eigenCalculus hA h (fun t ↦ (t : ℂ)) = A := by
  rw [eigenCalculus_eq_diagonalPMap hA h (chosenBasis hA h) (chosenBasis_spec hA h)]
  exact (hA.eq_diagonalPMap (chosenBasis_spec hA h)).symm

/-- On an eigenvector of `A` with real eigenvalue `r`, `f(A)` is defined and acts as scalar
multiplication by `f r`. -/
theorem eigenCalculus_apply_of_apply_eq_smul (f : ℝ → ℂ) (x : A.domain) {r : ℝ}
    (hx : A x = (r : ℂ) • (x : H)) :
    ∃ hmem : (x : H) ∈ (A.eigenCalculus hA h f).domain,
      A.eigenCalculus hA h f ⟨x, hmem⟩ = f r • (x : H) := by
  unfold eigenCalculus
  obtain ⟨hmem, happly⟩ := spectralPVM_spectralIntegral_apply_of_apply_eq_smul hA
    (measurable_indicator_eigvalRange hA h f) x hx
  refine ⟨hmem, ?_⟩
  by_cases hx0 : (x : H) = 0
  · rw [happly]
    simp [hx0]
  · rwa [Set.indicator_of_mem (mem_eigvalRange_of_apply_eq_smul hA h x hx hx0)] at happly

private def boundedIndicatorSymbol (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)
    (f : ℝ → ℂ) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) : BoundedBorelFunction ℝ :=
  BoundedBorelFunction.ofFunction ((eigvalRange hA h).indicator f)
    (measurable_indicator_eigvalRange hA h f)
    ⟨max hf.choose 0, le_max_right _ _, fun t ↦ by
      by_cases ht : t ∈ eigvalRange hA h
      · rw [Set.indicator_of_mem ht]
        exact (hf.choose_spec t).trans (le_max_left _ _)
      · rw [Set.indicator_of_notMem ht, norm_zero]
        exact le_max_right _ _⟩

private def boundedFamily {ι : Type*} (lam : ι → ℝ) (f : ℝ → ℂ) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    ℓ^∞(ι, ℂ) :=
  ⟨fun i ↦ f (lam i), memℓp_infty <| by
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, by rintro _ ⟨i, rfl⟩; exact hC (lam i)⟩⟩

/-- **Bounded eigenbasis functional calculus.** For a self-adjoint operator `A` with compact
resolvent and a bounded function `f : ℝ → ℂ`, `A.boundedEigenCalculus hA h f hf` is the bounded
spectral integral `(A.spectralPVM hA).integral` of `f` restricted to the countable eigenvalue set
of `A`. -/
def boundedEigenCalculus (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent)
    (f : ℝ → ℂ) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) : H →L[ℂ] H :=
  (A.spectralPVM hA).integral (boundedIndicatorSymbol hA h f hf)

/-- For a bounded Borel symbol `g : BoundedBorelFunction ℝ`, `boundedEigenCalculus` coincides with
the bounded spectral integral `(A.spectralPVM hA).integral g`. -/
theorem boundedEigenCalculus_eq_integral (g : BoundedBorelFunction ℝ)
    (hg : ∃ C, ∀ t, ‖g t‖ ≤ C) :
    A.boundedEigenCalculus hA h g hg = (A.spectralPVM hA).integral g :=
  (A.spectralPVM hA).integral_congr_ae ((ae_mem_eigvalRange hA h).mono fun _ ht ↦ by
    simp only [boundedIndicatorSymbol, BoundedBorelFunction.ofFunction_apply]
    exact Set.indicator_of_mem ht _)

/-- On an eigenvector of `A` with real eigenvalue `r`, `boundedEigenCalculus` acts as scalar
multiplication by `f r`. -/
theorem boundedEigenCalculus_apply_of_apply_eq_smul {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (x : A.domain) {r : ℝ} (hx : A x = (r : ℂ) • (x : H)) :
    A.boundedEigenCalculus hA h f hf x = f r • (x : H) := by
  rw [boundedEigenCalculus, spectralPVM_integral_apply_of_apply_eq_smul hA _ x hx]
  by_cases hx0 : (x : H) = 0
  · simp [hx0]
  · simp [boundedIndicatorSymbol, mem_eigvalRange_of_apply_eq_smul hA h x hx hx0]

/-- Characterization of `boundedEigenCalculus` in any orthonormal eigenbasis of `A`. -/
theorem boundedEigenCalculus_eq_diagonal {ι : Type*} (b : HilbertBasis ι ℂ H) {lam : ι → ℝ}
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i)
    (f : ℝ → ℂ) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) (m : ℓ^∞(ι, ℂ)) (hm : ∀ i, m i = f (lam i)) :
    A.boundedEigenCalculus hA h f hf = b.diagonal m := by
  refine b.ext_inner_apply b fun i j ↦ ?_
  obtain ⟨hj, hAj⟩ := hb j
  rw [boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨_, hj⟩ hAj, b.diagonal_apply_self, hm j]

/-- If `f : ℝ → ℂ` vanishes at infinity (`cocompact ℝ`), then `f(A)` is a compact operator. -/
theorem isCompactOperator_boundedEigenCalculus {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C)
    (hlim : Tendsto f (cocompact ℝ) (𝓝 0)) :
    IsCompactOperator (A.boundedEigenCalculus hA h f hf) := by
  rw [boundedEigenCalculus_eq_diagonal hA h (chosenBasis hA h) (chosenBasis_spec hA h) f hf
      (boundedFamily (chosenEigval hA h) f hf) (fun _ ↦ rfl),
    HilbertBasis.isCompactOperator_diagonal_iff]
  have hN := h.northcott_abs_of_eigenbasis (chosenBasis hA h) (chosenBasis_spec hA h)
  have hlim_eig : Tendsto (chosenEigval hA h) cofinite (cocompact ℝ) := by
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
    simpa only [Real.norm_eq_abs] using (northcott_iff_tendsto _).1 hN
  exact hlim.comp hlim_eig

/-- The bounded functional calculus applied to `t ↦ (1 + t²)⁻¹` equals `A.invOneAddSq`. -/
theorem boundedEigenCalculus_invOneAddSq
    (hf : ∃ C, ∀ t : ℝ, ‖(((1 + t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ C) :
    A.boundedEigenCalculus hA h (fun t ↦ (((1 + t ^ 2)⁻¹ : ℝ) : ℂ)) hf = A.invOneAddSq := by
  refine (chosenBasis hA h).ext_inner_apply (chosenBasis hA h) fun i j ↦ ?_
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  rw [boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨_, hj⟩ hAj,
    invOneAddSq_apply_of_apply_eq_smul hA.I_mem_resolventSet hA.neg_I_mem_resolventSet ⟨_, hj⟩ hAj]
  norm_cast

/-- Unitary conjugation commutes with the bounded eigenbasis functional calculus. -/
theorem boundedEigenCalculus_conj {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] (U : H ≃ₗᵢ[ℂ] H') (f : ℝ → ℂ)
    (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    (A.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H')).boundedEigenCalculus (hA.conj U)
      ((hasCompactResolvent_conj_iff (U : H ≃L[ℂ] H')).2 h) f hf =
      U.conjStarAlgEquiv (A.boundedEigenCalculus hA h f hf) := by
  set b := chosenBasis hA h
  set lam := chosenEigval hA h
  have hb' : ∀ k, ∃ hk : b.mapₗᵢ U k ∈ (A.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H')).domain,
      A.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H') ⟨b.mapₗᵢ U k, hk⟩ =
        (lam k : ℂ) • b.mapₗᵢ U k := fun k ↦ by
    obtain ⟨hk, hAk⟩ := chosenBasis_spec hA h k
    have hmem' := LinearPMap.map_mem_conj_domain (e := ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H')) ⟨b k, hk⟩
    have hmem : b.mapₗᵢ U k ∈ (A.conj ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H')).domain := by
      simpa only [HilbertBasis.mapₗᵢ_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hmem'
    refine ⟨hmem, ?_⟩
    have happ := LinearPMap.conj_apply_map (e := ((U : H ≃L[ℂ] H') : H ≃ₗ[ℂ] H')) ⟨b k, hk⟩
      (h := hmem')
    simp only [ContinuousLinearEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, ← b.mapₗᵢ_apply U k] at happ
    exact happ.trans (by rw [hAk, _root_.map_smul, b.mapₗᵢ_apply U k])
  refine (b.mapₗᵢ U).ext_inner_apply (b.mapₗᵢ U) fun i j ↦ ?_
  obtain ⟨hj', hAj'⟩ := hb' j
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  rw [boundedEigenCalculus_apply_of_apply_eq_smul _ _ hf ⟨_, hj'⟩ hAj',
    LinearIsometryEquiv.conjStarAlgEquiv_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, HilbertBasis.mapₗᵢ_apply]
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    HilbertBasis.mapₗᵢ_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨b j, hj⟩ hAj, _root_.map_smul]

/-- **Anticommutation with odd functions.** If a bounded operator `γ` preserves the domain of `A`
and anticommutes with `A` on `D(A)`, then `γ` anticommutes with `f(A)` for every bounded odd
function `f`. -/
theorem mul_boundedEigenCalculus_of_anticommute {γ : H →L[ℂ] H}
    (hγdom : ∀ x ∈ A.domain, γ x ∈ A.domain)
    (hγA : ∀ x : A.domain, γ (A x) = -A ⟨γ x, hγdom x x.property⟩)
    {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) (hodd : ∀ t, f (-t) = -f t) :
    γ * A.boundedEigenCalculus hA h f hf = -(A.boundedEigenCalculus hA h f hf * γ) := by
  refine (chosenBasis hA h).ext_inner_apply (chosenBasis hA h) fun i j ↦ ?_
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  have hγeig := apply_eq_neg_smul_of_anticommute hγdom hγA ⟨_, hj⟩ hAj
  rw [← Complex.ofReal_neg] at hγeig
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, _root_.neg_apply]
  rw [boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨_, hj⟩ hAj,
    boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨_, hγdom _ hj⟩ hγeig,
    hodd, _root_.map_smul, _root_.neg_smul, neg_neg]

/-- **Commutation with even functions.** If a bounded operator `γ` preserves the domain of `A` and
anticommutes with `A` on `D(A)`, then `γ` commutes with `f(A)` for every bounded even function
`f`. -/
theorem commute_boundedEigenCalculus_of_anticommute {γ : H →L[ℂ] H}
    (hγdom : ∀ x ∈ A.domain, γ x ∈ A.domain)
    (hγA : ∀ x : A.domain, γ (A x) = -A ⟨γ x, hγdom x x.property⟩)
    {f : ℝ → ℂ} (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) (heven : ∀ t, f (-t) = f t) :
    Commute γ (A.boundedEigenCalculus hA h f hf) := by
  refine (chosenBasis hA h).ext_inner_apply (chosenBasis hA h) fun i j ↦ ?_
  obtain ⟨hj, hAj⟩ := chosenBasis_spec hA h j
  have hγeig := apply_eq_neg_smul_of_anticommute hγdom hγA ⟨_, hj⟩ hAj
  rw [← Complex.ofReal_neg] at hγeig
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  rw [boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨_, hj⟩ hAj,
    boundedEigenCalculus_apply_of_apply_eq_smul hA h hf ⟨_, hγdom _ hj⟩ hγeig,
    heven, _root_.map_smul]

end EigenCalculus

end LinearPMap
