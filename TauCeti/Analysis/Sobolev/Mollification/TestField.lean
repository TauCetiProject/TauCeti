/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.Topology.MetricSpace.Thickening

/-!
# Approximating Sobolev test fields by test functions

Let `ψ` be a compactly supported field on an open set `Ω` of a finite-dimensional space, with a
weak derivative `Dψ ∈ Lˢ(Ω)`. Mollifying `ψ` by normalized bumps of shrinking radius gives test
functions `φ n` on `Ω`, supported in a fixed compact neighbourhood `K' ⊆ Ω` of the support of `ψ`,
whose derivatives on `K'` are the mollifications of `Dψ`
(`TauCeti.HasWeakFDerivOn.exists_seq_testFunction_convolution_normed`). Pairings of these
derivatives with a fixed field in the conjugate exponent converge to the pairings with `Dψ`
(`TauCeti.tendsto_integral_inner_fderiv_mollify`). This is how an identity tested against smooth
test functions extends to Sobolev test fields such as `ψ`.

As an application, the symmetry `∫ ⟪∂_v φ, Dξ w⟫ = ∫ ⟪∂_w φ, Dξ v⟫` of the weak derivative of
a field `ξ`, tested against test functions `φ`
(`TauCeti.HasWeakLineDerivOn.integral_inner_lineDeriv_comm`), extends to such `ψ`
(`TauCeti.HasWeakFDerivOn.setIntegral_inner_apply_comm`).

## Main results

* `TauCeti.HasWeakFDerivOn.exists_seq_testFunction_convolution_normed`: the mollifications of a
  compactly supported Sobolev field, as test functions on `Ω`.
* `TauCeti.tendsto_integral_inner_fderiv_mollify`: pairings of their derivatives converge.
* `TauCeti.HasWeakFDerivOn.ae_apply_eq_zero_of_notMem_tsupport`: a weak derivative vanishes
  almost everywhere off the support of the field.
* `TauCeti.HasWeakFDerivOn.setIntegral_inner_apply_comm`: mixed weak derivatives of a
  `W^{1,q}_loc` field commute when tested against a compactly supported Sobolev field.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.3.1.
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Metric Filter
open scoped InnerProductSpace ContDiff Convolution ENNReal Distributions Topology

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [HasContDiffBump E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Ω : Opens E} {s : ℝ≥0∞}
  {ψ : E → V} {Dψ : E → E →L[ℝ] V}

/-- **Mollifying a compactly supported Sobolev field.** Let `ψ ∈ Lᵖ` be supported in a compact
subset of `Ω`, with a weak derivative `Dψ ∈ Lˢ(Ω)`, `1 ≤ p, s`. Then there are a compact
measurable neighbourhood `K' ⊆ Ω` of the support of `ψ`, normalized bumps `ρ n` with radii tending
to zero, and test functions `φ n = ρ n ⋆ ψ` on `Ω`, supported in `K'`, whose derivatives on `K'`
are the mollifications `ρ n ⋆ Dψ` of the zero extension of `Dψ`. -/
theorem HasWeakFDerivOn.exists_seq_testFunction_convolution_normed
    (hψ : HasWeakFDerivOn μ Ω ψ Dψ) (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω)
    {p : ℝ≥0∞} (hψp : MemLp ψ p μ) (hp : 1 ≤ p) (hDψ : MemLp Dψ s (μ.restrict Ω)) (hs : 1 ≤ s) :
    ∃ K' : Set E, IsCompact K' ∧ MeasurableSet K' ∧ K' ⊆ Ω ∧ tsupport ψ ⊆ K' ∧
      ∃ (ρ : ℕ → ContDiffBump (0 : E)) (φ : ℕ → 𝓓(Ω, V)),
        Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) ∧
        (∀ n, ⇑(φ n) = (ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] ψ) ∧
        (∀ n, tsupport (φ n : E → V) ⊆ K') ∧
        ∀ n, ∀ z ∈ K', fderiv ℝ (φ n : E → V) z =
          ((ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (Ω : Set E).indicator Dψ) z := by
  obtain ⟨δ, hδ, hball⟩ := hψc.isCompact.exists_forall_closedBall_subset_of_isOpen Ω.isOpen hψΩ
  choose φ hφ hφs hderiv using fun n => hψ.exists_testFunction_convolution_normed hψc hψp hDψ
    hp hs hball (ContDiffBump.shrinking hδ n) (ContDiffBump.rOut_shrinking_le hδ n)
  exact ⟨_, hψc.isCompact.cthickening, isClosed_cthickening.measurableSet,
    fun z hz => hball z hz (mem_closedBall_self hδ.le), self_subset_cthickening _,
    _, φ, ContDiffBump.tendsto_rOut_shrinking hδ, hφ, hφs, hderiv⟩

/-- **Pairings of mollified derivatives converge.** Let `φ n` be test functions on `Ω` supported in
a measurable set `K' ⊆ Ω`, whose derivatives on `K'` are the mollifications of the zero extension
of a field `Dψ ∈ Lˢ(Ω)` by normalized bumps `ρ n` with radii tending to zero. Then for every
direction `c` and every field `a` in the conjugate exponent on `K'`,
`∫ ⟪∂_c φ n, a⟫ → ∫_{K'} ⟪Dψ c, a⟫`. -/
theorem tendsto_integral_inner_fderiv_mollify [CompleteSpace V] {K' : Set E}
    (hK'm : MeasurableSet K') (hK'Ω : K' ⊆ Ω) [Fact (1 ≤ s)] {ρ : ℕ → ContDiffBump (0 : E)}
    (hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0)) {φ : ℕ → 𝓓(Ω, V)}
    (hφs : ∀ n, tsupport (φ n : E → V) ⊆ K')
    (hderiv : ∀ n, ∀ z ∈ K', fderiv ℝ (φ n : E → V) z =
      ((ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (Ω : Set E).indicator Dψ) z)
    (hDψ : MemLp Dψ s (μ.restrict Ω)) (c : E) {a : E → V}
    (ha : MemLp a s.conjExponent (μ.restrict K')) :
    Tendsto (fun n => ∫ z, ⟪fderiv ℝ (φ n : E → V) z c, a z⟫_ℝ ∂μ) atTop
      (𝓝 (∫ z in K', ⟪Dψ z c, a z⟫_ℝ ∂μ)) := by
  let B : V →L[ℝ] (E →L[ℝ] V) →L[ℝ] ℝ := (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).bilinearComp
    (ContinuousLinearMap.id ℝ V) (ContinuousLinearMap.apply ℝ V c)
  have hB : ∀ w M, B w M = ⟪w, M c⟫_ℝ := fun w M => by simp [B]
  have := B.tendsto_integral_bilin_normed_convolution hρ
    ((memLp_indicator_iff_restrict hK'm.nullMeasurableSet).2 ha)
    ((memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).2 hDψ)
  convert this using 1
  · funext n
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    by_cases hz : z ∈ K'
    · rw [indicator_of_mem hz, hB, hderiv n z hz, real_inner_comm]
    · rw [indicator_of_notMem hz, map_zero, zero_apply,
        fderiv_of_notMem_tsupport ℝ fun h' => hz (hφs n h'), zero_apply,
        inner_zero_left]
  · rw [← integral_indicator hK'm]
    congr 1
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    by_cases hz : z ∈ K'
    · rw [indicator_of_mem hz, indicator_of_mem hz, indicator_of_mem (hK'Ω hz), hB,
        real_inner_comm]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz, map_zero,
        zero_apply]

omit [HasContDiffBump E] [μ.IsAddHaarMeasure] in
/-- **A weak derivative vanishes off the support.** If `Dψ` is a weak derivative of `ψ` on `Ω`,
then for every direction `c`, `Dψ z c = 0` for almost every `z ∈ Ω` outside the support of `ψ`. -/
theorem HasWeakFDerivOn.ae_apply_eq_zero_of_notMem_tsupport (hψ : HasWeakFDerivOn μ Ω ψ Dψ)
    (c : E) : ∀ᵐ z ∂μ.restrict Ω, z ∉ tsupport ψ → Dψ z c = 0 :=
  (hψ.hasWeakLineDerivOn c).ae_eq_zero_of_isOpen (isClosed_tsupport ψ).isOpen_compl
    (.of_forall fun _ hz => image_eq_zero_of_notMem_tsupport hz)

/-- **Mixed weak derivatives commute against Sobolev test fields.** Let `ξ` have a weak derivative
`Dξ` on `Ω` that is `L^q` on compact subsets of `Ω`. Let `ψ` be compactly supported in `Ω`, with a
weak derivative `Dψ ∈ Lˢ(Ω)`, where `1/s + 1/q ≤ 1`. Then for all directions `v` and `w`,

`∫_Ω ⟪Dψ v, Dξ w⟫ = ∫_Ω ⟪Dψ w, Dξ v⟫`.

For a test function `ψ` both sides are `-∫ ⟪∂_w ∂_v ψ, ξ⟫`; no second derivative of `ξ` or `ψ`
is assumed to exist. -/
theorem HasWeakFDerivOn.setIntegral_inner_apply_comm [FiniteDimensional ℝ V] {q : ℝ≥0∞}
    {ξ : E → V} {Dξ : E → E →L[ℝ] V} (hξ : HasWeakFDerivOn μ Ω ξ Dξ)
    (hDξ : ∀ K, IsCompact K → K ⊆ Ω → MemLp Dξ q (μ.restrict K))
    (hψ : HasWeakFDerivOn μ Ω ψ Dψ) (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω)
    (hDψ : MemLp Dψ s (μ.restrict Ω)) (hsq : s⁻¹ + q⁻¹ ≤ 1) (v w : E) :
    ∫ z in Ω, ⟪Dψ z v, Dξ z w⟫_ℝ ∂μ = ∫ z in Ω, ⟪Dψ z w, Dξ z v⟫_ℝ ∂μ := by
  have hs1 : 1 ≤ s := ENNReal.inv_le_one.1 (le_self_add.trans hsq)
  have : Fact (1 ≤ s) := ⟨hs1⟩
  -- `ψ` is integrable, being locally integrable on `Ω` and supported in a compact subset of `Ω`.
  have hψ1 : MemLp ψ 1 μ := memLp_one_iff_integrable.2 <|
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport ψ)).1
      (hψ.locallyIntegrableOn.integrableOn_compact_subset hψΩ hψc.isCompact)
  obtain ⟨K', hK'c, hK'm, hK'Ω, hψK', ρ, φ, hρ, -, hφs, hderiv⟩ :=
    hψ.exists_seq_testFunction_convolution_normed hψc hψΩ hψ1 le_rfl hDψ hs1
  have : IsFiniteMeasure (μ.restrict K') := isFiniteMeasure_restrict.2 hK'c.measure_lt_top.ne
  have hDξK (c : E) : MemLp (fun z => Dξ z c) s.conjExponent (μ.restrict K') :=
    ((hDξ K' hK'c hK'Ω).continuousLinearMap_comp (ContinuousLinearMap.apply ℝ V c)).mono_exponent
      (ENNReal.conjExponent_le_of_inv_add_inv_le_one hsq)
  -- Pass to the limit in the symmetry for the mollifications of `ψ`.
  have hK' : ∫ z in K', ⟪Dψ z v, Dξ z w⟫_ℝ ∂μ = ∫ z in K', ⟪Dψ z w, Dξ z v⟫_ℝ ∂μ :=
    tendsto_nhds_unique (tendsto_integral_inner_fderiv_mollify hK'm hK'Ω hρ hφs hderiv hDψ v
      (hDξK w)) ((tendsto_integral_inner_fderiv_mollify hK'm hK'Ω hρ hφs hderiv hDψ w
        (hDξK v)).congr fun n => by
          simpa only [TestFunction.lineDeriv_eq_fderiv] using
            (hξ.hasWeakLineDerivOn v).integral_inner_lineDeriv_comm (hξ.hasWeakLineDerivOn w)
              (φ n))
  -- Both integrands vanish almost everywhere on `Ω` off `K'`.
  have hDψ0 (c d : E) : ∀ᵐ z ∂μ, z ∈ (Ω : Set E) \ K' → ⟪Dψ z c, Dξ z d⟫_ℝ = 0 := by
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1
      (hψ.ae_apply_eq_zero_of_notMem_tsupport c)] with z hz hzΩ
    simp [hz hzΩ.1 fun h' => hzΩ.2 (hψK' h')]
  have hΩm : NullMeasurableSet (Ω : Set E) μ := Ω.isOpen.measurableSet.nullMeasurableSet
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hΩm hK'Ω (hDψ0 v w),
    setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hΩm hK'Ω (hDψ0 w v), hK']

end TauCeti
