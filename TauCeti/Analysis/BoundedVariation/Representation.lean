/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.LebesgueDecomposition
public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Topology.Sets.Opens

/-!
# Identifying variation measures and outer normals from Gauss–Green identities

Let `Ω` be an open subset of a finite-dimensional real inner product space `E` and `u : E → ℝ` be
locally integrable on `Ω` with respect to `μ`. Suppose the distributional gradient of `u` is
represented against a locally finite Borel measure `ν` on `Ω` by a locally `ν`-integrable vector
field `g : Ω → E`:

`∫ x, div φ x * u x ∂μ = -∫ x, ⟪φ x, g x⟫ ∂ν` for all `φ ∈ 𝓓(Ω, E)`.

This file shows that `u` then has locally finite variation on `Ω`, identifies its variation
measure as `|Du| = ν.withDensity (‖g ·‖ₑ)` and its relative total variation on every open
`U ⊆ Ω` as `∫⁻_{(↑) ⁻¹' U} ‖g‖ₑ ∂ν`, and identifies its polar density via
`‖g x‖ • polarDensity μ Ω u x = g x` for `ν`-almost every `x`.

When `‖σ‖ = 1` `ν`-almost everywhere, this yields `|Du| = ν`,
`totalVariationOn μ U u = ν ((↑) ⁻¹' U)`, and `polarDensity μ Ω u =ᵐ[ν] σ`, without requiring
continuity of `σ`. Specializing to the indicator of a locally `μ`-null-measurable set `s` whose
distributional Gauss–Green formula holds against `ν` with a `ν`-almost everywhere unit vector field
`n` identifies the perimeter measure with `ν`, the relative perimeter `P(s; U)` with
`ν ((↑) ⁻¹' U)`, and shows that `ν`-almost every point lies in the reduced boundary `∂*s` with
measure-theoretic outer normal `TauCeti.outerNormal μ Ω s = n`.

## Main results

* `TauCeti.variationMeasure_eq_withDensity_of_forall_integral_divergenceCLM_mul_eq`,
  `TauCeti.totalVariationOn_eq_setLIntegral_of_forall_integral_divergenceCLM_mul_eq`, and
  `TauCeti.ae_norm_smul_polarDensity_eq_of_forall_integral_divergenceCLM_mul_eq`: variation
  measure, relative total variation, and polar density from a locally `ν`-integrable representing
  vector field `g`.
* `TauCeti.variationMeasure_eq_of_forall_integral_divergenceCLM_mul_eq`,
  `TauCeti.totalVariationOn_eq_of_forall_integral_divergenceCLM_mul_eq`, and
  `TauCeti.ae_polarDensity_eq_of_forall_integral_divergenceCLM_mul_eq`: the specialization when
  `‖σ x‖ = 1` `ν`-almost everywhere.
* `TauCeti.variationMeasure_indicator_eq_of_forall_setIntegral_divergenceCLM_eq`,
  `TauCeti.perimeter_eq_of_forall_setIntegral_divergenceCLM_eq`,
  `TauCeti.ae_mem_reducedBoundary_of_forall_setIntegral_divergenceCLM_eq`, and
  `TauCeti.ae_outerNormal_eq_of_forall_setIntegral_divergenceCLM_eq`:
  perimeter measure, relative perimeter, reduced boundary, and outer normal of a set from a
  distributional Gauss–Green identity with a unit normal field.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Proposition 12.1 and Remark 15.2.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Oxford University Press, 2000, §3.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace TestFunction Set Filter
open scoped ENNReal Distributions RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω U : Opens E} {u : E → ℝ}

/-- If `Du` is represented against a measure `ν` on `Ω` by a vector field `g`, then the total
variation of `u` on any open subset `U ⊆ Ω` is bounded by `∫⁻_{(↑) ⁻¹' U} ‖g‖ₑ ∂ν`. -/
theorem totalVariationOn_le_setLIntegral_of_forall_integral_divergenceCLM_mul_eq
    {ν : Measure Ω} {g : Ω → E}
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ = -∫ x, ⟪φ x, g x⟫ ∂ν)
    (hU : U ≤ Ω) :
    totalVariationOn μ U u ≤ ∫⁻ x in ((↑) : Ω → E) ⁻¹' (U : Set E), ‖g x‖ₑ ∂ν := by
  set V : Set Ω := ((↑) : Ω → E) ⁻¹' (U : Set E)
  have hVm : MeasurableSet V := U.isOpen.measurableSet.preimage measurable_subtypeVal
  rw [totalVariationOn_le_iff]
  intro φ hφ
  let φΩ : 𝓓(Ω, E) := ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hU⟩
  have hdivφ (x : E) : divergenceCLM φ x = divergenceCLM φΩ x := by simp [φΩ]
  simp_rw [hdivφ, hdiv φΩ]
  refine (ENNReal.ofReal_le_ofReal (neg_le_abs _)).trans ?_
  rw [← Real.eNorm_eq_ofReal_abs, ← withDensity_apply _ hVm]
  exact TestFunction.enorm_integral_inner_le_withDensity (φ := φΩ) U.isOpen.measurableSet
    φ.tsupport_subset hφ ν g

/-- A locally `ν`-integrable vector field representing `Du` against `ν` forces `u` to have locally
finite variation on `Ω`. -/
theorem forall_isCompact_exists_totalVariationOn_ne_top_of_forall_integral_divergenceCLM_mul_eq
    {ν : Measure Ω} {g : Ω → E} (hg : LocallyIntegrable g ν)
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ = -∫ x, ⟪φ x, g x⟫ ∂ν) :
    ∀ K, IsCompact K → K ⊆ Ω → ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V u ≠ ∞ := by
  intro K hK hKΩ
  obtain ⟨L, hL, hKL, hLΩ⟩ := exists_compact_between hK Ω.isOpen hKΩ
  let V : Opens E := ⟨interior L, isOpen_interior⟩
  have hVΩ : V ≤ Ω := interior_subset.trans hLΩ
  have hL' : IsCompact (((↑) : Ω → E) ⁻¹' L) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hL (by simpa using hLΩ)
  have hfinL : ∫⁻ x in ((↑) : Ω → E) ⁻¹' L, ‖g x‖ₑ ∂ν < ∞ :=
    hasFiniteIntegral_iff_eNorm.1 (hg.integrableOn_isCompact hL').2
  refine ⟨V, hKL, ne_top_of_le_ne_top hfinL.ne ?_⟩
  exact (totalVariationOn_le_setLIntegral_of_forall_integral_divergenceCLM_mul_eq hdiv hVΩ).trans
    (lintegral_mono_set (preimage_mono interior_subset))

/-- A locally `ν`-integrable vector field `g` representing `Du` against a locally finite measure `ν`
agrees `ν`-almost everywhere with `acDerivativeDensity μ Ω u ν`. -/
private theorem ae_eq_acDerivativeDensity_of_forall_integral_divergenceCLM_mul_eq
    (hu : LocallyIntegrableOn u Ω μ) {ν : Measure Ω} [IsFiniteMeasureOnCompacts ν]
    {g : Ω → E} (hg : LocallyIntegrable g ν)
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ = -∫ x, ⟪φ x, g x⟫ ∂ν) :
    g =ᵐ[ν] acDerivativeDensity μ Ω u ν := by
  have := Ω.isOpen.locallyCompactSpace
  have hfin :=
    forall_isCompact_exists_totalVariationOn_ne_top_of_forall_integral_divergenceCLM_mul_eq hg hdiv
  refine ae_eq_acDerivativeDensity hu hfin ν hg locallyIntegrable_zero
    Measure.MutuallySingular.zero_left fun φ => ?_
  simpa using hdiv φ

/-- **Variation measure of a measure-represented distributional gradient.** If `u` is locally
integrable on `Ω` and `Du` is represented against a locally finite measure `ν` on `Ω` by a locally
`ν`-integrable vector field `g`, then `|Du| = ν.withDensity (‖g ·‖ₑ)`. -/
theorem variationMeasure_eq_withDensity_of_forall_integral_divergenceCLM_mul_eq
    (hu : LocallyIntegrableOn u Ω μ) {ν : Measure Ω} [IsFiniteMeasureOnCompacts ν]
    {g : Ω → E} (hg : LocallyIntegrable g ν)
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ = -∫ x, ⟪φ x, g x⟫ ∂ν) :
    variationMeasure μ Ω u = ν.withDensity fun x => ‖g x‖ₑ := by
  have := Ω.isOpen.locallyCompactSpace
  have hfin :=
    forall_isCompact_exists_totalVariationOn_ne_top_of_forall_integral_divergenceCLM_mul_eq hg hdiv
  let ρ : Measure Ω := ν.withDensity fun x => ‖g x‖ₑ
  have : IsFiniteMeasureOnCompacts ρ := ⟨fun K hK => by
    rw [withDensity_apply _ hK.measurableSet]
    exact hasFiniteIntegral_iff_eNorm.1 (hg.integrableOn_isCompact hK).2⟩
  have hle : variationMeasure μ Ω u ≤ ρ := Measure.le_iff.2 fun s _ => by
    rw [s.measure_eq_iInf_isOpen, s.measure_eq_iInf_isOpen]
    refine iInf₂_mono fun W _ => iInf_mono fun hW => ?_
    obtain ⟨V, hV, rfl⟩ := Ω.exists_le_preimage_coe_eq hW
    rw [withDensity_apply _ hW.measurableSet]
    exact (variationMeasure_preimage_coe hu hfin hV).trans_le
      (totalVariationOn_le_setLIntegral_of_forall_integral_divergenceCLM_mul_eq hdiv hV)
  have hac : variationMeasure μ Ω u ≪ ν :=
    (Measure.absolutelyContinuous_of_le hle).trans (withDensity_absolutelyContinuous _ _)
  have hsing : (variationMeasure μ Ω u).singularPart ν = 0 :=
    Measure.singularPart_eq_zero_of_ac hac
  have hg_eq := ae_eq_acDerivativeDensity_of_forall_integral_divergenceCLM_mul_eq hu hg hdiv
  rw [← withDensity_enorm_acDerivativeDensity_add_singularPart hu hfin ν, hsing, add_zero]
  exact withDensity_congr_ae (hg_eq.symm.fun_comp (‖·‖ₑ))

/-- **Total variation of a measure-represented distributional gradient.** Under the hypotheses of
`TauCeti.variationMeasure_eq_withDensity_of_forall_integral_divergenceCLM_mul_eq`, the total
variation of `u` on every open `U ⊆ Ω` equals `∫⁻ x in (↑) ⁻¹' U, ‖g x‖ₑ ∂ν`. -/
theorem totalVariationOn_eq_setLIntegral_of_forall_integral_divergenceCLM_mul_eq
    (hu : LocallyIntegrableOn u Ω μ) {ν : Measure Ω} [IsFiniteMeasureOnCompacts ν]
    {g : Ω → E} (hg : LocallyIntegrable g ν)
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ = -∫ x, ⟪φ x, g x⟫ ∂ν)
    (hU : U ≤ Ω) :
    totalVariationOn μ U u = ∫⁻ x in ((↑) : Ω → E) ⁻¹' (U : Set E), ‖g x‖ₑ ∂ν := by
  have hfin :=
    forall_isCompact_exists_totalVariationOn_ne_top_of_forall_integral_divergenceCLM_mul_eq hg hdiv
  rw [← variationMeasure_preimage_coe hu hfin hU,
    variationMeasure_eq_withDensity_of_forall_integral_divergenceCLM_mul_eq hu hg hdiv,
    withDensity_apply _ (U.isOpen.measurableSet.preimage measurable_subtypeVal)]

/-- **Polar density of a measure-represented distributional gradient.** If `u` is locally
integrable on `Ω` and `Du` is represented against a locally finite measure `ν` on `Ω` by a locally
`ν`-integrable vector field `g`, then `‖g x‖ • polarDensity μ Ω u x = g x` for `ν`-a.e. `x`. -/
theorem ae_norm_smul_polarDensity_eq_of_forall_integral_divergenceCLM_mul_eq
    (hu : LocallyIntegrableOn u Ω μ) {ν : Measure Ω} [IsFiniteMeasureOnCompacts ν]
    {g : Ω → E} (hg : LocallyIntegrable g ν)
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ = -∫ x, ⟪φ x, g x⟫ ∂ν) :
    ∀ᵐ x ∂ν, ‖g x‖ • polarDensity μ Ω u x = g x := by
  have := Ω.isOpen.locallyCompactSpace
  have hfin :=
    forall_isCompact_exists_totalVariationOn_ne_top_of_forall_integral_divergenceCLM_mul_eq hg hdiv
  filter_upwards [ae_eq_acDerivativeDensity_of_forall_integral_divergenceCLM_mul_eq hu hg hdiv,
    ae_enorm_acDerivativeDensity_eq_rnDeriv hu hfin ν] with x hx hrn
  have hnorm : ((variationMeasure μ Ω u).rnDeriv ν x).toReal = ‖g x‖ := by
    rw [← hrn, ← hx, ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
  rw [← hnorm, ← acDerivativeDensity_def, hx]

/-- **Variation measure from a unit-norm representation.** If `Du` is represented against a locally
finite measure `ν` on `Ω` by a `ν`-a.e. strongly measurable vector field `σ` of unit norm `ν`-a.e.,
then `variationMeasure μ Ω u = ν`. -/
theorem variationMeasure_eq_of_forall_integral_divergenceCLM_mul_eq
    (hu : LocallyIntegrableOn u Ω μ) {ν : Measure Ω} [IsFiniteMeasureOnCompacts ν]
    {σ : Ω → E} (hσm : AEStronglyMeasurable σ ν) (hσ1 : ∀ᵐ x ∂ν, ‖σ x‖ = 1)
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ = -∫ x, ⟪φ x, σ x⟫ ∂ν) :
    variationMeasure μ Ω u = ν := by
  have := Ω.isOpen.locallyCompactSpace
  have hσloc : LocallyIntegrable σ ν :=
    (memLp_top_of_bound hσm 1 (hσ1.mono fun _ h => h.le)).locallyIntegrable le_top
  rw [variationMeasure_eq_withDensity_of_forall_integral_divergenceCLM_mul_eq hu hσloc hdiv]
  refine (withDensity_congr_ae ?_).trans withDensity_one
  filter_upwards [hσ1] with x hx
  simp [← ofReal_norm, hx]

/-- **Total variation from a unit-norm representation.** Under the hypotheses of
`TauCeti.variationMeasure_eq_of_forall_integral_divergenceCLM_mul_eq`, the total variation of `u` on
every open `U ⊆ Ω` is `ν ((↑) ⁻¹' U)`. -/
theorem totalVariationOn_eq_of_forall_integral_divergenceCLM_mul_eq
    (hu : LocallyIntegrableOn u Ω μ) {ν : Measure Ω} [IsFiniteMeasureOnCompacts ν]
    {σ : Ω → E} (hσm : AEStronglyMeasurable σ ν) (hσ1 : ∀ᵐ x ∂ν, ‖σ x‖ = 1)
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ = -∫ x, ⟪φ x, σ x⟫ ∂ν)
    (hU : U ≤ Ω) :
    totalVariationOn μ U u = ν (((↑) : Ω → E) ⁻¹' (U : Set E)) := by
  have := Ω.isOpen.locallyCompactSpace
  have hσloc : LocallyIntegrable σ ν :=
    (memLp_top_of_bound hσm 1 (hσ1.mono fun _ h => h.le)).locallyIntegrable le_top
  rw [totalVariationOn_eq_setLIntegral_of_forall_integral_divergenceCLM_mul_eq hu hσloc hdiv hU]
  have hae : (fun x => ‖σ x‖ₑ) =ᵐ[ν.restrict (((↑) : Ω → E) ⁻¹' (U : Set E))] fun _ => 1 :=
    ae_restrict_of_ae (hσ1.mono fun _ hx => by simp [← ofReal_norm, hx])
  rw [lintegral_congr_ae hae, lintegral_one, Measure.restrict_apply_univ]

/-- **Polar density from a unit-norm representation.** Under the hypotheses of
`TauCeti.variationMeasure_eq_of_forall_integral_divergenceCLM_mul_eq`, `polarDensity μ Ω u =ᵐ[ν] σ`.
-/
theorem ae_polarDensity_eq_of_forall_integral_divergenceCLM_mul_eq
    (hu : LocallyIntegrableOn u Ω μ) {ν : Measure Ω} [IsFiniteMeasureOnCompacts ν]
    {σ : Ω → E} (hσm : AEStronglyMeasurable σ ν) (hσ1 : ∀ᵐ x ∂ν, ‖σ x‖ = 1)
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x, divergenceCLM φ x * u x ∂μ = -∫ x, ⟪φ x, σ x⟫ ∂ν) :
    polarDensity μ Ω u =ᵐ[ν] σ := by
  have := Ω.isOpen.locallyCompactSpace
  have hσloc : LocallyIntegrable σ ν :=
    (memLp_top_of_bound hσm 1 (hσ1.mono fun _ h => h.le)).locallyIntegrable le_top
  filter_upwards [ae_norm_smul_polarDensity_eq_of_forall_integral_divergenceCLM_mul_eq hu
    hσloc hdiv, hσ1] with x hx h1
  simpa [h1] using hx

/-- Rewriting a set Gauss–Green identity `∫_s div φ ∂μ = ∫ ⟪φ, n⟫ ∂ν` into the distributional
gradient form `∫ div φ * s.indicator 1 ∂μ = -∫ ⟪φ, -n⟫ ∂ν`. -/
private theorem integral_divergenceCLM_mul_indicator_eq_neg_integral
    {s : Set E} (hs : NullMeasurableSet s (μ.restrict Ω)) {ν : Measure Ω} {n : Ω → E}
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x in s, divergenceCLM φ x ∂μ = ∫ x, ⟪φ x, n x⟫ ∂ν)
    (φ : 𝓓(Ω, E)) :
    ∫ x, divergenceCLM φ x * s.indicator 1 x ∂μ = -∫ x, ⟪φ x, (-n) x⟫ ∂ν := by
  have hsupp : Function.support (divergenceCLM φ) ⊆ Ω :=
    (subset_tsupport _).trans ((divergenceCLM φ).tsupport_subset.trans le_rfl)
  have hΩ : ∀ x ∉ (Ω : Set E), divergenceCLM φ x = 0 := fun x hx =>
    Function.notMem_support.1 fun h => hx (hsupp h)
  have hset : ∫ x, divergenceCLM φ x * s.indicator 1 x ∂μ = ∫ x in s, divergenceCLM φ x ∂μ := by
    calc ∫ x, divergenceCLM φ x * s.indicator 1 x ∂μ
        = ∫ x in (Ω : Set E), divergenceCLM φ x * s.indicator 1 x ∂μ :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hΩ x hx]).symm
      _ = ∫ x in (Ω : Set E), s.indicator (divergenceCLM φ) x ∂μ := by
          congr 1 with x
          by_cases hx : x ∈ s <;> simp [hx]
      _ = ∫ x in s, divergenceCLM φ x ∂(μ.restrict Ω) := integral_indicator₀ hs
      _ = ∫ x in s, divergenceCLM φ x ∂μ := by
          rw [← Measure.restrict_comm Ω.isOpen.measurableSet]
          exact setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ.restrict s) hΩ
  rw [hset, hdiv φ, ← integral_neg]
  congr 1 with x
  simp

/-- **Perimeter measure from a Gauss–Green identity.** If `s` is null-measurable on `Ω` for a
locally finite measure `μ` and satisfies `∫_s div φ ∂μ = ∫ ⟪φ, n⟫ ∂ν` against a locally finite
measure `ν` on `Ω` with a `ν`-a.e. unit vector field `n`, then the perimeter measure
`|Dχ_s|` on `Ω` is `ν`. -/
theorem variationMeasure_indicator_eq_of_forall_setIntegral_divergenceCLM_eq
    [IsLocallyFiniteMeasure μ] {s : Set E} (hs : NullMeasurableSet s (μ.restrict Ω))
    {ν : Measure Ω} [IsFiniteMeasureOnCompacts ν] {n : Ω → E}
    (hnm : AEStronglyMeasurable n ν) (hn1 : ∀ᵐ x ∂ν, ‖n x‖ = 1)
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x in s, divergenceCLM φ x ∂μ = ∫ x, ⟪φ x, n x⟫ ∂ν) :
    variationMeasure μ Ω (s.indicator 1) = ν :=
  variationMeasure_eq_of_forall_integral_divergenceCLM_mul_eq
    (locallyIntegrableOn_indicator_const hs 1) hnm.neg (hn1.mono fun _ hx => by simp [hx])
    (integral_divergenceCLM_mul_indicator_eq_neg_integral hs hdiv)

/-- **Relative perimeter from a Gauss–Green identity.** Under the hypotheses of
`TauCeti.variationMeasure_indicator_eq_of_forall_setIntegral_divergenceCLM_eq`, the perimeter of `s`
in every open `U ⊆ Ω` equals `ν ((↑) ⁻¹' U)`. -/
theorem perimeter_eq_of_forall_setIntegral_divergenceCLM_eq
    [IsLocallyFiniteMeasure μ] {s : Set E} (hs : NullMeasurableSet s (μ.restrict Ω))
    {ν : Measure Ω} [IsFiniteMeasureOnCompacts ν] {n : Ω → E}
    (hnm : AEStronglyMeasurable n ν) (hn1 : ∀ᵐ x ∂ν, ‖n x‖ = 1)
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x in s, divergenceCLM φ x ∂μ = ∫ x, ⟪φ x, n x⟫ ∂ν)
    (hU : U ≤ Ω) :
    perimeter μ U s = ν (((↑) : Ω → E) ⁻¹' (U : Set E)) := by
  rw [perimeter_def]
  exact totalVariationOn_eq_of_forall_integral_divergenceCLM_mul_eq
    (locallyIntegrableOn_indicator_const hs 1) hnm.neg (hn1.mono fun _ hx => by simp [hx])
    (integral_divergenceCLM_mul_indicator_eq_neg_integral hs hdiv) hU

/-- **Reduced boundary concentration from a Gauss–Green identity.** Under the hypotheses of
`TauCeti.variationMeasure_indicator_eq_of_forall_setIntegral_divergenceCLM_eq`, `ν`-almost every
point of `Ω` belongs to the reduced boundary `∂*s`. -/
theorem ae_mem_reducedBoundary_of_forall_setIntegral_divergenceCLM_eq
    [IsLocallyFiniteMeasure μ] {s : Set E} (hs : NullMeasurableSet s (μ.restrict Ω))
    {ν : Measure Ω} [IsFiniteMeasureOnCompacts ν] {n : Ω → E}
    (hnm : AEStronglyMeasurable n ν) (hn1 : ∀ᵐ x ∂ν, ‖n x‖ = 1)
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x in s, divergenceCLM φ x ∂μ = ∫ x, ⟪φ x, n x⟫ ∂ν) :
    ∀ᵐ x : Ω ∂ν, ↑x ∈ reducedBoundary μ Ω s :=
  variationMeasure_indicator_eq_of_forall_setIntegral_divergenceCLM_eq hs hnm hn1 hdiv ▸
    ae_mem_reducedBoundary

/-- **Outer normal from a Gauss–Green identity.** Under the hypotheses of
`TauCeti.variationMeasure_indicator_eq_of_forall_setIntegral_divergenceCLM_eq`, the
measure-theoretic outer normal `outerNormal μ Ω s` agrees `ν`-almost everywhere on `Ω` with `n`. -/
theorem ae_outerNormal_eq_of_forall_setIntegral_divergenceCLM_eq
    [IsLocallyFiniteMeasure μ] {s : Set E} (hs : NullMeasurableSet s (μ.restrict Ω))
    {ν : Measure Ω} [IsFiniteMeasureOnCompacts ν] {n : Ω → E}
    (hnm : AEStronglyMeasurable n ν) (hn1 : ∀ᵐ x ∂ν, ‖n x‖ = 1)
    (hdiv : ∀ φ : 𝓓(Ω, E), ∫ x in s, divergenceCLM φ x ∂μ = ∫ x, ⟪φ x, n x⟫ ∂ν) :
    ∀ᵐ x : Ω ∂ν, outerNormal μ Ω s x = n x := by
  have hvar :=
    variationMeasure_indicator_eq_of_forall_setIntegral_divergenceCLM_eq hs hnm hn1 hdiv
  have hpol : polarDensity μ Ω (s.indicator 1) =ᵐ[ν] -n :=
    ae_polarDensity_eq_of_forall_integral_divergenceCLM_mul_eq
      (locallyIntegrableOn_indicator_const hs 1) hnm.neg (hn1.mono fun _ hx => by simp [hx])
      (integral_divergenceCLM_mul_indicator_eq_neg_integral hs hdiv)
  filter_upwards [hvar ▸ ae_outerNormal_eq, hpol] with x h1 h2
  rw [h1, h2, Pi.neg_apply, neg_neg]

end TauCeti
