/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.PolarDecomposition
public import TauCeti.Analysis.BoundedVariation.Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence

/-!
# Weak derivatives and absolutely continuous derivative measures

Let `Ω` be an open set of a finite-dimensional real inner product space `E` and let `u : E → ℝ`.
This file compares the weak derivatives of `TauCeti.HasWeakFDerivOn` with the derivative measure
`Du = σ_u |Du|` of `TauCeti.Analysis.BoundedVariation.PolarDecomposition`, where `|Du|` is the
variation measure `TauCeti.variationMeasure` on `Ω` and `σ_u` is the polar density
`TauCeti.polarDensity`. Write `μ_Ω = μ.comap (↑)` for the measure `μ` seen on the subtype `Ω`.

* Against an additive Haar measure, the variation measure of a weakly differentiable function
  has the norm of the weak derivative as density,
  `|Du| = ‖Du‖ μ_Ω` (`TauCeti.HasWeakFDerivOn.variationMeasure_eq_withDensity`), and the polar
  density is the direction of the weak gradient `∇u`: `‖∇u‖ σ_u = ∇u` at `μ`-almost every point
  of `Ω` (`TauCeti.HasWeakFDerivOn.ae_norm_smul_polarDensity_eq`). Together these say that the
  derivative measure is `Du = ∇u μ_Ω`.
* Conversely, if `u` has locally finite variation and `|Du|` is absolutely continuous with
  respect to `μ_Ω`, then `u` is weakly differentiable, with weak gradient
  `(d|Du| / dμ_Ω) σ_u` (`TauCeti.exists_hasWeakFDerivOn_of_absolutelyContinuous`). Thus a function
  has a weak derivative on `Ω` exactly when it is locally integrable with locally finite variation
  and an absolutely continuous derivative measure (`TauCeti.exists_hasWeakFDerivOn_iff`). For an
  integrable function of bounded variation the weak gradient is integrable, so such a function
  lies in `W^{1,1}(Ω)` (`TauCeti.MemBV.exists_hasWeakFDerivOn_integrableOn`).

No measure is assumed for the converse beyond finiteness on compact sets, since both sides are
defined relative to the same `μ`. The forward identities use an additive Haar measure through
`TauCeti.HasWeakFDerivOn.totalVariationOn_eq_setLIntegral_enorm`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1 (`W^{1,1}` as the functions whose derivative measure is absolutely
  continuous).
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace TestFunction Set Filter
open scoped ENNReal Distributions RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Opens E} {u : E → ℝ}

/-- **The variation measure of a weakly differentiable function.** If `u` has weak derivative `U`
on `Ω`, then against an additive Haar measure `|Du| = ‖U‖ μ_Ω`: the variation measure has the
norm of the weak derivative as density with respect to `μ` on `Ω`. -/
theorem HasWeakFDerivOn.variationMeasure_eq_withDensity [μ.IsAddHaarMeasure]
    {U : E → E →L[ℝ] ℝ} (h : HasWeakFDerivOn μ Ω u U) :
    variationMeasure μ Ω u = (μ.comap ((↑) : Ω → E)).withDensity fun x => ‖U x‖ₑ := by
  have := Ω.isOpen.locallyCompactSpace
  have hΩ := Ω.isOpen.measurableSet
  have : IsFiniteMeasureOnCompacts (μ.comap ((↑) : Ω → E)) :=
    .comap' μ continuous_subtype_val (.subtype_coe hΩ)
  -- The candidate measure is finite on compact sets, hence regular.
  have : IsFiniteMeasureOnCompacts ((μ.comap ((↑) : Ω → E)).withDensity fun x => ‖U x‖ₑ) :=
    ⟨fun K hK => by
      rw [withDensity_apply' _ K]
      exact (setLIntegral_subtype hΩ K fun y => ‖U y‖ₑ).trans_lt
        (h.locallyIntegrableOn_deriv.integrableOn_compact_subset
          (Subtype.coe_image_subset _ _) (hK.image continuous_subtype_val)).2⟩
  refine (eq_variationMeasure h.locallyIntegrableOn
    (fun K hK hKΩ => h.exists_totalVariationOn_ne_top hK hKΩ) fun V hV => ?_).symm
  rw [withDensity_apply _ (V.isOpen.measurableSet.preimage measurable_subtype_coe)]
  refine (setLIntegral_subtype hΩ _ fun y => ‖U y‖ₑ).trans ?_
  -- `convert` identifies the two spellings `↥Ω` and `↑(Ω : Set E)` of the subtype.
  convert (h.mono hV).totalVariationOn_eq_setLIntegral_enorm.symm using 3
  exact image_preimage_eq_of_subset (by simpa using hV)

/-- **The polar density of a weakly differentiable function** is the direction of its weak
gradient. If `u` has weak gradient `g` on `Ω`, then against an additive Haar measure
`‖g‖ σ_u = g` at `μ`-almost every point of `Ω`. With
`TauCeti.HasWeakFDerivOn.variationMeasure_eq_withDensity` this says that the derivative measure is
`Du = σ_u |Du| = g μ_Ω`. -/
theorem HasWeakFDerivOn.ae_norm_smul_polarDensity_eq [μ.IsAddHaarMeasure] {g : E → E}
    (h : HasWeakFDerivOn μ Ω u fun x => innerSL ℝ (g x)) :
    ∀ᵐ x : Ω ∂μ.comap (↑), ‖g x‖ • polarDensity μ Ω u x = g x := by
  have := Ω.isOpen.locallyCompactSpace
  have hΩ := Ω.isOpen.measurableSet
  set ν := μ.comap ((↑) : Ω → E)
  have hvar : variationMeasure μ Ω u = ν.withDensity fun x => ‖g x‖ₑ := by
    rw [h.variationMeasure_eq_withDensity]
    congr 1 with x
    simp [← ofReal_norm, innerSL_apply_norm]
  have hgm : AEStronglyMeasurable (fun x : Ω => g x) ν := by
    have hg := h.locallyIntegrableOn_gradient.aestronglyMeasurable
    rw [← map_comap_subtype_coe hΩ] at hg
    exact (MeasurableEmbedding.subtype_coe hΩ).aestronglyMeasurable_map_iff.1 hg
  -- The normalized gradient `τ = g / ‖g‖` represents `Du` against `|Du|`.
  set τ : Ω → E := fun x => ‖g x‖⁻¹ • g x
  have hτ (x : Ω) : ‖g x‖ • τ x = g x := by
    rcases eq_or_ne (g x) 0 with h0 | h0
    · simp [τ, h0]
    · simp [τ, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0)]
  have hτloc : LocallyIntegrable τ (variationMeasure μ Ω u) := by
    have hac : variationMeasure μ Ω u ≪ ν := hvar ▸ withDensity_absolutelyContinuous _ _
    refine locallyIntegrable_iff.2 fun K hK => Measure.integrableOn_of_bounded
      hK.measure_lt_top.ne
      ((hgm.norm.aemeasurable.inv.aestronglyMeasurable.smul hgm).mono_ac hac) (M := 1)
      (ae_of_all _ fun x => ?_)
    rcases eq_or_ne (g x) 0 with h0 | h0
    · simp [τ, h0]
    · simp [τ, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
  have hrep (φ : 𝓓(Ω, E)) : ∫ x, divergenceCLM φ x * u x ∂μ =
      -∫ x, ⟪φ x, τ x⟫ ∂variationMeasure μ Ω u := by
    rw [hvar, integral_withDensity_eq_integral_toReal_smul₀ hgm.enorm
      (ae_of_all _ fun _ => enorm_lt_top)]
    simp_rw [toReal_enorm, smul_eq_mul, ← real_inner_smul_right, hτ]
    have hsub : ∫ x : Ω, ⟪(φ : E → E) x, g x⟫ ∂ν = ∫ x in Ω, ⟪(φ : E → E) x, g x⟫ ∂μ :=
      integral_subtype_comap hΩ fun x => ⟪(φ : E → E) x, g x⟫
    rw [hsub, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun hmem => hx (φ.tsupport_subset hmem),
          inner_zero_left]]
    simpa [real_inner_comm] using h.integral_divergenceCLM_smul_eq_neg_integral φ
  have hae := ae_eq_polarDensity h.locallyIntegrableOn
    (fun K hK hKΩ => h.exists_totalVariationOn_ne_top hK hKΩ) hτloc hrep
  rw [hvar] at hae
  filter_upwards [(ae_withDensity_iff' hgm.enorm).1 hae] with x hx
  rcases eq_or_ne (g x) 0 with h0 | h0
  · simp [h0]
  · rw [← hx (by simpa using h0), hτ]

/-- **A function with an absolutely continuous derivative measure is weakly differentiable.** If
`u` is locally integrable on `Ω` with locally finite variation there, and its variation measure
`|Du|` is absolutely continuous with respect to `μ` on `Ω`, then `u` has a weak gradient on `Ω`,
namely `(d|Du| / dμ_Ω) σ_u` on `Ω`. -/
theorem exists_hasWeakFDerivOn_of_absolutelyContinuous [IsFiniteMeasureOnCompacts μ]
    (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    (hac : variationMeasure μ Ω u ≪ μ.comap ((↑) : Ω → E)) :
    ∃ g : E → E, HasWeakFDerivOn μ Ω u fun x => innerSL ℝ (g x) := by
  have := Ω.isOpen.locallyCompactSpace
  have hΩ := Ω.isOpen.measurableSet
  set ν := μ.comap ((↑) : Ω → E)
  have : IsFiniteMeasureOnCompacts ν := .comap' μ continuous_subtype_val (.subtype_coe hΩ)
  set lam := variationMeasure μ Ω u
  -- The density `G = (d|Du| / dν) σ_u` on `Ω`, extended by zero.
  set G : Ω → E := fun x => (lam.rnDeriv ν x).toReal • polarDensity μ Ω u x with hG
  have hGm : Measurable G := (Measure.measurable_rnDeriv _ _).ennreal_toReal.smul
    measurable_polarDensity
  classical
  set g : E → E := fun x => if hx : x ∈ Ω then G ⟨x, hx⟩ else 0
  have hg (x : Ω) : g x = G x := dite_eq_left x.2
  have hgm : Measurable g := hGm.dite measurable_const hΩ
  -- `∫_K ‖g‖ dμ ≤ |Du|(K) < ∞` for compact `K ⊆ Ω`.
  have hgloc : LocallyIntegrableOn g Ω μ := by
    refine (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).2 fun K hKΩ hK =>
      ⟨hgm.aestronglyMeasurable, ?_⟩
    set K' : Set Ω := (↑) ⁻¹' K
    have hKK' : (↑) '' K' = K :=
      image_preimage_eq_of_subset (by rw [Subtype.range_coe_subtype]; exact hKΩ)
    have hK' : IsCompact K' := Subtype.isCompact_iff.2 (hKK' ▸ hK)
    rw [HasFiniteIntegral, ← hKK']
    refine (setLIntegral_subtype hΩ K' fun y => ‖g y‖ₑ).symm.trans_lt ?_
    calc ∫⁻ x in K', ‖g x‖ₑ ∂ν
        ≤ ∫⁻ x in K', lam.rnDeriv ν x * ‖polarDensity μ Ω u x‖ₑ ∂ν := by
          refine lintegral_mono fun x => ?_
          rw [hg, hG, enorm_smul]
          gcongr
          rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.ofReal_toReal_le
      _ = ∫⁻ x in K', ‖polarDensity μ Ω u x‖ₑ ∂lam :=
          setLIntegral_rnDeriv_mul hac measurable_polarDensity.enorm.aemeasurable
            hK'.measurableSet
      _ ≤ ∫⁻ _ in K', 1 ∂lam := lintegral_mono_ae <| ae_restrict_of_ae <|
          (ae_norm_polarDensity_eq_one hu hfin).mono fun x hx => by simp [← ofReal_norm, hx]
      _ < ∞ := by simpa using hK'.measure_lt_top
  refine ⟨g, hasWeakFDerivOn_iff.2 fun v => hasWeakLineDerivOn_iff_testFunction.2
    ⟨inferInstance, hu, ?_, fun φ => ?_⟩⟩
  · simpa [Function.comp_def, real_inner_comm] using (innerSL ℝ v).locallyIntegrableOn_comp hgloc
  -- Test the polar decomposition against the vector field `φ v`, whose divergence is `∂_v φ`.
  set ψ := postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) φ
  have hψ := integral_divergenceCLM_mul_eq_neg_integral_inner_polarDensity hu hfin ψ
  rw [divergenceCLM_postcompCLM_toSpanSingleton] at hψ
  simp only [lineDerivOp_apply] at hψ
  rw [← setIntegral_smul_eq_integral_smul φ, ← integral_subtype_comap hΩ]
  simp only [smul_eq_mul]
  rw [hψ, ← integral_rnDeriv_smul hac, neg_inj]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [ψ, hg, hG, postcompCLM_apply, Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply, real_inner_smul_left,
    smul_eq_mul]
  rw [real_inner_comm]
  ring

/-- **Weak differentiability through the derivative measure.** Against an additive Haar measure,
`u` has a weak derivative on `Ω` exactly when it is locally integrable on `Ω` with locally finite
variation there and its variation measure `|Du|` is absolutely continuous with respect to `μ` on
`Ω`. -/
theorem exists_hasWeakFDerivOn_iff [μ.IsAddHaarMeasure] :
    (∃ U : E → E →L[ℝ] ℝ, HasWeakFDerivOn μ Ω u U) ↔
      LocallyIntegrableOn u Ω μ ∧
        (∀ K, IsCompact K → K ⊆ Ω →
          ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞) ∧
        variationMeasure μ Ω u ≪ μ.comap ((↑) : Ω → E) := by
  refine ⟨fun ⟨U, h⟩ => ⟨h.locallyIntegrableOn,
    fun K hK hKΩ => h.exists_totalVariationOn_ne_top hK hKΩ, ?_⟩,
    fun ⟨hu, hfin, hac⟩ => ?_⟩
  · rw [h.variationMeasure_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  · obtain ⟨g, hg⟩ := exists_hasWeakFDerivOn_of_absolutelyContinuous hu hfin hac
    exact ⟨_, hg⟩

/-- **An integrable function of bounded variation with an absolutely continuous derivative
measure lies in `W^{1,1}(Ω)`.** If `u` is integrable on `Ω` with finite total variation there,
and its variation measure is absolutely continuous with respect to an additive Haar measure `μ`
on `Ω`, then `u` has a weak gradient on `Ω` which is integrable on `Ω`. -/
theorem MemBV.exists_hasWeakFDerivOn_integrableOn [μ.IsAddHaarMeasure] (hu : MemBV μ Ω u)
    (hac : variationMeasure μ Ω u ≪ μ.comap ((↑) : Ω → E)) :
    ∃ g : E → E, HasWeakFDerivOn μ Ω u (fun x => innerSL ℝ (g x)) ∧ IntegrableOn g Ω μ := by
  obtain ⟨g, hg⟩ := exists_hasWeakFDerivOn_of_absolutelyContinuous
    (memBV_iff.1 hu).1.locallyIntegrableOn (fun _ _ hKΩ => ⟨Ω, hKΩ, (memBV_iff.1 hu).2.ne⟩) hac
  refine ⟨g, hg, ?_⟩
  exact (hg.totalVariationOn_lt_top_iff_integrableOn.1 (memBV_iff.1 hu).2).norm.mono'
    hg.locallyIntegrableOn_gradient.aestronglyMeasurable
    (ae_of_all _ fun x => by simp [innerSL_apply_norm])

end TauCeti
