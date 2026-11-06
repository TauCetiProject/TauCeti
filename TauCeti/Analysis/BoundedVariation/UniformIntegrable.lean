/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.WeakDerivative
public import Mathlib.MeasureTheory.Function.UniformIntegrable
import TauCeti.MeasureTheory.Function.DeLaValleePoussin

/-!
# Uniform integrability excludes singular variation in limits

Local `L¹` convergence of weakly differentiable functions does not by itself preserve weak
differentiability: their gradients may concentrate into a singular derivative measure.
Uniform integrability prevents this concentration.

For a locally BV limit, `variationMeasure_absolutelyContinuous_of_unifIntegrable` proves
absolute continuity of its variation measure from uniform integrability of the approximating
weak derivatives. The reference measure need only be outer regular. Lower semicontinuity
bounds variation on small open sets; outer regularity then covers reference-null sets by such
open sets.

For a locally integrable limit and a uniformly integrable, uniformly `L¹`-bounded family of weak
derivatives, `exists_hasWeakFDerivOn_integrableOn_of_uniformIntegrable` supplies an integrable
weak gradient and the lower semicontinuity bound on its norm. In particular no singular
variation survives. A superlinear integral bound is an alternative sufficient hypothesis,
recorded in `variationMeasure_absolutelyContinuous_of_superlinear_bound`. These results apply
to limits of rearranged Sobolev functions once their gradient estimates have been established;
no convergence of the gradients is required.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1 (the comparison between BV and Sobolev functions).
* G. Bianchi, R. J. Gardner, P. Gronchi, M. Kiderlen, *The Pólya–Szegő inequality for smoothing
  rearrangements*, Theorem 6.3 and Corollary 6.5 (exclusion of singular concentration).
-/

public section

open TauCeti TopologicalSpace Set Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.OuterRegular]
  {Ω : Opens E} {u : E → ℝ} {v : ι → E → ℝ} {U : ι → E → E →L[ℝ] ℝ}
  {l : Filter ι} [l.NeBot]

/-- Uniform integrability of approximating weak derivatives prevents singular variation in a
locally BV limit under local `L¹` convergence. Uniform boundedness of their global norms is not
needed here; local finiteness of the variation of the limit is assumed explicitly. -/
theorem LocallyIntegrableOn.variationMeasure_absolutelyContinuous_of_unifIntegrable
    (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V u ≠ ∞)
    (hv : ∀ i, HasWeakFDerivOn μ Ω (v i) (U i))
    (hUI : UnifIntegrable U 1 (μ.restrict Ω))
    (hconv : ∀ K, IsCompact K → K ⊆ Ω →
      Tendsto (fun i => ∫⁻ x in K, ‖v i x - u x‖ₑ ∂μ) l (𝓝 0)) :
    variationMeasure μ Ω u ≪ μ.comap ((↑) : Ω → E) := by
  refine Measure.AbsolutelyContinuous.mk fun A _ hnull => ?_
  have hnull' : μ (((↑) : Ω → E) '' A) = 0 := by
    exact ((MeasurableEmbedding.subtype_coe Ω.isOpen.measurableSet).comap_apply μ A).symm.trans
      hnull
  refine le_antisymm ?_ bot_le
  apply le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_
  obtain ⟨δ, hδ, hsmall⟩ := unifIntegrable_iff.1 hUI ε hε
  obtain ⟨V, hAV, hVo, hVδ⟩ := (Subtype.val '' A).exists_isOpen_lt_of_lt δ
    (hnull' ▸ hδ)
  let W : Opens E := ⟨V ∩ Ω, hVo.inter Ω.isOpen⟩
  have hWΩ : W ≤ Ω := inter_subset_right
  have hAW : A ⊆ ((↑) : Ω → E) ⁻¹' (W : Set E) := fun x hx =>
    ⟨hAV (mem_image_of_mem _ hx), x.2⟩
  refine (measure_mono hAW).trans ?_
  rw [variationMeasure_preimage_coe hu hfin hWΩ]
  refine (totalVariationOn_le_liminf
    (.of_forall fun i => (hv i).locallyIntegrableOn.mono_set hWΩ)
    (hu.mono_set hWΩ) (fun K hK hKW => hconv K hK (hKW.trans hWΩ))).trans ?_
  apply liminf_le_of_frequently_le'
  exact .of_forall fun i => by
    refine ((hv i).mono hWΩ).totalVariationOn_le_setLIntegral_enorm.trans ?_
    have hbound := hsmall i (W : Set E) (by
      rw [Measure.restrict_apply W.isOpen.measurableSet, inter_eq_left.mpr hWΩ]
      exact (measure_mono inter_subset_left).trans hVδ.le)
    rwa [Measure.restrict_restrict_of_subset hWΩ,
      eLpNorm_one_eq_lintegral_enorm
        ((hv i).locallyIntegrableOn_deriv.aestronglyMeasurable.mono_measure
          (Measure.restrict_mono_set μ hWΩ))] at hbound

/-- A uniform superlinear integral bound on approximating weak derivatives excludes singular
variation in a locally BV limit. Neither convexity of the superlinear function nor convergence
of the derivatives is required for this limit argument. -/
theorem LocallyIntegrableOn.variationMeasure_absolutelyContinuous_of_superlinear_bound
    (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V u ≠ ∞)
    (hv : ∀ i, HasWeakFDerivOn μ Ω (v i) (U i))
    {Φ : ℝ → ℝ} (hΦ : Tendsto (fun t => Φ t / t) atTop atTop)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ i, ∫⁻ x in Ω, ENNReal.ofReal (Φ ‖U i x‖) ∂μ ≤ C)
    (hconv : ∀ K, IsCompact K → K ⊆ Ω →
      Tendsto (fun i => ∫⁻ x in K, ‖v i x - u x‖ₑ ∂μ) l (𝓝 0)) :
    variationMeasure μ Ω u ≪ μ.comap ((↑) : Ω → E) :=
  hu.variationMeasure_absolutelyContinuous_of_unifIntegrable hfin hv
    (unifIntegrable_of_lintegral_ofReal_le hΦ
      (fun i => (hv i).locallyIntegrableOn_deriv.aestronglyMeasurable) hC hbound) hconv

/-- A locally integrable local `L¹` limit of weakly differentiable functions whose derivatives are
uniformly integrable and uniformly `L¹`-bounded has an integrable weak gradient. Its gradient
norm integral is bounded by the lower limit of those of the approximants. In contrast to weak
closedness with a specified gradient, no convergence of the derivatives is assumed. -/
theorem LocallyIntegrableOn.exists_hasWeakFDerivOn_integrableOn_of_uniformIntegrable
    [IsFiniteMeasureOnCompacts μ] (hu : LocallyIntegrableOn u Ω μ)
    (hv : ∀ i, HasWeakFDerivOn μ Ω (v i) (U i))
    (hUI : UniformIntegrable U 1 (μ.restrict Ω))
    (hconv : ∀ K, IsCompact K → K ⊆ Ω →
      Tendsto (fun i => ∫⁻ x in K, ‖v i x - u x‖ₑ ∂μ) l (𝓝 0)) :
    ∃ g : E → E, HasWeakFDerivOn μ Ω u (fun x => innerSL ℝ (g x)) ∧
      IntegrableOn g Ω μ ∧
      (∫⁻ x in Ω, ‖g x‖ₑ ∂μ) ≤ liminf (fun i => ∫⁻ x in Ω, ‖U i x‖ₑ ∂μ) l := by
  have hlsc := totalVariationOn_le_liminf
    (.of_forall fun i => (hv i).locallyIntegrableOn) hu hconv
  obtain ⟨C, hC⟩ := hUI.2
  have hnorm (i : ι) : (∫⁻ x in Ω, ‖U i x‖ₑ ∂μ) ≤ C := by
    simpa only [eLpNorm_one_eq_lintegral_enorm
      (hv i).locallyIntegrableOn_deriv.aestronglyMeasurable] using hC i
  have htv : totalVariationOn μ Ω u ≤ C := hlsc.trans
    (liminf_le_of_frequently_le' (.of_forall fun i =>
      (hv i).totalVariationOn_le_setLIntegral_enorm.trans (hnorm i)))
  have hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn μ V u ≠ ∞ :=
    fun _ _ hK => ⟨Ω, hK, (htv.trans_lt ENNReal.coe_lt_top).ne⟩
  have hac := hu.variationMeasure_absolutelyContinuous_of_unifIntegrable hfin hv hUI.1 hconv
  have hg := hasWeakFDerivOn_of_absolutelyContinuous hu hfin hac
  have hnormg : (∫⁻ x in Ω, ‖Function.extend ((↑) : Ω → E)
      (fun x => ((variationMeasure μ Ω u).rnDeriv (μ.comap (↑)) x).toReal •
        polarDensity μ Ω u x) 0 x‖ₑ ∂μ) ≤ totalVariationOn μ Ω u := by
    rw [← Subtype.range_coe (s := (Ω : Set E)), ← image_univ,
      ← setLIntegral_subtype Ω.isOpen.measurableSet]
    simp only [Subtype.val_injective.extend_apply]
    exact (setLIntegral_enorm_rnDeriv_smul_polarDensity_le hu hfin hac
      MeasurableSet.univ).trans_eq (variationMeasure_univ hu hfin)
  refine ⟨_, hg, ⟨hg.locallyIntegrableOn_gradient.aestronglyMeasurable, ?_⟩, ?_⟩
  · exact hnormg.trans_lt (htv.trans_lt ENNReal.coe_lt_top)
  · exact hnormg.trans (hlsc.trans (liminf_le_liminf (.of_forall fun i =>
      (hv i).totalVariationOn_le_setLIntegral_enorm)))

end MeasureTheory
