/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.BoundedVariation.WeakDerivative
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.BoundedVariation.Approximation
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Normed.Operator.Compact.Basic

/-!
# Embedding of `W^{1,1}` into `BV`, strict approximation, and compactness transfer

On an open subset `Ω` of a finite-dimensional real inner product space `E` equipped with an
additive Haar measure `μ`:

* Under `[OpensMeasurableSpace E]`, every first-order Sobolev function `u ∈ W^{1,1}(Ω)` has bounded
  variation, with total variation bounded above by the `L¹(Ω)` norm of its weak gradient
  `W1p.gradient u`. Bundling this construction produces the continuous linear map
  `TauCeti.W1p.toBVL : W1p μ Ω 1 →L[ℝ] BV μ Ω` of operator norm at most `2` satisfying
  `BV.toL1CLM ∘L W1p.toBVL = W1p.valueL`.
* Under `[BorelSpace E]`, the total variation of `u ∈ W^{1,1}(Ω)` equals the `L¹(Ω)` norm of
  `W1p.gradient u`. Because `W1p` carries the `L¹` norm of the Euclidean value-gradient jet while
  `BV` carries `‖u‖₁ + |Du|(Ω)`, the two norms satisfy `‖u‖ ≤ ‖W1p.toBVL u‖ ≤ 2 * ‖u‖`; hence
  `W1p.toBVL` is a closed topological embedding whose image consists precisely of the BV classes
  whose variation measure `|Du|` is absolutely continuous with respect to `μ` on `Ω`
  (`TauCeti.BV.mem_range_toBVL_iff`).
* Conversely, under `[BorelSpace E]`, smooth strict approximation
  (`TauCeti.Analysis.BoundedVariation.Approximation`) produces for every `u ∈ BV μ Ω` a sequence
  `w : ℕ → W1p μ Ω 1` with `W1p.value (w n) → u.toL1` in `L¹(Ω)` and
  `‖W1p.gradient (w n)‖ → |Du|(Ω)` (`TauCeti.BV.exists_w1p_tendsto_value_and_norm_gradient`).
  Consequently, the `L¹` image of the unit ball of `BV μ Ω` lies in the `L¹` closure of the image
  of the closed ball of radius `2` in `W1p μ Ω 1`, so `BV.toL1CLM` is a compact operator if and
  only if `W1p.valueL` at `p = 1` is a compact operator
  (`TauCeti.BV.isCompactOperator_toL1CLM_iff`).

No boundedness or boundary regularity of `Ω` is assumed in this file.

## Main declarations

* `TauCeti.W1p.totalVariationOn_value_le`, `TauCeti.W1p.totalVariationOn_value`, and
  `TauCeti.W1p.variationMeasure_value`: upper bound and Borel-measure identities for the total
  variation and variation measure of `u ∈ W^{1,p}(Ω)` in terms of `W1p.gradient u`.
* `TauCeti.W1p.toBVL`: the continuous linear map `W1p μ Ω 1 →L[ℝ] BV μ Ω`.
* `TauCeti.W1p.isClosedEmbedding_toBVL` and `TauCeti.BV.mem_range_toBVL_iff`: under
  `[BorelSpace E]`, `W1p.toBVL` is a closed embedding with range
  `{u ∈ BV μ Ω | variationMeasure μ Ω u ≪ μ.comap (↑)}`.
* `TauCeti.BV.exists_w1p_tendsto_value_and_norm_gradient`: strict approximation of any
  `u ∈ BV μ Ω` by elements of `W1p μ Ω 1`.
* `TauCeti.BV.isCompactOperator_toL1CLM_iff`: `BV.toL1CLM` on `Ω` is compact if and only if
  `W1p.valueL` on `W1p μ Ω 1` is compact.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1, Theorem 3.9, and Theorem 3.23.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §§5.1–5.2.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Gradient Topology

section OpensMeasurableSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

namespace W1p

/-- The total variation of the value of `u ∈ W^{1,p}(Ω)` on `Ω` is at most
`∫⁻ x in Ω, ‖W1p.gradient u x‖ₑ ∂μ`. -/
theorem totalVariationOn_value_le {p : ENNReal} [Fact (1 ≤ p)] (u : W1p μ Ω p) :
    totalVariationOn μ Ω (value u) ≤ ∫⁻ x in Ω, ‖gradient u x‖ₑ ∂μ := by
  refine (hasWeakFDerivOn u).totalVariationOn_le_setLIntegral_enorm.trans_eq ?_
  refine lintegral_congr fun x => ?_
  simp [← ofReal_norm, innerSL_apply_norm]

/-- For `u ∈ W^{1,1}(Ω)`, the total variation of `W1p.value u` on `Ω` is at most the extended
`L¹` norm of `W1p.gradient u`. -/
theorem totalVariationOn_value_one_le (u : W1p μ Ω 1) :
    totalVariationOn μ Ω (value u) ≤ ‖gradient u‖ₑ := by
  refine (totalVariationOn_value_le u).trans_eq ?_
  rw [← eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable _), ← Lp.eNorm_def]

/-- The value representative of any `u ∈ W^{1,1}(Ω)` belongs to `MemBV μ Ω`. -/
theorem memBV_value (u : W1p μ Ω 1) : MemBV μ Ω (value u) :=
  memBV_iff.mpr
    ⟨L1.integrable_coeFn (value u), (totalVariationOn_value_one_le u).trans_lt eNorm_lt_top⟩

/-- Underlying map of `W1p.toBVL`, sending `u ∈ W^{1,1}(Ω)` to its BV class. -/
private def toBVAux (u : W1p μ Ω 1) : BV μ Ω :=
  BV.ofFunction (value u) (memBV_value u)

private theorem toL1_toBVAux (u : W1p μ Ω 1) : (toBVAux u).toL1 = value u := by
  rw [toBVAux, BV.toL1_ofFunction]
  exact Integrable.toL1_coeFn (value u) _

private theorem norm_toBVAux_le (u : W1p μ Ω 1) : ‖toBVAux u‖ ≤ ‖value u‖ + ‖gradient u‖ := by
  rw [BV.norm_def, toL1_toBVAux, ← toReal_eNorm (gradient u)]
  gcongr
  · exact eNorm_ne_top
  · exact totalVariationOn_value_one_le u

/-- **Continuous linear map from `W^{1,1}(Ω)` into `BV(Ω)`.** It preserves the underlying `L¹(Ω)`
class and has operator norm at most `2`; under `[BorelSpace E]` it sends the `L¹(Ω)` norm of the
weak gradient to the total variation and is a closed topological embedding
(`TauCeti.W1p.isClosedEmbedding_toBVL`). -/
def toBVL : W1p μ Ω 1 →L[ℝ] BV μ Ω :=
  LinearMap.mkContinuous
    { toFun := toBVAux
      map_add' u v := BV.toL1_injective <| by
        rw [toL1_toBVAux, BV.toL1_add, toL1_toBVAux, toL1_toBVAux, ← valueL_apply, map_add,
          valueL_apply, valueL_apply]
      map_smul' c u := BV.toL1_injective <| by
        rw [RingHom.id_apply, toL1_toBVAux, BV.toL1_smul, toL1_toBVAux, ← valueL_apply, map_smul,
          valueL_apply] }
    2 fun u => by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      linarith [norm_toBVAux_le u, norm_value_le u, norm_gradient_le u]

/-- `W1p.toBVL` preserves the underlying `L¹(Ω)` class. -/
@[simp]
theorem toL1_toBVL (u : W1p μ Ω 1) : (toBVL u).toL1 = value u :=
  toL1_toBVAux u

/-- Composing `BV.toL1CLM` with `W1p.toBVL` recovers `W1p.valueL`. -/
@[simp]
theorem toL1CLM_comp_toBVL :
    (BV.toL1CLM : BV μ Ω →L[ℝ] _) ∘L (toBVL : W1p μ Ω 1 →L[ℝ] BV μ Ω) = valueL := by
  ext1 u
  simp [toL1_toBVL]

/-- The function coercion of `W1p.toBVL u` coincides with that of `W1p.value u`. -/
theorem coeFn_toBVL (u : W1p μ Ω 1) : (toBVL u : E → ℝ) = value u :=
  congrArg (fun v : E →₁[μ.restrict Ω] ℝ => (v : E → ℝ)) (toL1_toBVL u)

/-- The total variation of `W1p.toBVL u` on `Ω` is at most the extended `L¹` norm of
`W1p.gradient u`. -/
theorem totalVariationOn_toBVL_le (u : W1p μ Ω 1) :
    totalVariationOn μ Ω (toBVL u) ≤ ‖gradient u‖ₑ := by
  rw [coeFn_toBVL]
  exact totalVariationOn_value_one_le u

/-- The BV norm of `W1p.toBVL u` is at most `‖W1p.value u‖ + ‖W1p.gradient u‖`. -/
theorem norm_toBVL_le_norm_value_add_norm_gradient (u : W1p μ Ω 1) :
    ‖toBVL u‖ ≤ ‖value u‖ + ‖gradient u‖ :=
  norm_toBVAux_le u

/-- The BV norm of `W1p.toBVL u` is at most twice the `W^{1,1}` norm of `u`. -/
theorem norm_toBVL_le_two_mul_norm (u : W1p μ Ω 1) : ‖toBVL u‖ ≤ 2 * ‖u‖ := by
  linarith [norm_toBVL_le_norm_value_add_norm_gradient u, norm_value_le u, norm_gradient_le u]

/-- The operator norm of `W1p.toBVL` is at most `2`. -/
theorem opNorm_toBVL_le : ‖(toBVL : W1p μ Ω 1 →L[ℝ] BV μ Ω)‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end W1p

end OpensMeasurableSpace

section BorelSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

namespace W1p

/-- The total variation of the value of `u ∈ W^{1,p}(Ω)` is `∫⁻ x in Ω, ‖W1p.gradient u x‖ₑ ∂μ`. -/
theorem totalVariationOn_value {p : ENNReal} [Fact (1 ≤ p)] (u : W1p μ Ω p) :
    totalVariationOn μ Ω (value u) = ∫⁻ x in Ω, ‖gradient u x‖ₑ ∂μ := by
  rw [(hasWeakFDerivOn u).totalVariationOn_eq_setLIntegral_enorm]
  refine lintegral_congr fun x => ?_
  simp [← ofReal_norm, innerSL_apply_norm]

/-- The variation measure of `u ∈ W^{1,p}(Ω)` has density `x ↦ ‖W1p.gradient u x‖ₑ` with respect
to `μ` on `Ω`. -/
theorem variationMeasure_value {p : ENNReal} [Fact (1 ≤ p)] (u : W1p μ Ω p) :
    variationMeasure μ Ω (value u) =
      (μ.comap ((↑) : Ω → E)).withDensity fun x => ‖gradient u x‖ₑ := by
  rw [(hasWeakFDerivOn u).variationMeasure_eq_withDensity]
  congr 1 with x
  simp [← ofReal_norm, innerSL_apply_norm]

/-- The variation measure of `u ∈ W^{1,p}(Ω)` is absolutely continuous with respect to `μ` on
`Ω`. -/
theorem variationMeasure_value_absolutelyContinuous {p : ENNReal} [Fact (1 ≤ p)] (u : W1p μ Ω p) :
    variationMeasure μ Ω (value u) ≪ μ.comap ((↑) : Ω → E) := by
  rw [variationMeasure_value]
  exact withDensity_absolutelyContinuous _ _

/-- For `u ∈ W^{1,1}(Ω)`, the total variation of `W1p.value u` on `Ω` is the extended `L¹` norm of
`W1p.gradient u`. -/
@[simp]
theorem totalVariationOn_value_one (u : W1p μ Ω 1) :
    totalVariationOn μ Ω (value u) = ‖gradient u‖ₑ := by
  rw [totalVariationOn_value, ← eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable _),
    ← Lp.eNorm_def]

/-- The total variation of `W1p.toBVL u` on `Ω` is the extended `L¹` norm of `W1p.gradient u`. -/
theorem totalVariationOn_toBVL (u : W1p μ Ω 1) :
    totalVariationOn μ Ω (toBVL u) = ‖gradient u‖ₑ := by
  rw [coeFn_toBVL, totalVariationOn_value_one]

/-- The variation measure of `W1p.toBVL u` has density `x ↦ ‖W1p.gradient u x‖ₑ` with respect to
`μ` on `Ω`. -/
theorem variationMeasure_toBVL (u : W1p μ Ω 1) :
    variationMeasure μ Ω (toBVL u) =
      (μ.comap ((↑) : Ω → E)).withDensity fun x => ‖gradient u x‖ₑ := by
  rw [coeFn_toBVL, variationMeasure_value]

/-- The BV norm of `W1p.toBVL u` is `‖W1p.value u‖ + ‖W1p.gradient u‖`. -/
theorem norm_toBVL (u : W1p μ Ω 1) : ‖toBVL u‖ = ‖value u‖ + ‖gradient u‖ := by
  rw [BV.norm_def, toL1_toBVL, totalVariationOn_value_one, toReal_eNorm]

/-- The `W^{1,1}` norm of `u` is bounded above by the BV norm of `W1p.toBVL u`. -/
theorem norm_le_norm_toBVL (u : W1p μ Ω 1) : ‖u‖ ≤ ‖toBVL u‖ := by
  rw [norm_toBVL]
  exact norm_le_norm_value_add_norm_gradient u

/-- `W1p.toBVL` is `1`-antilipschitz from `W1p μ Ω 1` into `BV μ Ω`. -/
theorem antilipschitzWith_toBVL : AntilipschitzWith 1 (toBVL : W1p μ Ω 1 →L[ℝ] BV μ Ω) :=
  AddMonoidHomClass.antilipschitz_of_bound toBVL fun u => by simpa using norm_le_norm_toBVL u

/-- `W1p.toBVL` is injective. -/
theorem toBVL_injective : Function.Injective (toBVL : W1p μ Ω 1 →L[ℝ] BV μ Ω) :=
  antilipschitzWith_toBVL.injective

/-- `W1p.toBVL` embeds `W1p μ Ω 1` as a closed topological subspace of `BV μ Ω`. -/
theorem isClosedEmbedding_toBVL :
    Topology.IsClosedEmbedding (toBVL : W1p μ Ω 1 →L[ℝ] BV μ Ω) :=
  antilipschitzWith_toBVL.isClosedEmbedding toBVL.uniformContinuous

end W1p

namespace BV

/-- **Characterization of the image of `W^{1,1}(Ω)` inside `BV(Ω)`.** A BV class `u ∈ BV μ Ω`
lies in the range of `W1p.toBVL` if and only if its variation measure `variationMeasure μ Ω u` is
absolutely continuous with respect to `μ` on `Ω`. -/
theorem mem_range_toBVL_iff (u : BV μ Ω) :
    u ∈ range (W1p.toBVL : W1p μ Ω 1 →L[ℝ] BV μ Ω) ↔
      variationMeasure μ Ω u ≪ μ.comap ((↑) : Ω → E) := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [W1p.coeFn_toBVL]
    exact W1p.variationMeasure_value_absolutelyContinuous w
  · intro hac
    obtain ⟨g, hg, hg_int⟩ := u.memBV.exists_hasWeakFDerivOn_integrableOn hac
    have hu1 : MemLp u 1 (μ.restrict Ω) := memLp_one_iff_integrable.mpr u.integrableOn
    have hD1 : MemLp (fun x => innerSL ℝ (g x)) 1 (μ.restrict Ω) :=
      memLp_one_iff_integrable.mpr
        ((innerSL ℝ (E := E)).toContinuousLinearMap.integrable_comp hg_int)
    obtain ⟨w, hw, -⟩ := W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn hu1 hD1 hg
    exact ⟨w, ext <| by simpa only [W1p.coeFn_toBVL] using hw⟩

/-- Assemble an element of `W1p μ Ω 1` from a `C¹` approximation `f` of `u ∈ BV μ Ω` whose `L¹`
distance to `u` and derivative `L¹` seminorm on `Ω` are finite. -/
private theorem exists_w1p_of_contDiffOn_of_lintegral_lt_top (u : BV μ Ω) {f : E → ℝ}
    (hf : ContDiffOn ℝ 1 f Ω) (hL : ∫⁻ x in Ω, ‖f x - u x‖ₑ ∂μ < ∞)
    (hD : ∫⁻ x in Ω, ‖fderiv ℝ f x‖ₑ ∂μ < ∞) :
    ∃ w : W1p μ Ω 1,
      ‖W1p.value w - u.toL1‖ₑ = ∫⁻ x in Ω, ‖f x - u x‖ₑ ∂μ ∧
      ‖W1p.gradient w‖ₑ = ∫⁻ x in Ω, ‖fderiv ℝ f x‖ₑ ∂μ := by
  have hfm : AEStronglyMeasurable f (μ.restrict Ω) :=
    hf.continuousOn.aestronglyMeasurable Ω.isOpen.measurableSet
  have hsub_int : IntegrableOn (fun x => f x - u x) Ω μ :=
    ⟨hfm.sub u.integrableOn.aestronglyMeasurable, hL⟩
  have hf_lp : MemLp f 1 (μ.restrict Ω) :=
    memLp_one_iff_integrable.mpr <|
      (hsub_int.add u.integrableOn).congr (ae_of_all _ fun x => sub_add_cancel (f x) (u x))
  have hgrad_norm (x : E) : ‖(∇ f) x‖ₑ = ‖fderiv ℝ f x‖ₑ := by
    simp only [← ofReal_norm, norm_gradient_eq_norm_fderiv]
  have hg_lp : MemLp (∇ f) 1 (μ.restrict Ω) :=
    memLp_one_iff_integrable.mpr
      ⟨(measurable_gradient f).aestronglyMeasurable,
        by simpa only [HasFiniteIntegral, hgrad_norm]⟩
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn hf hf_lp hg_lp
  refine ⟨w, ?_, ?_⟩
  · have hsub_ae : (W1p.value w - u.toL1 : E →₁[μ.restrict Ω] ℝ) =ᵐ[μ.restrict Ω]
        fun x => f x - u x := by
      filter_upwards [Lp.coeFn_sub (W1p.value w) u.toL1, hwv] with x h₁ h₂
      exact h₁.trans (by simp [h₂])
    rw [Lp.eNorm_def, eLpNorm_congr_ae hsub_ae,
      eLpNorm_one_eq_lintegral_eNorm hsub_int.aestronglyMeasurable]
  · rw [Lp.eNorm_def, eLpNorm_congr_ae hwg,
      eLpNorm_one_eq_lintegral_eNorm hg_lp.aestronglyMeasurable]
    exact lintegral_congr hgrad_norm

/-- **Strict `W^{1,1}` approximation of BV functions on an open set.** Every `u ∈ BV μ Ω` is the
limit in `L¹(Ω)` of a sequence `w : ℕ → W1p μ Ω 1` such that `‖W1p.gradient (w n)‖` converges to
`(totalVariationOn μ Ω u).toReal`. Neither boundedness nor boundary regularity of `Ω` is
assumed. -/
theorem exists_w1p_tendsto_value_and_norm_gradient (u : BV μ Ω) :
    ∃ w : ℕ → W1p μ Ω 1,
      Tendsto (fun n => W1p.value (w n)) atTop (𝓝 u.toL1) ∧
      Tendsto (fun n => ‖W1p.gradient (w n)‖) atTop (𝓝 (totalVariationOn μ Ω u).toReal) := by
  obtain ⟨f, hf, hL, hD⟩ :=
    u.integrableOn.locallyIntegrableOn.exists_contDiffOn_tendsto_setLIntegral_enorm_fderiv
  have hL_ev : ∀ᶠ n in atTop, ∫⁻ x in Ω, ‖f n x - u x‖ₑ ∂μ < ∞ :=
    hL.eventually (Iio_mem_nhds ENNReal.zero_lt_top)
  have hD_ev : ∀ᶠ n in atTop, ∫⁻ x in Ω, ‖fderiv ℝ (f n) x‖ₑ ∂μ < ∞ :=
    hD.eventually (Iio_mem_nhds u.totalVariationOn_lt_top)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hL_ev.and hD_ev)
  choose w hwL hwD using fun k : ℕ =>
    exists_w1p_of_contDiffOn_of_lintegral_lt_top u ((hf (k + N)).of_le (by simp))
      (hN (k + N) (Nat.le_add_left N k)).1 (hN (k + N) (Nat.le_add_left N k)).2
  refine ⟨w, ?_, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hL' : Tendsto (fun k => ‖W1p.value (w k) - u.toL1‖ₑ) atTop (𝓝 0) := by
      simpa only [Function.comp_def, hwL] using hL.comp (tendsto_add_atTop_nat N)
    simpa only [Function.comp_def, toReal_eNorm, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL'
  · have hD' : Tendsto (fun k => ‖W1p.gradient (w k)‖ₑ) atTop (𝓝 (totalVariationOn μ Ω u)) := by
      simpa only [Function.comp_def, hwD] using hD.comp (tendsto_add_atTop_nat N)
    simpa only [Function.comp_def, toReal_eNorm] using
      (ENNReal.tendsto_toReal u.totalVariationOn_lt_top.ne).comp hD'

/-- The `L¹(Ω)` image of the closed unit ball of `BV μ Ω` lies in the `L¹(Ω)` closure of the image
under `W1p.valueL` of the closed ball of radius `2` in `W1p μ Ω 1`. -/
theorem subset_closure_valueL_image_closedBall :
    (toL1CLM : BV μ Ω →L[ℝ] _) '' closedBall 0 1 ⊆
      closure ((W1p.valueL : W1p μ Ω 1 →L[ℝ] _) '' closedBall 0 2) := by
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_closedBall_zero_iff] at hu
  obtain ⟨w, hv, hg⟩ := exists_w1p_tendsto_value_and_norm_gradient u
  have hnorm : Tendsto (fun n => ‖W1p.value (w n)‖ + ‖W1p.gradient (w n)‖) atTop (𝓝 ‖u‖) := by
    rw [norm_def]
    exact hv.norm.add hg
  have hev : ∀ᶠ n in atTop, W1p.value (w n) ∈
      (W1p.valueL : W1p μ Ω 1 →L[ℝ] _) '' closedBall 0 2 := by
    filter_upwards [hnorm.eventually (Iio_mem_nhds (hu.trans_lt one_lt_two))] with n hn
    refine ⟨w n, mem_closedBall_zero_iff.mpr ?_, W1p.valueL_apply (w n)⟩
    exact (W1p.norm_le_norm_value_add_norm_gradient (w n)).trans hn.le
  rw [toL1CLM_apply]
  exact mem_closure_of_tendsto hv hev

/-- **Equivalence of global `L¹` compactness for `BV` and `W^{1,1}`.** On any open set `Ω`, the
inclusion `BV.toL1CLM : BV μ Ω →L[ℝ] (E →₁[μ.restrict Ω] ℝ)` is a compact operator if and only if
the Sobolev value projection `W1p.valueL : W1p μ Ω 1 →L[ℝ] Lp ℝ 1 (μ.restrict Ω)` is a compact
operator. -/
theorem isCompactOperator_toL1CLM_iff :
    IsCompactOperator (toL1CLM : BV μ Ω →L[ℝ] _) ↔
      IsCompactOperator (W1p.valueL : W1p μ Ω 1 →L[ℝ] _) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← W1p.toL1CLM_comp_toBVL]
    exact h.comp_clm W1p.toBVL
  · exact (isCompactOperator_iff_totallyBounded_image_closedBall
      (toL1CLM : BV μ Ω →L[ℝ] _).toLinearMap zero_lt_one).mpr
      ((h.totallyBounded_image_closedBall 2).closure.subset subset_closure_valueL_image_closedBall)

end BV

end BorelSpace

end TauCeti
