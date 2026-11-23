/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.BoundedVariation.Space
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.BoundedVariation.Approximation
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Normed.Operator.Compact.Basic

/-!
# Continuous inclusion of `W^{1,1}` into `BV`, strict approximation, and compactness transfer

On an open subset `Ω` of a finite-dimensional real inner product space `E` equipped with an
additive Haar measure `μ`:

* Under `[OpensMeasurableSpace E]`, every first-order Sobolev function `u ∈ W^{1,1}(Ω)` has bounded
  variation, with total variation bounded above by the `L¹(Ω)` norm of its weak gradient
  `W1p.gradient u`. Bundling this construction produces the continuous linear map
  `TauCeti.W1p.toBVL : W1p μ Ω 1 →L[ℝ] BV μ Ω` of operator norm at most `2` satisfying
  `BV.toL1CLM ∘L W1p.toBVL = W1p.valueL`.
* Conversely, under `[BorelSpace E]`, smooth strict approximation
  (`TauCeti.Analysis.BoundedVariation.Approximation`) produces for every `u ∈ BV μ Ω` a sequence
  `w : ℕ → W1p μ Ω 1` with `W1p.value (w n) → u.toL1` in `L¹(Ω)` and
  `‖W1p.gradient (w n)‖ → |Du|(Ω)` (`TauCeti.BV.exists_w1p_tendsto_value_and_norm_gradient`).
  Rescaling the approximants shows that for every radius `r`, the `L¹(Ω)` image of the closed ball
  of radius `r` in `BV μ Ω` lies in the `L¹(Ω)` closure of the image of the closed ball of radius
  `r` in `W1p μ Ω 1` (`TauCeti.BV.toL1CLM_image_closedBall_subset_closure_valueL_image_closedBall`),
  so `BV.toL1CLM` is a compact operator if and only if `W1p.valueL` at `p = 1` is a compact
  operator (`TauCeti.BV.isCompactOperator_toL1CLM_iff_isCompactOperator_valueL`).

No boundedness or boundary regularity of `Ω` is assumed in this file.

## Main declarations

* `TauCeti.W1p.totalVariationOn_value_le` and `TauCeti.W1p.totalVariationOn_value_one_le`: upper
  bound on the total variation of `u ∈ W^{1,p}(Ω)` in terms of `W1p.gradient u`.
* `TauCeti.W1p.toBVL`: the continuous linear map `W1p μ Ω 1 →L[ℝ] BV μ Ω`.
* `TauCeti.BV.exists_w1p_tendsto_value_and_norm_gradient`: strict approximation of any
  `u ∈ BV μ Ω` by elements of `W1p μ Ω 1`.
* `TauCeti.BV.toL1CLM_image_closedBall_subset_closure_valueL_image_closedBall`: density of the
  `W^{1,1}` closed ball of radius `r` in the `BV` closed ball of radius `r` with respect to `L¹(Ω)`.
* `TauCeti.BV.isCompactOperator_toL1CLM_iff_isCompactOperator_valueL`: `BV.toL1CLM` on `Ω` is
  compact if and only if `W1p.valueL` on `W1p μ Ω 1` is compact.

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
class and has operator norm at most `2`. -/
def toBVL : W1p μ Ω 1 →L[ℝ] BV μ Ω :=
  LinearMap.mkContinuous
    { toFun := toBVAux
      map_add' u v := BV.toL1_injective <| by simp [toL1_toBVAux]
      map_smul' c u := BV.toL1_injective <| by
        simpa only [RingHom.id_apply, toL1_toBVAux, BV.toL1_smul, valueL_apply] using
          map_smul valueL c u }
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

namespace BV

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

/-- For every radius `r`, the `L¹(Ω)` image of the closed ball of radius `r` in `BV μ Ω` lies in
the `L¹(Ω)` closure of the image under `W1p.valueL` of the closed ball of radius `r` in
`W1p μ Ω 1`. -/
theorem toL1CLM_image_closedBall_subset_closure_valueL_image_closedBall (r : ℝ) :
    (toL1CLM : BV μ Ω →L[ℝ] _) '' closedBall 0 r ⊆
      closure ((W1p.valueL : W1p μ Ω 1 →L[ℝ] _) '' closedBall 0 r) := by
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_closedBall_zero_iff] at hu
  rcases lt_or_eq_of_le ((norm_nonneg u).trans hu) with hr | rfl
  · obtain ⟨w, hv, hg⟩ := exists_w1p_tendsto_value_and_norm_gradient u
    let a : ℕ → ℝ := fun n => r / max r (‖W1p.value (w n)‖ + ‖W1p.gradient (w n)‖)
    have hsum : Tendsto (fun n => ‖W1p.value (w n)‖ + ‖W1p.gradient (w n)‖) atTop (𝓝 ‖u‖) := by
      rw [norm_def]
      exact hv.norm.add hg
    have ha : Tendsto a atTop (𝓝 1) := by
      have hmax : Tendsto (fun n => max r (‖W1p.value (w n)‖ + ‖W1p.gradient (w n)‖))
          atTop (𝓝 r) := by
        simpa only [max_eq_left hu] using (tendsto_const_nhds (x := r)).max hsum
      simpa only [a, Pi.div_def, div_self hr.ne'] using
        (tendsto_const_nhds (x := r)).div hmax hr.ne'
    have hlim : Tendsto (fun n => W1p.valueL (a n • w n)) atTop (𝓝 u.toL1) := by
      simpa only [map_smul, W1p.valueL_apply, one_smul] using ha.smul hv
    rw [toL1CLM_apply]
    refine mem_closure_of_tendsto hlim (.of_forall fun n => ⟨a n • w n, ?_, rfl⟩)
    have hmpos : 0 < max r (‖W1p.value (w n)‖ + ‖W1p.gradient (w n)‖) :=
      hr.trans_le (le_max_left _ _)
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (div_nonneg hr.le hmpos.le)]
    calc r / max r (‖W1p.value (w n)‖ + ‖W1p.gradient (w n)‖) * ‖w n‖
        ≤ r / max r (‖W1p.value (w n)‖ + ‖W1p.gradient (w n)‖) *
          max r (‖W1p.value (w n)‖ + ‖W1p.gradient (w n)‖) := by
          gcongr
          exact (W1p.norm_le_norm_value_add_norm_gradient (w n)).trans (le_max_right _ _)
      _ = r := div_mul_cancel₀ r hmpos.ne'
  · have hu0 : u = 0 := norm_eq_zero.mp (le_antisymm hu (norm_nonneg u))
    rw [hu0, map_zero]
    exact subset_closure ⟨0, mem_closedBall_self le_rfl, map_zero _⟩

/-- **Equivalence of global `L¹` compactness for `BV` and `W^{1,1}`.** On any open set `Ω`, the
inclusion `BV.toL1CLM : BV μ Ω →L[ℝ] (E →₁[μ.restrict Ω] ℝ)` is a compact operator if and only if
the Sobolev value projection `W1p.valueL : W1p μ Ω 1 →L[ℝ] Lp ℝ 1 (μ.restrict Ω)` is a compact
operator. -/
theorem isCompactOperator_toL1CLM_iff_isCompactOperator_valueL :
    IsCompactOperator (toL1CLM : BV μ Ω →L[ℝ] _) ↔
      IsCompactOperator (W1p.valueL : W1p μ Ω 1 →L[ℝ] _) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← W1p.toL1CLM_comp_toBVL]
    exact h.comp_clm W1p.toBVL
  · exact (isCompactOperator_iff_totallyBounded_image_closedBall
      (toL1CLM : BV μ Ω →L[ℝ] _).toLinearMap zero_lt_one).mpr
      ((h.totallyBounded_image_closedBall 1).closure.subset
        (toL1CLM_image_closedBall_subset_closure_valueL_image_closedBall 1))

end BV

end BorelSpace

end TauCeti
