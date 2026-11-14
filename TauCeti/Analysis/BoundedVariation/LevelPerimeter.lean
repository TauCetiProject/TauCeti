/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Function.Coarea.Lipschitz
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import TauCeti.Analysis.BoundedVariation.Coarea
import TauCeti.Analysis.BoundedVariation.TotalVariation
import TauCeti.Analysis.BoundedVariation.Truncation
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Function.Coarea.Measurability
import TauCeti.Topology.EMetricSpace.Lipschitz
import TauCeti.Topology.MetricSpace.ProperSpace

/-!
# Perimeter of superlevel sets of locally Lipschitz functions

Let `E` be a finite-dimensional real inner product space of dimension `n`, and let `u : E → ℝ` be
locally Lipschitz on an open set `Ω ⊆ E`. Both the BV coarea formula
(`LocallyLipschitzOn.lintegral_perimeter_eq_setLIntegral_enorm_fderiv`) and the Federer coarea
formula (`lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv`
on `LocallyLipschitzOn`) express `∫_Ω ‖Du‖` as an integral over levels `t ∈ ℝ`: the former
integrates the variational perimeter `P({u > t}; Ω)`, and the latter integrates the normalized
`(n - 1)`-dimensional Euclidean Hausdorff measure `Hⁿ⁻¹(Ω ∩ u⁻¹{t}) = μHE[n - 1] (Ω ∩ u ⁻¹' {t})`.

This file identifies the two integrands at almost every level `t ∈ ℝ`, without any integrability or
finite-variation hypothesis on `u`:

`P({u > t}; Ω) = μHE[n - 1] (Ω ∩ u ⁻¹' {t})` for almost every `t ∈ ℝ`.

On each relatively compact open subset `V` of `Ω`, clipping `u` to `[a, b]` equates the integrals
of both level functions over `[a, b)` for all `a < b`: by truncation of BV variation, the integral
of `P({u > t}; V)` over `[a, b)` is the total variation of `max a (min u b)` on `V`, which equals
`∫_{V ∩ {a < u < b}} ‖Du‖`, and the Lipschitz coarea formula on `V ∩ {a < u < b}` equates this with
the integral of `μHE[n - 1] (V ∩ u ⁻¹' {t})` over `(a, b)`. Since both level functions are
integrable on `ℝ` for relatively compact `V`, Radon–Nikodym uniqueness gives almost-everywhere
equality on `V`, and exhausting `Ω` by an increasing sequence of relatively compact open subsets
passes to general `Ω`.

## Main results

* `LocallyLipschitzOn.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage`: for `u`
  locally Lipschitz on `Ω`, `perimeter volume Ω {x | t < u x} = μHE[n - 1] (Ω ∩ u ⁻¹' {t})` at
  almost every `t ∈ ℝ`.
* `LocallyLipschitz.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage`,
  `LocallyLipschitz.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage`, and
  `LipschitzWith.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage`: specializations to
  globally locally Lipschitz and Lipschitz functions.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4 and §5.5.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 13.
-/

public section

open Filter Function MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal NNReal Topology

section PrivateHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- At a point `x` where `u` is continuous, the totalized derivative of `max a (min u b)` (`a < b`)
agrees with `fderiv ℝ u x` when `u x ∈ (a, b)` and vanishes otherwise. -/
private theorem fderiv_max_min_const_eq_indicator_of_continuousAt {u : E → ℝ} {x : E}
    (hu : ContinuousAt u x) {a b : ℝ} (hab : a < b) :
    fderiv ℝ (fun y ↦ max a (min (u y) b)) x = (u ⁻¹' Ioo a b).indicator (fderiv ℝ u) x := by
  rcases lt_trichotomy (u x) a with h | h | h
  · rw [indicator_of_notMem (s := u ⁻¹' Ioo a b) fun hx ↦ (h.trans hx.1).false]
    refine (EventuallyEq.fderiv_eq (f := fun _ ↦ a) ?_).trans (fderiv_const_apply a)
    filter_upwards [hu.eventually (gt_mem_nhds h)] with y hy
    exact max_eq_left ((min_le_left _ _).trans hy.le)
  · rw [indicator_of_notMem (s := u ⁻¹' Ioo a b) fun hx ↦ (h ▸ hx.1).false]
    refine IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun y ↦ ?_)
    simp only [h, min_eq_left hab.le, max_self]
    exact le_max_left _ _
  rcases lt_trichotomy (u x) b with h' | h' | h'
  · rw [indicator_of_mem (s := u ⁻¹' Ioo a b) ⟨h, h'⟩]
    refine EventuallyEq.fderiv_eq ?_
    filter_upwards [hu.eventually (lt_mem_nhds h), hu.eventually (gt_mem_nhds h')] with y hy hy'
    rw [min_eq_left hy'.le, max_eq_right hy.le]
  · rw [indicator_of_notMem (s := u ⁻¹' Ioo a b) fun hx ↦ (h' ▸ hx.2).false]
    refine IsLocalMax.fderiv_eq_zero (Eventually.of_forall fun y ↦ ?_)
    simp only [h', min_self, max_eq_right hab.le]
    exact max_le hab.le (min_le_right _ _)
  · rw [indicator_of_notMem (s := u ⁻¹' Ioo a b) fun hx ↦ (hx.2.trans h').false]
    refine (EventuallyEq.fderiv_eq (f := fun _ ↦ b) ?_).trans (fderiv_const_apply b)
    filter_upwards [hu.eventually (lt_mem_nhds h')] with y hy
    rw [min_eq_right hy.le, max_eq_right hab.le]

/-- On an open set `V`, the integral of the perimeter of `{u > t}` over `[a, b)` equals the
integral of the `(n - 1)`-dimensional Hausdorff measure of `V ∩ u ⁻¹' {t}` over `[a, b)`. -/
private theorem setLIntegral_Ico_perimeter_eq_euclideanHausdorffMeasure {V : Opens E} {u : E → ℝ}
    (huV : LocallyLipschitzOn V u) {a b : ℝ} (hab : a < b) :
    ∫⁻ t in Ico a b, TauCeti.perimeter volume V {x | t < u x} =
      ∫⁻ t in Ico a b, μHE[finrank ℝ E - 1] ((V : Set E) ∩ u ⁻¹' {t}) := by
  have hVm : MeasurableSet (V : Set E) := V.isOpen.measurableSet
  have hu_cont : ContinuousOn u V := huV.continuousOn
  have hclamp_lip : LocallyLipschitzOn V (fun x ↦ max a (min (u x) b)) := by
    change LocallyLipschitzOn V ((fun t : ℝ ↦ max a (min t b)) ∘ u)
    exact LocallyLipschitz.comp_locallyLipschitzOn
      (((LipschitzWith.const a).max
        (LipschitzWith.id.min (LipschitzWith.const b))).locallyLipschitz)
      huV
  -- Express the `[a, b)` perimeter integral via the clamped variation and evaluate its gradient.
  rw [← TauCeti.totalVariationOn_max_min_const_eq_lintegral_perimeter
      (hu_cont.locallyIntegrableOn hVm),
    hclamp_lip.totalVariationOn_eq_setLIntegral_enorm_fderiv]
  have hband : MeasurableSet ((V : Set E) ∩ u ⁻¹' Ioo a b) :=
    (hu_cont.isOpen_inter_preimage V.isOpen isOpen_Ioo).measurableSet
  have hgrad : ∫⁻ x in (V : Set E), ‖fderiv ℝ (fun y ↦ max a (min (u y) b)) x‖ₑ =
      ∫⁻ x in (V : Set E) ∩ u ⁻¹' Ioo a b, ENNReal.ofReal (fderiv ℝ u x).adjoint.normDet := by
    have hind : ∫⁻ x in (V : Set E), ‖fderiv ℝ (fun y ↦ max a (min (u y) b)) x‖ₑ =
        ∫⁻ x in (V : Set E), (u ⁻¹' Ioo a b).indicator (fun x ↦ ‖fderiv ℝ u x‖ₑ) x := by
      refine setLIntegral_congr_fun hVm fun x hx ↦ ?_
      rw [fderiv_max_min_const_eq_indicator_of_continuousAt
        ((hu_cont x hx).continuousAt (V.isOpen.mem_nhds hx)) hab]
      by_cases hxu : x ∈ u ⁻¹' Ioo a b
      · simp [hxu]
      · simp [hxu, ← ofReal_norm]
    rw [hind, ← lintegral_indicator hVm, ← lintegral_indicator hband]
    refine lintegral_congr fun x ↦ ?_
    by_cases hxV : x ∈ (V : Set E) <;> by_cases hxu : x ∈ u ⁻¹' Ioo a b <;>
      simp [hxV, hxu, ContinuousLinearMap.normDet_adjoint_eq_norm, ofReal_norm]
  have hco :=
    huV.lintegral_euclideanHausdorffMeasure_inter_preimage_eq_lintegral_normDet_adjoint_fderiv
      V.isOpen inter_subset_left hband.nullMeasurableSet
  rw [hgrad, ← hco, finrank_self]
  -- Identify the fibre integral over `ℝ` with the restricted integral over `[a, b)`.
  have hfib : (∫⁻ t : ℝ, μHE[finrank ℝ E - 1] (((V : Set E) ∩ u ⁻¹' Ioo a b) ∩ u ⁻¹' {t})) =
      ∫⁻ t in Ioo a b, μHE[finrank ℝ E - 1] ((V : Set E) ∩ u ⁻¹' {t}) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun t ↦ ?_
    by_cases ht : t ∈ Ioo a b
    · rw [indicator_of_mem ht]
      congr 1
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      exact ⟨fun ⟨⟨hxV, _⟩, hxt⟩ ↦ ⟨hxV, hxt⟩, fun ⟨hxV, hxt⟩ ↦ ⟨⟨hxV, hxt.symm ▸ ht⟩, hxt⟩⟩
    · rw [indicator_of_notMem ht]
      have hemp : ((V : Set E) ∩ u ⁻¹' Ioo a b) ∩ u ⁻¹' {t} = ∅ :=
        eq_empty_of_forall_notMem fun x ⟨⟨_, hxu⟩, hxt⟩ ↦ ht (hxt ▸ hxu)
      simp [hemp]
  rw [hfib]
  exact setLIntegral_congr Ioo_ae_eq_Ico

/-- Almost-everywhere equality of superlevel perimeter and Hausdorff level measure on a relatively
compact open subset `V` of `Ω`. -/
private theorem ae_perimeter_eq_euclideanHausdorffMeasure_of_isCompact_closure {Ω V : Opens E}
    {u : E → ℝ} (hu : LocallyLipschitzOn Ω u) (hVc : IsCompact (closure (V : Set E)))
    (hVΩ : closure (V : Set E) ⊆ Ω) :
    ∀ᵐ t : ℝ, TauCeti.perimeter volume V {x | t < u x} =
      μHE[finrank ℝ E - 1] ((V : Set E) ∩ u ⁻¹' {t}) := by
  have huV : LocallyLipschitzOn V u := hu.mono (subset_closure.trans hVΩ)
  have hVm : MeasurableSet (V : Set E) := V.isOpen.measurableSet
  set P : ℝ → ℝ≥0∞ := fun t ↦ TauCeti.perimeter volume V {x | t < u x}
  set H : ℝ → ℝ≥0∞ := fun t ↦ μHE[finrank ℝ E - 1] ((V : Set E) ∩ u ⁻¹' {t})
  have hPm : Measurable P :=
    TauCeti.measurable_perimeter_setOf_lt (huV.continuousOn.aemeasurable hVm)
  have hHm : AEMeasurable H volume :=
    LocallyLipschitzOn.aemeasurable_euclideanHausdorffMeasure_inter_preimage (Y := ℝ) volume huV
      hVm.nullMeasurableSet (by rw [finrank_self]; exact le_add_tsub)
  have hfin : ∫⁻ x in (V : Set E), ‖fderiv ℝ u x‖ₑ < ∞ := by
    have hint := (hu.integrableOn_normDet_adjoint_fderiv_of_isCompact Ω.isOpen hVΩ hVc).mono_set
      subset_closure
    simpa only [ContinuousLinearMap.normDet_adjoint_eq_norm, ofReal_norm] using
      hint.lintegral_lt_top
  have hP_fin : IsFiniteMeasure (volume.withDensity P) := by
    rw [isFiniteMeasure_withDensity_iff, huV.lintegral_perimeter_eq_setLIntegral_enorm_fderiv]
    exact hfin.ne
  have hmeq : volume.withDensity P = volume.withDensity H := by
    refine (volume.withDensity P).ext_of_Ico (volume.withDensity H) fun a b hab ↦ ?_
    rw [withDensity_apply _ measurableSet_Ico, withDensity_apply _ measurableSet_Ico]
    exact setLIntegral_Ico_perimeter_eq_euclideanHausdorffMeasure huV hab
  exact (withDensity_eq_iff_of_sigmaFinite hPm.aemeasurable hHm).1 hmeq

end PrivateHelpers

namespace LocallyLipschitzOn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E} {u : E → ℝ}

/-- **Superlevel perimeter of a locally Lipschitz function.** If `u : E → ℝ` is locally Lipschitz
on an open set `Ω`, then at almost every level `t ∈ ℝ` the variational perimeter of `{x | t < u x}`
in `Ω` equals the `(dim E - 1)`-dimensional Euclidean Hausdorff measure of `Ω ∩ u ⁻¹' {t}`. Neither
integrability nor finite total variation is required. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage
    (hu : LocallyLipschitzOn Ω u) :
    ∀ᵐ t : ℝ, TauCeti.perimeter volume Ω {x | t < u x} =
      μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ u ⁻¹' {t}) := by
  obtain ⟨V, hVc, hVΩ, hVmono, hVU, -⟩ := Ω.exists_monotone_isCompact_closure_iUnion_eq
  have hsup : (⨆ j, V j) = Ω := SetLike.coe_injective (by simp [hVU])
  filter_upwards [ae_all_iff.2 fun j ↦
    ae_perimeter_eq_euclideanHausdorffMeasure_of_isCompact_closure hu (hVc j) (hVΩ j)] with t ht
  have hH : μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ u ⁻¹' {t}) =
      ⨆ j, μHE[finrank ℝ E - 1] ((V j : Set E) ∩ u ⁻¹' {t}) := by
    have hunion : (Ω : Set E) ∩ u ⁻¹' {t} = ⋃ j, ((V j : Set E) ∩ u ⁻¹' {t}) := by
      rw [← iUnion_inter, hVU]
    rw [hunion]
    exact Monotone.measure_iUnion fun i j hij ↦ inter_subset_inter_left _ (hVmono hij)
  rw [hH, ← hsup, TauCeti.perimeter_iSup hVmono.directed_le]
  exact iSup_congr ht

end LocallyLipschitzOn

namespace LocallyLipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {u : E → ℝ}

/-- For a locally Lipschitz function `u : E → ℝ` and any open set `Ω`, at almost every level `t`
the perimeter of `{x | t < u x}` in `Ω` equals `μHE[dim E - 1] (Ω ∩ u ⁻¹' {t})`. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage
    (hu : LocallyLipschitz u) (Ω : Opens E) :
    ∀ᵐ t : ℝ, TauCeti.perimeter volume Ω {x | t < u x} =
      μHE[finrank ℝ E - 1] ((Ω : Set E) ∩ u ⁻¹' {t}) :=
  hu.locallyLipschitzOn.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage

/-- For a locally Lipschitz function `u : E → ℝ`, at almost every level `t` the whole-space
perimeter of `{x | t < u x}` equals `μHE[dim E - 1] (u ⁻¹' {t})`. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage
    (hu : LocallyLipschitz u) :
    ∀ᵐ t : ℝ, TauCeti.perimeter volume ⊤ {x | t < u x} =
      μHE[finrank ℝ E - 1] (u ⁻¹' {t}) := by
  simpa using hu.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_inter_preimage ⊤

end LocallyLipschitz

namespace LipschitzWith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {K : ℝ≥0} {u : E → ℝ}

/-- For a Lipschitz function `u : E → ℝ`, at almost every level `t` the whole-space perimeter of
`{x | t < u x}` equals `μHE[dim E - 1] (u ⁻¹' {t})`. -/
theorem ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage
    (hu : LipschitzWith K u) :
    ∀ᵐ t : ℝ, TauCeti.perimeter volume ⊤ {x | t < u x} =
      μHE[finrank ℝ E - 1] (u ⁻¹' {t}) :=
  hu.locallyLipschitz.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage

end LipschitzWith
