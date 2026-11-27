/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.MeasurableIntegral
import TauCeti.Probability.Kernel.Integral

/-!
# Integrating against measurable families of measures

A measurable family of measures need not be an s-finite kernel. When its slices have finite
mass almost everywhere for an outer measure, integrating a jointly measurable function gives
an almost everywhere measurable function of the parameter. The Bochner version applies to
jointly strongly measurable functions with values in any normed real vector space.

The outer measure is arbitrary, and the finite-mass hypothesis is only almost everywhere:
exceptional slices may have infinite mass. In particular, no uniform mass bound or integrability
of the total mass is required. These results apply to spatial integrals of measure-valued curves
without requiring a continuity equation.

For parameter-independent integrands `g : β → ℝ≥0∞` or `g : β → F`, neither Giry measurability of
`κ` nor almost-everywhere finiteness of `κ y` is required: if `y ↦ κ y t` is `ν`-almost everywhere
measurable on every measurable set `t`, then `y ↦ ∫⁻ x, g x ∂κ y` is `ν`-almost everywhere
measurable and `y ↦ ∫ x, g x ∂κ y` is `ν`-almost everywhere strongly measurable.

## Main results

* `Measurable.aemeasurable_lintegral_measure`: measurability of nonnegative integrals against a
  measurable family with almost everywhere finite slices.
* `MeasureTheory.StronglyMeasurable.aestronglyMeasurable_integral_measure`: strong measurability
  of Bochner integrals against such a family.
* `Measurable.aemeasurable_lintegral_of_aemeasurable_measure`,
  `MeasureTheory.StronglyMeasurable.aestronglyMeasurable_integral_of_aemeasurable_measure`:
  almost-everywhere (strong) measurability of integrals of fixed integrands against families of
  measures with almost-everywhere measurable set evaluations, without finiteness or σ-finiteness
  hypotheses.
-/

public section

open MeasureTheory ProbabilityTheory Set Function Filter
open scoped ENNReal

/-- Integrating a jointly measurable nonnegative function against a measurable family of measures
with almost everywhere finite slices gives an almost everywhere measurable function. -/
theorem Measurable.aemeasurable_lintegral_measure
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : α → Measure β}
    {ν : Measure α} {f : α → β → ℝ≥0∞} (hf : Measurable (uncurry f)) (hμ : Measurable μ)
    (hμfin : ∀ᵐ a ∂ν, μ a univ ≠ ∞) :
    AEMeasurable (fun a ↦ ∫⁻ x, f a x ∂μ a) ν := by
  have hm : Measurable fun a ↦ 1 + μ a univ :=
    measurable_const.add ((Measure.measurable_coe .univ).comp hμ)
  have hκ := hf.lintegral_kernel_prod_right (κ := (Kernel.mk μ hμ).normalize)
  refine (hm.mul hκ).aemeasurable.congr ?_
  filter_upwards [hμfin] with a ha
  simpa only [Pi.mul_apply, Kernel.coe_mk] using
    ((Kernel.mk μ hμ).lintegral_eq_mul_normalize ha (f a)).symm

/-- Integrating a jointly strongly measurable function against a measurable family of measures
with almost everywhere finite slices gives an almost everywhere strongly measurable function.
The codomain needs no measurable-space, separability or completeness assumptions. -/
theorem MeasureTheory.StronglyMeasurable.aestronglyMeasurable_integral_measure
    {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : α → Measure β} {ν : Measure α}
    {f : α → β → F} (hf : StronglyMeasurable (uncurry f)) (hμ : Measurable μ)
    (hμfin : ∀ᵐ a ∂ν, μ a univ ≠ ∞) :
    AEStronglyMeasurable (fun a ↦ ∫ x, f a x ∂μ a) ν := by
  have hm : Measurable fun a ↦ 1 + μ a univ :=
    measurable_const.add ((Measure.measurable_coe .univ).comp hμ)
  have hκ := hf.integral_kernel_prod_right (κ := (Kernel.mk μ hμ).normalize)
  refine (hm.ennreal_toReal.stronglyMeasurable.smul hκ).aestronglyMeasurable.congr ?_
  filter_upwards [hμfin] with a ha
  simpa only [Pi.smul_apply', Kernel.coe_mk] using
    ((Kernel.mk μ hμ).integral_eq_smul_normalize ha (f a)).symm

/-- Borel-measurable nonnegative integrands have `ν`-almost everywhere measurable integrals
against any family of measures `κ` with `ν`-almost everywhere measurable values on Borel sets. -/
theorem Measurable.aemeasurable_lintegral_of_aemeasurable_measure {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {κ : α → Measure β} {ν : Measure α} {g : β → ℝ≥0∞} (hg : Measurable g)
    (hκ : ∀ t, MeasurableSet t → AEMeasurable (fun y ↦ κ y t) ν) :
    AEMeasurable (fun y ↦ ∫⁻ x, g x ∂κ y) ν := by
  refine Measurable.ennreal_induction ?_ ?_ ?_ hg
  · intro c t ht
    simp_rw [lintegral_indicator_const ht]
    exact (hκ t ht).const_mul c
  · intro g h _ hg _ ihg ihh
    simp_rw [Pi.add_apply, lintegral_add_left hg]
    exact ihg.add ihh
  · intro g hg hmono ih
    have heq (y : α) : (∫⁻ x, ⨆ n, g n x ∂κ y) = ⨆ n, ∫⁻ x, g n x ∂κ y :=
      lintegral_iSup hg hmono
    simp_rw [heq]
    exact AEMeasurable.iSup ih

/-- Adapting `MeasureTheory.StronglyMeasurable.integral_kernel` in
`Mathlib.Probability.Kernel.MeasurableIntegral` from measurable kernels to families of measures
with `ν`-almost everywhere measurable evaluations on Borel sets: if `g : β → F` is strongly
measurable, then `y ↦ ∫ x, g x ∂κ y` is `ν`-almost everywhere strongly measurable. Neither
completeness of `F` nor σ-finiteness of `κ y` is assumed. -/
theorem MeasureTheory.StronglyMeasurable.aestronglyMeasurable_integral_of_aemeasurable_measure
    {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {κ : α → Measure β} {ν : Measure α} {g : β → F} (hg : StronglyMeasurable g)
    (hκ : ∀ t, MeasurableSet t → AEMeasurable (fun y ↦ κ y t) ν) :
    AEStronglyMeasurable (fun y ↦ ∫ x, g x ∂κ y) ν := by
  by_cases hF : CompleteSpace F; swap
  · simp [integral_of_not_completeSpace hF, aestronglyMeasurable_const]
  borelize F
  have : TopologicalSpace.SeparableSpace (range g ∪ {0} : Set F) :=
    hg.separableSpace_range_union_singleton
  let s : ℕ → SimpleFunc β F := SimpleFunc.approxOn _ hg.measurable (range g ∪ {0}) 0 (by simp)
  let g' (n : ℕ) : α → F := {y | Integrable g (κ y)}.indicator fun y ↦ (s n).integral (κ y)
  have hint_set : NullMeasurableSet {y | Integrable g (κ y)} ν := by
    simp_rw [Integrable, hg.aestronglyMeasurable, true_and, HasFiniteIntegral]
    exact (hg.eNorm.aemeasurable_lintegral_of_aemeasurable_measure hκ).nullMeasurable
      measurableSet_Iio
  refine aestronglyMeasurable_of_tendsto_ae (f := g') atTop (fun n ↦ ?_) (Eventually.of_forall ?_)
  · refine AEStronglyMeasurable.indicator₀ ?_ hint_set
    simp_rw [SimpleFunc.integral_eq]
    refine Finset.aestronglyMeasurable_fun_sum _ fun _ _ ↦ ?_
    exact (hκ _ ((s n).measurableSet_fiber _)).ennreal_toReal.aestronglyMeasurable.smul_const _
  · intro y
    by_cases hgy : Integrable g (κ y)
    · simp only [mem_ofPred_eq, hgy, indicator_of_mem, g']
      apply tendsto_integral_approxOn_of_measurable_of_range_subset _ hgy
      exact subset_rfl
    · simp [g', hgy, integral_undef]
