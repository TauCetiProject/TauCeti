/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import TauCeti.MeasureTheory.Measure.Typeclasses.Finite
-- Non-public: measurability of the sections `ν.map (Prod.mk a)` is used only inside a proof.
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measurability of measure-valued maps

This file supplies general-purpose measurability results for maps into the Giry measurable space
of measures.

## Main results

* `Measurable.measure_of_isPiSystem_of_iUnion` — measurability on a generating π-system
  suffices for measures finite on a fixed increasing exhaustion by π-system sets, without
  finite total mass.
* `TauCeti.MeasureTheory.measurable_sum_smul_dirac` — a countable mixture of Dirac measures at
  fixed atoms is measurable when each weight is measurable.
* `TauCeti.MeasureTheory.measurable_probabilityMeasure_map` — pushing forward along a fixed
  measurable map is measurable on `ProbabilityMeasure`.
* `TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry` — pushing a fixed s-finite measure
  forward along a jointly measurable family of maps is measurable in the parameter.
* `TauCeti.MeasureTheory.measurable_map_finiteMeasure_of_measurable_uncurry` — jointly varying a
  finite measure and the map that pushes it forward is measurable, with a probability-measure
  specialization.
* `MeasureTheory.measurableSet_isLocallyFiniteMeasure` and
  `MeasureTheory.measurableSet_isFiniteMeasureOnCompacts` — local finiteness is a measurable
  condition on measures on a locally compact, sigma-compact Hausdorff space.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

/-- A countable mixture of Dirac measures at fixed atoms `g i` is measurable in the weights.

Evaluating on a measurable set turns the measure into the sum
`∑' i, f b i * 1_{g i ∈ s}`, and a `tsum` of measurable functions is measurable. The atoms are
indexed by a countable type of their own, so the ambient space `α` may be uncountable. -/
theorem measurable_sum_smul_dirac {β ι α : Type*} [MeasurableSpace β] [MeasurableSpace α]
    [Countable ι] {f : β → ι → ℝ≥0∞} {g : ι → α}
    (hf : ∀ i, Measurable fun b => f b i) :
    Measurable fun b => Measure.sum fun i => f b i • Measure.dirac (g i) := by
  refine Measure.measurable_measure.2 fun s hs => ?_
  simp only [Measure.sum_apply _ hs, _root_.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  exact Measurable.tsum fun i => (hf i).mul_const _

/-- Pushing a probability measure forward along a fixed measurable map is measurable for the Giry
structure that `ProbabilityMeasure` inherits as a subtype of `Measure`. -/
theorem measurable_probabilityMeasure_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) :
    Measurable fun P : ProbabilityMeasure α => P.map f :=
  ((Measure.measurable_map f hf).comp measurable_subtype_coe).subtype_mk

/-- Pushing a fixed s-finite measure forward along a jointly measurable family of maps `f a` is
measurable in the parameter `a`. -/
theorem measurable_map_of_measurable_uncurry {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] {ν : Measure β} [SFinite ν] {f : α → β → γ}
    (hf : Measurable (Function.uncurry f)) :
    Measurable fun a => ν.map (f a) := by
  -- `ν.map (f a)` is the pushforward along `uncurry f` of the section `ν.map (Prod.mk a)`.
  have hsec : (fun a => ν.map (f a)) = fun a => (ν.map (Prod.mk a)).map (Function.uncurry f) :=
    funext fun a => (Measure.map_map hf measurable_prodMk_left).symm
  rw [hsec]
  exact (Measure.measurable_map _ hf).comp Measurable.map_prodMk_left

/-- Pushing a finite measure forward along a jointly measurable family of maps is jointly
measurable in the measure and the parameter.

This complements `Measure.measurable_map`, where the map is fixed, and
`measurable_map_of_measurable_uncurry`, where the measure is fixed. -/
theorem measurable_map_finiteMeasure_of_measurable_uncurry
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : γ → α → β} (hf : Measurable (Function.uncurry f)) :
    Measurable fun p : FiniteMeasure α × γ => (p.1 : Measure α).map (f p.2) := by
  let diracFinite (c : γ) : FiniteMeasure γ := ⟨Measure.dirac c, inferInstance⟩
  have hdirac : Measurable diracFinite := by
    exact Measure.measurable_dirac.subtype_mk
  have hprod : Measurable fun p : FiniteMeasure α × γ =>
      (Measure.dirac p.2).prod (p.1 : Measure α) := by
    exact FiniteMeasure.measurable_fun_prod.comp
      ((hdirac.comp measurable_snd).prodMk measurable_fst)
  have hmap : Measurable fun p : FiniteMeasure α × γ =>
      ((Measure.dirac p.2).prod (p.1 : Measure α)).map (Function.uncurry f) :=
    (Measure.measurable_map _ hf).comp hprod
  convert hmap using 1
  funext p
  rw [Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
  rfl

/-- The probability-measure specialization of
`measurable_map_finiteMeasure_of_measurable_uncurry`. -/
theorem measurable_probabilityMeasure_map_of_measurable_uncurry
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : γ → α → β} (hf : Measurable (Function.uncurry f)) :
    Measurable fun p : ProbabilityMeasure α × γ => p.1.map (f p.2) := by
  have htoFinite : Measurable fun μ : ProbabilityMeasure α => μ.toFiniteMeasure := by
    exact measurable_subtype_coe.subtype_mk
  exact ((measurable_map_finiteMeasure_of_measurable_uncurry hf).comp
    (htoFinite.comp measurable_fst |>.prodMk measurable_snd)).subtype_mk

end MeasureTheory

end TauCeti

open Set

/-- Measurability on a generating π-system suffices for a family of measures finite on a
fixed increasing exhaustion from that π-system. The measures need not have finite total mass.
This extends `Measurable.measure_of_isPiSystem` by restricting to each exhaustion set. -/
theorem Measurable.measure_of_isPiSystem_of_iUnion
    {α β : Type*} [MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ : α → Measure β} {C : Set (Set β)} {B : ℕ → Set β}
    (hgen : mβ = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C)
    (hB : ∀ n, B n ∈ C) (hmono : Monotone B) (hcover : ⋃ n, B n = univ)
    (hfinite : ∀ a n, μ a (B n) ≠ ∞)
    (hbasic : ∀ s ∈ C, Measurable fun a ↦ μ a s) : Measurable μ := by
  have hmeas (s : Set β) (hs : s ∈ C) : MeasurableSet s :=
    hgen ▸ MeasurableSpace.measurableSet_generateFrom hs
  have hrestrict (n : ℕ) : Measurable fun a ↦ (μ a).restrict (B n) := by
    have (a : α) : IsFiniteMeasure ((μ a).restrict (B n)) :=
      isFiniteMeasure_restrict.mpr (hfinite a n)
    refine Measurable.measure_of_isPiSystem hgen hpi (fun s hs ↦ ?_) ?_
    · simp_rw [Measure.restrict_apply (hmeas s hs)]
      rcases (s ∩ B n).eq_empty_or_nonempty with h | h
      · simp [h]
      · exact hbasic _ (hpi s hs (B n) (hB n) h)
    · simpa using hbasic _ (hB n)
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  have heq : (fun a ↦ μ a s) = fun a ↦ ⨆ n, (μ a).restrict (B n) s := by
    funext a
    rw [← Measure.restrict_iUnion_apply_eq_iSup hmono.directed_le hs, hcover,
      Measure.restrict_univ]
  rw [heq]
  exact Measurable.iSup fun n ↦ (Measure.measurable_coe hs).comp (hrestrict n)

namespace MeasureTheory

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [T2Space X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]

omit [T2Space X] in
/-- Local finiteness is a measurable condition in the evaluation sigma-algebra on measures. -/
theorem measurableSet_isLocallyFiniteMeasure :
    MeasurableSet {μ : Measure X | IsLocallyFiniteMeasure μ} := by
  let K := CompactExhaustion.choice X
  -- The compact sets of an exhaustion need not be measurable, but their interiors are.
  have h : {μ : Measure X | IsLocallyFiniteMeasure μ} = ⋂ n, {μ | μ (interior (K n)) < ∞} := by
    ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun _ n ↦ (measure_mono interior_subset).trans_lt (K.isCompact n).measure_lt_top,
      fun h ↦ ⟨fun x ↦ ?_⟩⟩
    obtain ⟨n, hn⟩ := K.exists_mem_nhds x
    exact ⟨interior (K n), interior_mem_nhds.2 hn, h n⟩
  rw [h]
  exact MeasurableSet.iInter fun n ↦
    measurableSet_lt (Measure.measurable_coe isOpen_interior.measurableSet) measurable_const

/-- Finiteness on compact sets is measurable in the evaluation sigma-algebra on measures. -/
theorem measurableSet_isFiniteMeasureOnCompacts :
    MeasurableSet {μ : Measure X | IsFiniteMeasureOnCompacts μ} := by
  let K := CompactExhaustion.choice X
  simp_rw [K.isFiniteMeasureOnCompacts_iff]
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun n =>
    measurableSet_lt (Measure.measurable_coe (K.isCompact n).measurableSet) measurable_const

end MeasureTheory
