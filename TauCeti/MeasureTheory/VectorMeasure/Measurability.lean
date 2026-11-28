/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Measurability of vector-measure evaluations

Strong measurability of a family of vector measures can be checked on a generating π-system
and the whole space. Applied to Mathlib's derivative vector measure of a BV path, this gives
strong measurability of every fixed-set evaluation from strong measurability of the path's
evaluations, without right-continuity assumptions.
-/

public section

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology

/-- Strong measurability of vector-measure evaluations extends from a generating π-system
and the whole space to every set, including nonmeasurable sets, on which vector measures vanish. -/
theorem MeasureTheory.VectorMeasure.stronglyMeasurable_apply_of_isPiSystem
    {Ω β E : Type*} [MeasurableSpace Ω] {mβ : MeasurableSpace β}
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [MetrizableSpace E]
    (μ : Ω → VectorMeasure β E) {S : Set (Set β)}
    (hgen : mβ = MeasurableSpace.generateFrom S) (hpi : IsPiSystem S)
    (huniv : StronglyMeasurable (fun ω => μ ω univ))
    (hS : ∀ s ∈ S, StronglyMeasurable (fun ω => μ ω s)) (s : Set β) :
    StronglyMeasurable (fun ω => μ ω s) := by
  by_cases hs : MeasurableSet s
  · induction s, hs using MeasurableSpace.induction_on_inter hgen hpi with
    | empty => simpa only [VectorMeasure.empty] using (stronglyMeasurable_const (b := (0 : E)))
    | basic s hs => exact hS s hs
    | compl s hs ih =>
      simp_rw [VectorMeasure.of_compl hs]
      exact huniv.fun_sub ih
    | iUnion f hfd hfm ih =>
      exact stronglyMeasurable_of_tendsto atTop
        (fun n => (Finset.stronglyMeasurable_fun_sum _ fun i _ => ih i))
        (tendsto_pi_nhds.mpr fun ω =>
          ((μ ω).hasSum_of_disjoint_iUnion hfm hfd).tendsto_sum_nat)
  · simp only [VectorMeasure.not_measurable _ hs]
    exact stronglyMeasurable_const

/-- Measurability of vector-measure evaluations in a second-countable Borel space extends from
a generating π-system and the whole space to every set, including nonmeasurable sets. -/
theorem MeasureTheory.VectorMeasure.measurable_apply_of_isPiSystem
    {Ω β E : Type*} [MeasurableSpace Ω] {mβ : MeasurableSpace β}
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [MetrizableSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Ω → VectorMeasure β E) {S : Set (Set β)}
    (hgen : mβ = MeasurableSpace.generateFrom S) (hpi : IsPiSystem S)
    (huniv : Measurable (fun ω => μ ω univ))
    (hS : ∀ s ∈ S, Measurable (fun ω => μ ω s)) (s : Set β) :
    Measurable (fun ω => μ ω s) :=
  (MeasureTheory.VectorMeasure.stronglyMeasurable_apply_of_isPiSystem μ hgen hpi
    huniv.stronglyMeasurable (fun s hs => (hS s hs).stronglyMeasurable) s).measurable

namespace BoundedVariationOn

variable {α Ω E : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [SecondCountableTopology α] [DenselyOrdered α] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [CompleteSpace E] {X : α → Ω → E}

variable [CompactIccSpace α] [MeasurableSpace α] [BorelSpace α]

/-- Fixed-set evaluations of the derivative vector measures of globally BV paths are strongly
measurable when every path evaluation is strongly measurable. Endpoints and unbounded domains
are allowed; no right continuity is required. -/
theorem stronglyMeasurable_vectorMeasure_apply
    (hX : ∀ t, StronglyMeasurable (X t))
    (hv : ∀ ω, BoundedVariationOn (fun t => X t ω) univ) (s : Set α) :
    StronglyMeasurable (fun ω => (hv ω).vectorMeasure s) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp only [eq_empty_of_isEmpty s, VectorMeasure.empty]
    exact stronglyMeasurable_const
  have htop : StronglyMeasurable (fun ω => limUnder atTop (fun t => X t ω)) :=
    stronglyMeasurable_of_tendsto (atTop : Filter α) hX
      (tendsto_pi_nhds.mpr fun ω => (hv ω).tendsto_atTop_limUnder)
  have hbot : StronglyMeasurable (fun ω => limUnder atBot (fun t => X t ω)) :=
    stronglyMeasurable_of_tendsto (atBot : Filter α) hX
      (tendsto_pi_nhds.mpr fun ω => (hv ω).tendsto_atBot_limUnder)
  have hright (z : α) : StronglyMeasurable (fun ω => (fun t => X t ω).rightLim z) := by
    by_cases hz : ∃ b, z < b
    · have : (𝓝[>] z).NeBot := nhdsGT_neBot_of_exists_gt hz
      exact stronglyMeasurable_of_tendsto (𝓝[>] z) hX
        (tendsto_pi_nhds.mpr fun ω => (hv ω).tendsto_rightLim z)
    · have hz' : IsTop z := fun t => le_of_not_gt (fun ht => hz ⟨t, ht⟩)
      simpa only [rightLim_eq_of_isTop hz'] using hX z
  apply VectorMeasure.stronglyMeasurable_apply_of_isPiSystem
    (fun ω => (hv ω).vectorMeasure)
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic α)) isPiSystem_Iic
  · simpa only [vectorMeasure_univ] using htop.fun_sub hbot
  · rintro _ ⟨z, rfl⟩
    simpa only [vectorMeasure_Iic] using (hright z).fun_sub hbot

/-- Fixed-set evaluations of derivative vector measures of globally BV paths in a
second-countable Borel space are measurable when every path evaluation is measurable. -/
theorem measurable_vectorMeasure_apply [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (hX : ∀ t, Measurable (X t))
    (hv : ∀ ω, BoundedVariationOn (fun t => X t ω) univ) (s : Set α) :
    Measurable (fun ω => (hv ω).vectorMeasure s) :=
  (stronglyMeasurable_vectorMeasure_apply (fun t => (hX t).stronglyMeasurable) hv s).measurable

end BoundedVariationOn
