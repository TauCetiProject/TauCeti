/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Counting measure on discrete spaces

Counting measure is finite on compact sets, outer regular, inner regular, and regular in a
discrete space with measurable singletons. On a discrete group it is therefore both a regular and
an inner regular Haar measure. These instances allow regular representations and `L¹` convolution
algebras on counting-measure `Lᵖ` spaces without a countability assumption.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

/-- Counting measure gives positive mass to every nonempty open set. -/
instance count_isOpenPosMeasure : (count : Measure X).IsOpenPosMeasure where
  open_pos _ _ hs := count_ne_zero hs

/-- Every measure on a discrete space is outer regular, since every subset is open. -/
instance outerRegular_of_discreteTopology [DiscreteTopology X] (μ : Measure X) :
    μ.OuterRegular where
  outerRegular s _ _ hr := ⟨s, Set.Subset.rfl, isOpen_discrete s, hr⟩

section MeasurableSingletonClass

variable [MeasurableSingletonClass X]

/-- Any strict lower bound for the counting measure of a set `s` is exceeded on a finite (hence
compact) subset of `s`. -/
theorem exists_isCompact_lt_count {s : Set X} {r : ℝ≥0∞} (hr : r < count s) :
    ∃ K ⊆ s, IsCompact K ∧ r < count K := by
  by_cases hs : s.Finite
  · exact ⟨s, Set.Subset.rfl, hs.isCompact, hr⟩
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hr.ne_top
    obtain ⟨t, hts, hcard⟩ := (Set.not_finite.mp hs).exists_subset_card_eq n
    refine ⟨t, hts, t.finite_toSet.isCompact, hn.trans_le ?_⟩
    rw [count_apply_finset, hcard]

/-- Counting measure is inner regular in any topological space with measurable singletons, since
every finite subset is compact. -/
instance count_innerRegular : (count : Measure X).InnerRegular where
  innerRegular _ _ _ hr := exists_isCompact_lt_count hr

/-- Counting measure is inner regular on sets of finite measure in any topological space with
measurable singletons. -/
instance count_innerRegularCompactLTTop : (count : Measure X).InnerRegularCompactLTTop :=
  inferInstance

variable [DiscreteTopology X]

/-- Compact sets in a discrete space have finite counting measure. -/
instance count_isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts (count : Measure X) where
  lt_top_of_isCompact _ hs := count_apply_lt_top.mpr hs.finite_of_discrete

/-- Counting measure is regular in a discrete space with measurable singletons. -/
instance count_regular : (count : Measure X).Regular where
  innerRegular _ _ _ hr := exists_isCompact_lt_count hr

/-- Counting measure is a Haar measure on a discrete group. -/
instance count_isHaarMeasure [Group X] [MeasurableMul X] :
    (count : Measure X).IsHaarMeasure where

end MeasurableSingletonClass

end MeasureTheory.Measure
