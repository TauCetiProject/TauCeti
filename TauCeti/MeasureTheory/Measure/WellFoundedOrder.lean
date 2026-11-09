/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Measures on a countable upward well-founded order are determined by their upper rays

Mathlib's `MeasureTheory.Measure.ext_of_Ici` says that a finite Borel measure on a second-countable
linear order is determined by its values on the closed upper rays `Set.Ici a`. On a countable
partial order with no infinite strictly ascending chains (`WellFoundedGT`), for instance any finite
partial order, no topology is needed, and neither is a total order: the ray `Set.Ici a` is the
point `a` together with the strictly larger points, so downward induction along the order recovers
the mass of every singleton from the masses of the rays, and a measure on a countable space with
measurable singletons is determined by its singletons.

The same downward induction shows that a family of finite measures on such an order, indexed by a
measurable space, is measurable into the Giry σ-algebra once its evaluations on the upper rays are
measurable.

The typical consumers are laws on finite lattices of finite graphs, where the mass of a ray is the
probability that a random graph contains a fixed pattern, and on products of such lattices.

## Main results

* `MeasureTheory.Measure.ext_of_Ici_of_wellFoundedGT` — two measures on a countable
  `WellFoundedGT` partial order with measurable singletons, the first of them finite, agree once
  they agree on every `Set.Ici a`;
* `Measurable.measure_of_Ici_of_wellFoundedGT` — a family of finite measures on such an order is
  measurable once each of its upper-ray evaluations is.
-/

public section

open MeasureTheory Set

variable {α : Type*} [Countable α] [PartialOrder α] [WellFoundedGT α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- Two measures on a countable partial order with no infinite strictly ascending chains and with
measurable singletons are equal if they agree on all closed upper rays `Set.Ici a` and the first is
finite. -/
theorem MeasureTheory.Measure.ext_of_Ici_of_wellFoundedGT (μ ν : Measure α)
    [IsFiniteMeasure μ] (h : ∀ a, μ (Ici a) = ν (Ici a)) : μ = ν := by
  refine Measure.ext_of_singleton fun a => ?_
  -- Downward induction: the ray at `a` is `a` together with the strictly larger points.
  induction a using WellFoundedGT.induction with
  | ind a ih =>
    -- The strictly larger points form a countable union of singletons, on which both agree.
    have hIoi : μ (Ioi a) = ν (Ioi a) := by
      rw [← μ.tsum_indicator_apply_singleton _ .of_discrete,
        ← ν.tsum_indicator_apply_singleton _ .of_discrete, indicator_congr fun c hc => ih c hc]
    have hsplit : ∀ ρ : Measure α, ρ (Ici a) = ρ {a} + ρ (Ioi a) := fun ρ => by
      rw [← Ioi_union_left, measure_union (disjoint_singleton_right.2 (lt_irrefl a))
        (measurableSet_singleton a), add_comm]
    have hadd := (hsplit μ).symm.trans ((h a).trans (hsplit ν))
    rwa [hIoi, ENNReal.add_left_inj (hIoi ▸ measure_ne_top μ _)] at hadd

/-- A family of finite measures on a countable partial order with no infinite strictly ascending
chains and with measurable singletons is measurable as soon as its value on every closed upper ray
`Set.Ici a` depends measurably on the parameter. -/
theorem Measurable.measure_of_Ici_of_wellFoundedGT {β : Type*} [MeasurableSpace β]
    {μ : β → Measure α} [∀ b, IsFiniteMeasure (μ b)]
    (h : ∀ a, Measurable fun b => μ b (Ici a)) : Measurable μ := by
  -- Every evaluation on a set is the countable sum of its singleton evaluations.
  have hsum (s : Set α) (hs : ∀ c ∈ s, Measurable fun b => μ b {c}) :
      Measurable fun b => μ b s := by
    simp_rw [← Measure.tsum_indicator_apply_singleton (μ _) s .of_discrete]
    refine Measurable.tsum fun c => ?_
    by_cases hc : c ∈ s <;> simp [hc, hs]
  -- Downward induction: the mass of `{a}` is the mass of the ray at `a` minus the masses of the
  -- singletons strictly above `a`.
  have hsingle : ∀ a, Measurable fun b => μ b {a} := by
    intro a
    induction a using WellFoundedGT.induction with
    | ind a ih =>
      have hsplit : ∀ b, μ b {a} = μ b (Ici a) - μ b (Ioi a) := fun b => by
        rw [← Ioi_union_left, measure_union (disjoint_singleton_right.2 (lt_irrefl a))
          (measurableSet_singleton a), ENNReal.add_sub_cancel_left (measure_ne_top _ _)]
      simp_rw [hsplit]
      exact (h a).sub (hsum _ ih)
  exact Measure.measurable_of_measurable_coe _ fun s _ => hsum s fun c _ => hsingle c
