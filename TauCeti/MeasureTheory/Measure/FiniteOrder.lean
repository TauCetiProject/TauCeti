/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Measures on a finite partial order are determined by their upper sets

Mathlib's `MeasureTheory.Measure.ext_of_Ici` says that a finite Borel measure on a second-countable
linear order is determined by its values on the closed upper rays `Set.Ici a`. On a *finite*
partial order no topology is needed, and neither is a total order: the ray `Set.Ici a` is the point
`a` together with the strictly larger points, so downward induction along the order recovers the
mass of every singleton from the masses of the rays, and a measure on a countable space with
measurable singletons is determined by its singletons.

The same downward induction shows that a family of finite measures on a finite partial order,
indexed by a measurable space, is measurable into the Giry σ-algebra once its evaluations on the
upper rays are measurable.

The typical consumers are laws on finite lattices of finite graphs, where the mass of a ray is the
probability that a random graph contains a fixed pattern, and on products of such lattices.

## Main results

* `MeasureTheory.Measure.ext_of_Ici_of_finite` — two measures on a finite partial order with
  measurable singletons, the first of them finite, agree once they agree on every `Set.Ici a`;
* `Measurable.measure_of_Ici_of_finite` — a family of finite measures on such an order is
  measurable once each of its upper-ray evaluations is.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {α : Type*} [Finite α] [PartialOrder α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Two measures on a finite partial order with measurable singletons are equal if they agree on
all closed upper rays `Set.Ici a` and the first is finite: the ray at `a` is `a` together with the
strictly larger points, so downward induction recovers the mass of every singleton. -/
theorem _root_.MeasureTheory.Measure.ext_of_Ici_of_finite (μ ν : Measure α) [IsFiniteMeasure μ]
    (h : ∀ a, μ (Ici a) = ν (Ici a)) : μ = ν := by
  refine Measure.ext_of_singleton fun a => ?_
  induction a using WellFoundedGT.induction with
  | ind a ih =>
    -- The strictly larger points form a finite union of singletons, on which both agree.
    have hIoi : μ (Ioi a) = ν (Ioi a) := by
      have hfin := (toFinite (Ioi a)).coe_toFinset
      rw [← hfin, ← sum_measure_singleton, ← sum_measure_singleton]
      exact Finset.sum_congr rfl fun b hb => ih b ((toFinite (Ioi a)).mem_toFinset.1 hb)
    have hsplit : ∀ ρ : Measure α, ρ (Ici a) = ρ {a} + ρ (Ioi a) := fun ρ => by
      rw [← Ioi_union_left, union_comm,
        measure_union' (s₂ := Ioi a) (disjoint_singleton_left.2 (lt_irrefl a))
          (measurableSet_singleton a)]
    have hne : μ (Ioi a) ≠ ⊤ := measure_ne_top μ _
    have hadd := (hsplit μ).symm.trans ((h a).trans (hsplit ν))
    rwa [hIoi, ENNReal.add_left_inj (hIoi ▸ hne)] at hadd

/-- A family of finite measures on a finite partial order with measurable singletons is measurable
as soon as its value on every closed upper ray `Set.Ici a` depends measurably on the parameter:
the mass of `{a}` is the mass of the ray at `a` minus the finitely many singleton masses strictly
above `a`, so downward induction makes every singleton evaluation measurable, and every set is a
finite union of singletons. -/
theorem _root_.Measurable.measure_of_Ici_of_finite {β : Type*} [MeasurableSpace β]
    {μ : β → Measure α} [∀ b, IsFiniteMeasure (μ b)]
    (h : ∀ a, Measurable fun b => μ b (Ici a)) : Measurable μ := by
  -- Every evaluation on a set is the finite sum of its singleton evaluations.
  have hsum : ∀ (s : Set α) (b : β), μ b s = ∑ c ∈ (toFinite s).toFinset, μ b {c} :=
    fun s b => by rw [sum_measure_singleton, (toFinite s).coe_toFinset]
  have hsingle : ∀ a, Measurable fun b => μ b {a} := by
    intro a
    induction a using WellFoundedGT.induction with
    | ind a ih =>
      have hIoi : Measurable fun b => μ b (Ioi a) := by
        simp_rw [hsum (Ioi a)]
        exact Finset.measurable_sum _ fun c hc => ih c ((toFinite (Ioi a)).mem_toFinset.1 hc)
      have hsplit : ∀ b, μ b {a} = μ b (Ici a) - μ b (Ioi a) := fun b => by
        rw [← Ioi_union_left, union_comm,
          measure_union' (s₂ := Ioi a) (disjoint_singleton_left.2 (lt_irrefl a))
            (measurableSet_singleton a),
          ENNReal.add_sub_cancel_right (measure_ne_top _ _)]
      simp_rw [hsplit]
      exact (h a).sub hIoi
  refine Measure.measurable_of_measurable_coe _ fun s _ => ?_
  simp_rw [hsum s]
  exact Finset.measurable_sum _ fun c _ => hsingle c

end TauCeti
