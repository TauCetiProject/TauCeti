/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Closed constraints in optimal transport

An infinite barrier charges zero on an allowed set of pairs and infinity elsewhere. Its
integral vanishes exactly for plans concentrated on the allowed set. Because each plan costs
either zero or infinity, the transport value is zero exactly when a constrained coupling
exists, and infinity otherwise. This remains valid for arbitrary measures and measurable
constraints. A closed constraint also gives a lower semicontinuous cost.

The cost formula for an individual plan and the feasibility characterization require only
measurability of the constraint; topology enters only in the lower semicontinuity lemma.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*}

/-- The infinite barrier for a set of allowed source-target pairs. -/
def transportConstraintCost (C : Set (X × Y)) : X × Y → ℝ≥0∞ :=
  Cᶜ.indicator fun _ ↦ ∞

@[simp]
theorem transportConstraintCost_of_mem {C : Set (X × Y)} {z : X × Y} (hz : z ∈ C) :
    transportConstraintCost C z = 0 := by
  simp [transportConstraintCost, hz]

@[simp]
theorem transportConstraintCost_of_not_mem {C : Set (X × Y)} {z : X × Y} (hz : z ∉ C) :
    transportConstraintCost C z = ∞ := by
  simp [transportConstraintCost, hz]

variable [MeasurableSpace X] [MeasurableSpace Y]

/-- A barrier cost is measurable when the allowed pairs form a measurable set. -/
theorem measurable_transportConstraintCost {C : Set (X × Y)} (hC : MeasurableSet C) :
    Measurable (transportConstraintCost C) :=
  measurable_const.indicator hC.compl

/-- Integrating the infinite barrier records precisely the mass outside the constraint. -/
theorem lintegral_transportConstraintCost {C : Set (X × Y)} (hC : MeasurableSet C)
    (π : Measure (X × Y)) :
    ∫⁻ z, transportConstraintCost C z ∂π = ∞ * π Cᶜ := by
  exact lintegral_indicator_const hC.compl ∞

/-- A plan has zero barrier cost exactly when it is concentrated on the allowed pairs. -/
theorem lintegral_transportConstraintCost_eq_zero_iff {C : Set (X × Y)}
    (hC : MeasurableSet C) (π : Measure (X × Y)) :
    (∫⁻ z, transportConstraintCost C z ∂π) = 0 ↔ π Cᶜ = 0 := by
  rw [lintegral_transportConstraintCost hC]
  simp

/-- A barrier plan has infinite cost as soon as it violates the constraint on positive mass. -/
theorem lintegral_transportConstraintCost_eq_top_iff {C : Set (X × Y)}
    (hC : MeasurableSet C) (π : Measure (X × Y)) :
    (∫⁻ z, transportConstraintCost C z ∂π) = ∞ ↔ π Cᶜ ≠ 0 := by
  rw [lintegral_transportConstraintCost hC]
  simp [ENNReal.top_mul']

/-- A measurable set of pairs supports a coupling exactly when its barrier transport cost is zero.
No topological or probability assumptions are needed. -/
theorem transportCost_transportConstraintCost_eq_zero_iff {C : Set (X × Y)}
    (hC : MeasurableSet C)
    {μ : Measure X} {ν : Measure Y} :
    transportCost (transportConstraintCost C) μ ν = 0 ↔
      ∃ π : Measure (X × Y), IsCoupling π μ ν ∧ π Cᶜ = 0 := by
  constructor
  · intro h
    obtain ⟨π, hπ, hπcost⟩ := transportCost_lt_iff.1 (by rw [h]; exact zero_lt_one)
    refine ⟨π, hπ, ?_⟩
    by_contra hπC
    have htop := (lintegral_transportConstraintCost_eq_top_iff hC π).2 hπC
    exact not_lt_of_ge (htop.symm.le) (hπcost.trans ENNReal.one_lt_top)
  · rintro ⟨π, hπ, hπC⟩
    exact nonpos_iff_eq_zero.1 <|
      (transportCost_le_lintegral hπ _).trans_eq
        ((lintegral_transportConstraintCost_eq_zero_iff hC π).2 hπC)

/-- The barrier transport value is infinite precisely when the constraint is infeasible. -/
theorem transportCost_transportConstraintCost_eq_top_iff {C : Set (X × Y)}
    (hC : MeasurableSet C)
    {μ : Measure X} {ν : Measure Y} :
    transportCost (transportConstraintCost C) μ ν = ∞ ↔
      ¬∃ π : Measure (X × Y), IsCoupling π μ ν ∧ π Cᶜ = 0 := by
  constructor
  · intro h hπ
    have hz := (transportCost_transportConstraintCost_eq_zero_iff hC).2 hπ
    exact ENNReal.zero_ne_top (hz.symm.trans h)
  · intro h
    by_contra htop
    obtain ⟨π, hπ, hπcost⟩ := transportCost_lt_iff.1 (lt_top_iff_ne_top.2 htop)
    have hπC : π Cᶜ = 0 := by
      by_contra hπC
      have hcost := (lintegral_transportConstraintCost_eq_top_iff hC π).2 hπC
      exact not_lt_of_ge (hcost.symm.le) hπcost
    exact h ⟨π, hπ, hπC⟩

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- A closed constraint has a lower semicontinuous infinite barrier. -/
theorem lowerSemicontinuous_transportConstraintCost [TopologicalSpace X]
    [TopologicalSpace Y] {C : Set (X × Y)} (hC : IsClosed C) :
    LowerSemicontinuous (transportConstraintCost C) :=
  hC.isOpen_compl.lowerSemicontinuous_indicator bot_le

end TauCeti
