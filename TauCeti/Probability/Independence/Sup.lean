/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic
import TauCeti.MeasureTheory.MeasurableSpace.Sup

/-!
# Independence of a join of σ-algebras

If `m₁` is independent of `m` and `m₂` is independent of `m₁ ⊔ m`, then the join `m₁ ⊔ m₂` is
independent of `m`. The proof checks independence on the π-system of intersections generating the
join.

## Main declarations

* `ProbabilityTheory.Indep.sup_left`: if `m₁` is independent of `m` and `m₂` is independent of
  `m₁ ⊔ m`, then `m₁ ⊔ m₂` is independent of `m`.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- If `m₁` is independent of `m` and `m₂` is independent of `m₁ ⊔ m`, then the join `m₁ ⊔ m₂` is
independent of `m`. -/
theorem Indep.sup_left [IsZeroOrProbabilityMeasure μ] {m₁ m₂ m : MeasurableSpace Ω}
    (h₁ : Indep m₁ m μ) (h₂ : Indep m₂ (m₁ ⊔ m) μ) (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    (hm : m ≤ mΩ) : Indep (m₁ ⊔ m₂) m μ := by
  refine IndepSets.indep (sup_le hm₁ hm₂) hm
    (MeasurableSpace.isPiSystem_inter_measurableSet m₁ m₂)
    (@MeasurableSpace.isPiSystem_measurableSet Ω m)
    (MeasurableSpace.sup_eq_generateFrom_inter_measurableSet m₁ m₂)
    (@MeasurableSpace.generateFrom_measurableSet Ω m).symm ?_
  rw [IndepSets_iff]
  rintro _ c ⟨a, b, ha, hb, rfl⟩ hc
  have ha' : MeasurableSet[m₁ ⊔ m] a := le_sup_left (b := m) _ ha
  have hac : MeasurableSet[m₁ ⊔ m] (a ∩ c) := ha'.inter (le_sup_right (a := m₁) _ hc)
  have hset : a ∩ b ∩ c = b ∩ (a ∩ c) := by grind
  calc μ (a ∩ b ∩ c) = μ (b ∩ (a ∩ c)) := by rw [hset]
    -- `b ∈ m₂` is independent of `a ∩ c ∈ m₁ ⊔ m`
    _ = μ b * μ (a ∩ c) := (Indep_iff _ _ _).1 h₂ b _ hb hac
    -- `a ∈ m₁` is independent of `c ∈ m`
    _ = μ b * (μ a * μ c) := by rw [(Indep_iff _ _ _).1 h₁ a c ha hc]
    -- `b ∈ m₂` is independent of `a ∈ m₁ ⊔ m`
    _ = μ (b ∩ a) * μ c := by rw [(Indep_iff _ _ _).1 h₂ b a hb ha', mul_assoc]
    _ = μ (a ∩ b) * μ c := by rw [Set.inter_comm]

end ProbabilityTheory
