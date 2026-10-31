/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import TauCeti.MeasureTheory.Measure.AddContent

/-!
# Contents from functionals on bounded functions

On a discrete space, applying a linear functional to characteristic functions gives a real-valued
content on all subsets. It is nonnegative when the functional is positive, and its total mass is
the functional's value at one.
This construction is the forward direction of the correspondence between means and finitely
additive probabilities. It does not assert countable additivity.

We use Mathlib's bounded continuous characteristic functions, with a small API for clopen sets
that also applies without discreteness.

## References

* A. Garrido, *An introduction to amenable groups*, Theorem 1.15.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped BoundedContinuousFunction

namespace BoundedContinuousFunction

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[simp]
theorem indicator_empty : indicator (∅ : Set X) isClopen_empty = 0 := by
  ext x
  simp

@[simp]
theorem indicator_univ : indicator (univ : Set X) isClopen_univ = 1 := by
  ext x
  simp

/-- Characteristic functions add on disjoint clopen sets. -/
theorem indicator_union {s t : Set X} (hs : IsClopen s) (ht : IsClopen t)
    (hst : Disjoint s t) : indicator (s ∪ t) (hs.union ht) = indicator s hs + indicator t ht := by
  ext x
  simp only [indicator_apply, Set.indicator_union_of_disjoint hst, add_apply]

/-- A characteristic function is pointwise nonnegative. -/
theorem indicator_nonneg (s : Set X) (hs : IsClopen s) : 0 ≤ indicator s hs := by
  intro x
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- Pullback of a characteristic function is the characteristic function of the preimage. -/
@[simp]
theorem indicator_compContinuous (s : Set X) (hs : IsClopen s) (f : C(Y, X)) :
    (indicator s hs).compContinuous f = indicator (f ⁻¹' s) (hs.preimage f.continuous) := by
  ext x
  by_cases hx : f x ∈ s <;> simp [hx]

end BoundedContinuousFunction

namespace LinearMap

variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X]

/-- The real content obtained by evaluating a linear functional on characteristic functions. -/
def toAddContent (m : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : AddContent ℝ (univ : Set (Set X)) :=
  isSetRing_univ.addContent_of_union
    (fun s => m (BoundedContinuousFunction.indicator s (isClopen_discrete s)))
    (by simp) (by
      intro s _ t _ hst
      rw [BoundedContinuousFunction.indicator_union _ _ hst, map_add])

@[simp 900] -- Prefer normalization at the whole space to expanding the content.
theorem toAddContent_apply (m : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (s : Set X) :
    m.toAddContent s = m (BoundedContinuousFunction.indicator s (isClopen_discrete s)) :=
  (rfl)

@[simp]
theorem toAddContent_univ (m : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : m.toAddContent univ = m 1 := by
  simp

end LinearMap

namespace PositiveLinearMap

/-- The content of a positive functional is nonnegative. -/
theorem toAddContent_nonneg {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    (m : (X →ᵇ ℝ) →ₚ[ℝ] ℝ) (s : Set X) : 0 ≤ m.toLinearMap.toAddContent s :=
  m.map_nonneg (BoundedContinuousFunction.indicator_nonneg _ _)

end PositiveLinearMap
