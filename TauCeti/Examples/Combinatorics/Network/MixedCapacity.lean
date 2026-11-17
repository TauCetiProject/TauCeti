/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.MixedCapacity
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Mixed vertex and arrow capacity examples

Consider two routes from a source to a sink. One route passes through a vertex of capacity
`1 / 2`; the other is a direct arrow of capacity `1 / 3`. Sending both amounts gives a flow of
value `5 / 6`. The intermediate vertex together with the direct arrow is a mixed separator of the
same weight. Weak duality therefore certifies both objects as optimal, and neither part of the
separator is redundant.

The same network with every capacity set to zero exercises the boundary case: the zero flow and
the same genuinely mixed separator both have value and weight zero.
-/

namespace TauCeti.Examples.MixedCapacity

public section

open Finset

/-- The three arrows in the two-route mixed-capacity example. -/
inductive Hom : Fin 3 → Fin 3 → Type
  | sourceMiddle : Hom 0 1
  | middleSink : Hom 1 2
  | sourceSink : Hom 0 2
  deriving DecidableEq

instance {x y} : Subsingleton (Hom x y) := ⟨by
  intro e f
  cases e <;> cases f <;> rfl⟩

noncomputable instance {x y} : Fintype (Hom x y) := Fintype.ofFinite _

/-- The intermediate vertex has capacity `1 / 2`; terminal capacities are immaterial. -/
def vertexCapacity : Fin 3 → ℚ
  | 1 => 1 / 2
  | _ => 0

@[simp]
theorem vertexCapacity_apply (v : Fin 3) : vertexCapacity v = if v = 1 then 1 / 2 else 0 := by
  fin_cases v <;> simp [vertexCapacity]

private def sourceMiddlePath : ArrowWalk Hom 0 1 :=
  (ArrowWalk.nil 0).cons Hom.sourceMiddle

private def middleSinkPath : ArrowWalk Hom 1 2 :=
  (ArrowWalk.nil 1).cons Hom.middleSink

private def sourceSinkPath : ArrowWalk Hom 0 2 :=
  (ArrowWalk.nil 0).cons Hom.sourceSink

private def viaMiddlePath : ArrowWalk Hom 0 2 :=
  sourceMiddlePath.cons Hom.middleSink

/-- The arrow capacities, expressed as the sum of the three weighted one-arrow routes: `1 / 2`
on the two-arrow route and `1 / 3` on the direct route. -/
noncomputable def capacity : Assignment Hom ℚ :=
  walkAssignment sourceMiddlePath (1 / 2) +
    walkAssignment middleSinkPath (1 / 2) + walkAssignment sourceSinkPath (1 / 3)

@[simp]
theorem capacity_apply {x y : Fin 3} (e : Hom x y) :
    capacity e = match e with
      | .sourceMiddle | .middleSink => 1 / 2
      | .sourceSink => 1 / 3 := by
  cases e <;>
    norm_num [capacity, sourceMiddlePath, middleSinkPath, sourceSinkPath,
      walkAssignment_cons, walkAssignment_nil, Assignment.single_apply]

private theorem capacity_nonneg : 0 ≤ capacity := by
  exact add_nonneg
    (add_nonneg (walkAssignment_nonneg sourceMiddlePath (by norm_num))
      (walkAssignment_nonneg middleSinkPath (by norm_num)))
    (walkAssignment_nonneg sourceSinkPath (by norm_num))

/-- The feasible flow saturating both routes. -/
noncomputable def flow : Flow capacity 0 2 where
  toFun := capacity
  mem_Icc := ⟨capacity_nonneg, le_rfl⟩
  conserve v hv₀ hv₂ := by
    fin_cases v
    · exact (hv₀ rfl).elim
    · norm_num [capacity, excessAt_add, excessAt_walkAssignment]
    · exact (hv₂ rfl).elim
  excessAt_sink_nonneg := by
    norm_num [capacity, excessAt_add, excessAt_walkAssignment]

@[simp]
theorem flow_toFun : flow.toFun = capacity :=
  (rfl)

/-- The arrow part of the displayed separator, consisting of the direct source--sink arrow. -/
def separatorArrows : Finset (Σ v w, Hom v w) :=
  {⟨0, 2, Hom.sourceSink⟩}

@[simp]
theorem mem_separatorArrows {a : Σ v w, Hom v w} :
    a ∈ separatorArrows ↔ a = ⟨0, 2, Hom.sourceSink⟩ :=
  mem_singleton

/-- The intermediate vertex together with the direct arrow meets every source--sink walk. -/
theorem isMixedSeparator :
    IsMixedSeparator {1} separatorArrows 0 2 := by
  refine isMixedSeparator_iff.2 ⟨by decide, by decide, fun p ↦ ?_⟩
  cases p with
  | cons p e =>
      cases e with
      | middleSink =>
          exact .inl ⟨1, by simp [ArrowWalk.vertices, Quiver.Path.vertices_cons], by simp⟩
      | sourceSink =>
          exact .inr ⟨⟨0, 2, Hom.sourceSink⟩, by simp [ArrowWalk.arrows_cons], by
            simp [separatorArrows]⟩

/-- Removing the vertex part of the displayed separator leaves the two-arrow route intact. -/
theorem not_isMixedSeparator_without_vertex :
    ¬IsMixedSeparator ∅ separatorArrows 0 2 := by
  intro h
  simpa [viaMiddlePath, sourceMiddlePath, separatorArrows, ArrowWalk.arrows_cons] using
    h.exists_mem viaMiddlePath

/-- Removing the arrow part of the displayed separator leaves the direct route intact. -/
theorem not_isMixedSeparator_without_arrow :
    ¬IsMixedSeparator {1} (∅ : Finset (Σ v w, Hom v w)) 0 2 := by
  intro h
  simpa [sourceSinkPath, ArrowWalk.vertices, Quiver.Path.vertices_cons,
    ArrowWalk.arrows_cons] using h.exists_mem sourceSinkPath

/-- The explicit rational flow respects the intermediate vertex capacity. -/
theorem flow_respectsVertexCapacity : flow.RespectsVertexCapacity vertexCapacity := by
  rw [Flow.respectsVertexCapacity_iff]
  intro v hv₀ hv₂
  fin_cases v
  · exact (hv₀ rfl).elim
  · rw [flow_toFun, capacity, arrowSum_add, arrowSum_add,
      arrowSum_walkAssignment_univ_singleton,
      arrowSum_walkAssignment_univ_singleton,
      arrowSum_walkAssignment_univ_singleton]
    norm_num [vertexCapacity, sourceMiddlePath, middleSinkPath,
      sourceSinkPath, ArrowWalk.vertices, Quiver.Path.vertices_cons]
  · exact (hv₂ rfl).elim

/-- The explicit flow has value `5 / 6`. -/
theorem flow_val : flow.val = 5 / 6 := by
  norm_num [BoundedFlow.val_def, flow, capacity, excessAt_add, excessAt_walkAssignment]

/-- The displayed mixed separator has the same weight `5 / 6` as the flow. -/
theorem separator_weight :
    ∑ v ∈ ({1} : Finset (Fin 3)), vertexCapacity v +
        ∑ a ∈ separatorArrows, capacity a.2.2 = 5 / 6 := by
  norm_num [vertexCapacity, separatorArrows]

/-- The rational example has an optimal mixed separator using both a vertex and an arrow.
Every capacity-respecting flow has value at most `5 / 6`, and the displayed flow attains it. -/
theorem rational_optimal_mixed_separator :
    ({1} : Finset (Fin 3)).Nonempty ∧ separatorArrows.Nonempty ∧
      ¬IsMixedSeparator ∅ separatorArrows 0 2 ∧
      ¬IsMixedSeparator {1} (∅ : Finset (Σ v w, Hom v w)) 0 2 ∧
      flow.RespectsVertexCapacity vertexCapacity ∧ flow.val = 5 / 6 ∧
      ∀ g : Flow capacity 0 2, g.RespectsVertexCapacity vertexCapacity → g.val ≤ 5 / 6 := by
  refine ⟨by simp, by simp [separatorArrows], not_isMixedSeparator_without_vertex,
    not_isMixedSeparator_without_arrow, flow_respectsVertexCapacity, flow_val, fun g hg ↦ ?_⟩
  rw [← separator_weight]
  exact hg.val_le isMixedSeparator

/-- With all capacities zero, the zero flow and the same mixed separator attain the common
value and weight zero. -/
theorem zero_capacity_optimal_mixed_separator :
    ∃ f : Flow (0 : Assignment Hom ℚ) 0 2,
    f.RespectsVertexCapacity (0 : Fin 3 → ℚ) ∧ f.val = 0 ∧
      IsMixedSeparator {1} separatorArrows 0 2 ∧
      ∑ v ∈ ({1} : Finset (Fin 3)), (0 : Fin 3 → ℚ) v +
        ∑ a ∈ separatorArrows, (0 : Assignment Hom ℚ) a.2.2 = 0 ∧
      ∀ g : Flow (0 : Assignment Hom ℚ) 0 2,
        g.RespectsVertexCapacity (0 : Fin 3 → ℚ) → g.val = 0 := by
  let hzero : 0 ≤ (0 : Assignment Hom ℚ) := fun _ _ _ ↦ le_rfl
  refine ⟨Flow.zero hzero, ?_, Flow.val_zero hzero, isMixedSeparator, by simp, fun g hg ↦ ?_⟩
  · rw [Flow.respectsVertexCapacity_iff]
    intro v _ _
    rw [Flow.zero_toFun, arrowSum_zero]
    exact le_rfl
  · exact le_antisymm (by simpa using hg.val_le isMixedSeparator) g.val_nonneg

end

end TauCeti.Examples.MixedCapacity
