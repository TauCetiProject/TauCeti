/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Infima of a lower semicontinuous function over a compact factor

A lower semicontinuous function on a nonempty compact space attains its infimum, and the partial
infimum `y ↦ ⨅ x, f (x, y)` of a jointly lower semicontinuous function over a compact first factor
is again lower semicontinuous.

The first statement is recorded as an equation for the infimum rather than as `IsMinOn`, the form
in which an infimum is rewritten to a value of `f`; attainment is also what turns a strict lower
bound valid at every point of the compact factor into a strict lower bound for the infimum itself.
Only lower semicontinuity of `f` is used, so no continuity, metrizability or countability
hypothesis appears. The order `β` carries no topology of its own and need only be conditionally
complete, so real-valued functions are covered as well as extended-real ones.

Mathlib has `LowerSemicontinuousOn.exists_isMinOn`, the extreme value theorem for lower
semicontinuous functions, but nothing about infima over a compact factor of a product: its
semicontinuity operations combine functions on a fixed domain, and the corresponding
`lowerSemicontinuous_iInf` is false without compactness: arbitrary infima do not preserve lower
semicontinuity. What an infimum does preserve is upper semicontinuity, of upper semicontinuous
and in particular of continuous functions, which is `upperSemicontinuous_iInf`.

## Main results

* `LowerSemicontinuous.exists_iInf_eq`: on a nonempty compact space, a lower
  semicontinuous function attains its infimum.
* `LowerSemicontinuous.iInf_of_compactSpace`: the partial infimum of a jointly lower
  semicontinuous function over a compact first factor is lower semicontinuous.
-/

public section

open Set

variable {X Y β : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ConditionallyCompleteLinearOrder β]

namespace LowerSemicontinuous

/-- A lower semicontinuous function on a nonempty compact space attains its infimum. -/
theorem exists_iInf_eq [CompactSpace X] [Nonempty X] {f : X → β}
    (hf : LowerSemicontinuous f) : ∃ x₀, ⨅ x, f x = f x₀ := by
  obtain ⟨x₀, -, hx₀⟩ :=
    (hf.lowerSemicontinuousOn univ).exists_isMinOn univ_nonempty isCompact_univ
  exact ⟨x₀, (Equiv.Set.univ X).iInf_comp.symm.trans (hx₀.iInf_eq (mem_univ x₀))⟩

/-- The infimum of a jointly lower semicontinuous function over a compact first factor is a lower
semicontinuous function of the second variable.

Compactness is what makes this true: an arbitrary infimum of lower semicontinuous functions need
not be lower semicontinuous. -/
theorem iInf_of_compactSpace [CompactSpace X] {f : X × Y → β}
    (hf : LowerSemicontinuous f) : LowerSemicontinuous fun y => ⨅ x, f (x, y) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simpa only [iInf_of_isEmpty] using lowerSemicontinuous_const
  intro y₀ b hb
  -- `f` is bounded below on the compact slice `X × {y₀}`, so its infimum there bounds it.
  have : Nonempty β := ⟨b⟩
  have hbdd : BddBelow (range fun x => f (x, y₀)) :=
    image_univ ▸ ((hf.comp (Continuous.prodMk_left y₀)).lowerSemicontinuousOn
      univ).bddBelow_of_isCompact isCompact_univ
  -- Hence the strict lower bound `b` holds on the whole compact slice.
  have hsub : (univ : Set X) ×ˢ ({y₀} : Set Y) ⊆ f ⁻¹' Ioi b := by
    rintro ⟨x, y⟩ ⟨-, rfl : y = y₀⟩
    exact hb.trans_le (ciInf_le hbdd x)
  obtain ⟨u, v, -, hv, hu, hy₀v, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton (hf.isOpen_preimage b) hsub
  refine Filter.eventually_of_mem (hv.mem_nhds (hy₀v rfl)) fun y hy => ?_
  -- The bound holds at every point of the slice over `y`, and the infimum there is attained.
  obtain ⟨x₀, hx₀⟩ := (hf.comp (Continuous.prodMk_left y)).exists_iInf_eq
  exact (huv ⟨hu (mem_univ x₀), hy⟩).trans_le hx₀.ge

end LowerSemicontinuous
