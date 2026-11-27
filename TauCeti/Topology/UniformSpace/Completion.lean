/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# Neighbourhoods, fibres and range of the map to the separated completion

The neighbourhood filter of a point of a uniform space is countably generated exactly when the
neighbourhood filter of its image in the separated completion is. Nothing is assumed of the space
beyond its uniformity — no separation, no completeness, no algebraic structure.

`TauCeti.Topology.Algebra.GroupCompletion` specialises this to the zero of a uniform
space with a zero, which is the form typeclass resolution consumes.

Two points of a uniform space have the same image in the separated completion exactly when they
are inseparable. Mathlib's `UniformSpace.Completion.coe_inj` is the case of a `T0Space`, where
inseparable points are equal; without separation the canonical map identifies precisely the
points that the separation quotient identifies. Consequently, completing a subsingleton space
yields a subsingleton, and completing a nontrivial `T0Space` yields a nontrivial space.

## Main results

* `UniformSpace.Completion.isCountablyGenerated_nhds_coe_iff`.
* `UniformSpace.Completion.coe_eq_coe_iff_inseparable`.
* `UniformSpace.Completion.instSubsingleton`, `UniformSpace.Completion.instNontrivial`.
* `TauCeti.range_coe_completion_eq_univ`: a complete uniform space maps onto its completion.
-/

public section

open Filter
open scoped Topology

namespace UniformSpace.Completion

/-- **Countable generation of `𝓝 x` is detected in the separated completion**: the neighbourhood
filter of a point is countably generated exactly when that of its image in the separated completion
is. -/
@[simp]
theorem isCountablyGenerated_nhds_coe_iff {α : Type*} [UniformSpace α] {x : α} :
    (𝓝 (x : Completion α)).IsCountablyGenerated ↔ (𝓝 x).IsCountablyGenerated := by
  refine ⟨fun _ ↦ isDenseInducing_coe.nhds_eq_comap x ▸ inferInstance, fun _ ↦ ?_⟩
  obtain ⟨V, hV⟩ := (𝓝 x).exists_antitone_basis
  exact (hV.toHasBasis.hasBasis_of_isDenseInducing isDenseInducing_coe).isCountablyGenerated

/-- Two points of a uniform space have the same image in the separated completion exactly when
they are inseparable. -/
theorem coe_eq_coe_iff_inseparable {α : Type*} [UniformSpace α] {a b : α} :
    (a : Completion α) = b ↔ Inseparable a b := by
  rw [← inseparable_iff_eq, isDenseInducing_coe.isInducing.inseparable_iff]

/-- The separated completion of a subsingleton uniform space is a subsingleton. -/
instance instSubsingleton {α : Type*} [UniformSpace α] [Subsingleton α] :
    Subsingleton (Completion α) :=
  ⟨fun u v ↦ Completion.induction_on₂ u v (isClosed_eq continuous_fst continuous_snd)
    fun a b ↦ congrArg _ (Subsingleton.elim a b)⟩

/-- The separated completion of a nontrivial `T0Space` uniform space is nontrivial. -/
instance instNontrivial {α : Type*} [UniformSpace α] [T0Space α] [Nontrivial α] :
    Nontrivial (Completion α) :=
  let ⟨a, b, hab⟩ := exists_pair_ne α; ⟨a, b, coe_inj.not.2 hab⟩

end UniformSpace.Completion

namespace TauCeti

/-- A complete space has no ideal boundary: every point of its completion comes from the
space. -/
@[simp]
theorem range_coe_completion_eq_univ {α : Type*} [UniformSpace α] [CompleteSpace α] :
    Set.range ((↑) : α → UniformSpace.Completion α) = Set.univ := by
  rw [← (UniformSpace.Completion.isUniformInducing_coe α).isComplete_range.isClosed.closure_eq]
  exact UniformSpace.Completion.denseRange_coe.closure_range

end TauCeti

end
