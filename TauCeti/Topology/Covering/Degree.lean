/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The locally constant degree of a covering

The cardinality of the fibres of a covering map is locally constant, including over a
disconnected base and at points with empty fibres. For finite fibres this is the number of
sheets. This supplies the variable degree in the transfer formula for singular homology.
For infinite fibres, `Nat.card` has its usual value zero; no finite-sheet interpretation is
asserted in that case.

The construction uses Mathlib's `IsEvenlyCovered.fiberHomeomorph`. See Hatcher,
*Algebraic Topology*, Sections 1.3 and 3.G, for covering degree and transfer.
-/

public section

namespace IsCoveringMap

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- Fibre cardinality is locally constant for a covering, without connectedness or
surjectivity assumptions. Infinite fibres have `Nat.card` equal to zero. -/
theorem isLocallyConstant_natCard_fiber (hp : IsCoveringMap p) :
    IsLocallyConstant (fun b ↦ Nat.card (p ⁻¹' {b})) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun b ↦ ?_
  obtain ⟨hdisc, U, hb, hU, hpU, H, hH⟩ := hp b
  refine ⟨U, hU, hb, fun b' hb' ↦ ?_⟩
  have h (y : B) (hy : y ∈ U) : IsEvenlyCovered p y (p ⁻¹' {b}) :=
    ⟨hdisc, U, hy, hU, hpU, H, hH⟩
  exact (Nat.card_congr (h b' hb').fiberHomeomorph.toEquiv).symm

/-- The locally constant fibre cardinality of a covering. For a finite covering this is its
number of sheets on each connected component of the base. -/
noncomputable def degree (hp : IsCoveringMap p) : LocallyConstant B ℕ :=
  ⟨fun b ↦ Nat.card (p ⁻¹' {b}), hp.isLocallyConstant_natCard_fiber⟩

/-- The degree at a point is the cardinality of its fibre. -/
@[simp]
lemma degree_apply (hp : IsCoveringMap p) (b : B) :
    hp.degree b = Nat.card (p ⁻¹' {b}) := (rfl)

end IsCoveringMap
