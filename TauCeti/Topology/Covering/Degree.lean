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
disconnected base and at points with empty fibres. This holds for the cardinal `Cardinal.mk` of
the fibre, and hence for `Nat.card`. For finite fibres the latter is the number of
sheets. This supplies the variable degree in the transfer formula for singular homology.
For infinite fibres, `Nat.card` has its usual value zero; no finite-sheet interpretation is
asserted in that case.

The construction uses Mathlib's `IsEvenlyCovered.fiberHomeomorph`. See Hatcher,
*Algebraic Topology*, Sections 1.3 and 3.G, for covering degree and transfer.
-/

public section

namespace IsCoveringMap

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- The cardinal of the fibres of a covering is locally constant, without connectedness or
surjectivity assumptions. Unlike `Nat.card`, this distinguishes the infinite fibres. -/
theorem isLocallyConstant_cardinalMk_fiber (hp : IsCoveringMap p) :
    IsLocallyConstant (fun b ↦ Cardinal.mk (p ⁻¹' {b})) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun b ↦ ?_
  obtain ⟨hdisc, U, hb, hU, hpU, H, hH⟩ := hp b
  refine ⟨U, hU, hb, fun b' hb' ↦ ?_⟩
  have h : IsEvenlyCovered p b' (p ⁻¹' {b}) := ⟨hdisc, U, hb', hU, hpU, H, hH⟩
  exact (Cardinal.mk_congr h.fiberHomeomorph.toEquiv).symm

/-- Finiteness of a covering fibre propagates throughout its connected component. -/
theorem finite_fiber_of_mem_connectedComponent (hp : IsCoveringMap p) {x y : B}
    (hxy : x ∈ connectedComponent y) (hfin : Finite (p ⁻¹' {y})) :
    Finite (p ⁻¹' {x}) := by
  apply Cardinal.mk_lt_aleph0_iff.mp
  rw [hp.isLocallyConstant_cardinalMk_fiber.apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hxy mem_connectedComponent]
  exact Cardinal.mk_lt_aleph0_iff.mpr hfin

/-- Fibre cardinality is locally constant for a covering, without connectedness or
surjectivity assumptions. Infinite fibres have `Nat.card` equal to zero. -/
theorem isLocallyConstant_natCard_fiber (hp : IsCoveringMap p) :
    IsLocallyConstant (fun b ↦ Nat.card (p ⁻¹' {b})) :=
  hp.isLocallyConstant_cardinalMk_fiber.comp Cardinal.toNat

/-- The locally constant fibre cardinality of a covering. For a finite covering this is its
number of sheets on each connected component of the base. -/
noncomputable def degree (hp : IsCoveringMap p) : LocallyConstant B ℕ :=
  ⟨fun b ↦ Nat.card (p ⁻¹' {b}), hp.isLocallyConstant_natCard_fiber⟩

/-- The degree at a point is the cardinality of its fibre. -/
@[simp]
lemma degree_apply (hp : IsCoveringMap p) (b : B) :
    hp.degree b = Nat.card (p ⁻¹' {b}) := (rfl)

end IsCoveringMap
