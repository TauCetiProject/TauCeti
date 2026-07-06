/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.SmallGridDifferential
public import TauCeti.KnotTheory.Grid.ChainCardinality
public import Mathlib.Algebra.Module.Submodule.Range

/-!
# Cycles and boundaries for the fully blocked grid differential

This file packages the kernel and range of the fully blocked grid differential as the cycle
and boundary submodules of the finite free grid chain module. It does not assert the global
square-zero theorem; instead it records the exact condition under which boundaries are cycles,
and computes the cycle and boundary submodules in the already-proved zero-differential small-grid
case.

## Main results

* `TauCeti.GridDiagram.fullyBlockedCycles`: the kernel of the fully blocked differential.
* `TauCeti.GridDiagram.fullyBlockedBoundaries`: the range of the fully blocked differential.
* `TauCeti.GridDiagram.fullyBlockedBoundaries_le_cycles`: boundaries lie in cycles whenever the
  fully blocked differential squares to zero.
* `TauCeti.GridDiagram.fullyBlockedCycles_eq_top_of_le_two` and
  `TauCeti.GridDiagram.fullyBlockedBoundaries_eq_bot_of_le_two`: the small-grid computation.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane G.3, "The complexes and `∂² = 0`", and for the acceptance criterion that the `2 × 2`
unknot grid complex be explicitly computable with its bigradings. The terminology follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The cycles of the fully blocked grid differential: chains killed by `∂`. -/
noncomputable def fullyBlockedCycles : Submodule (ZMod 2) (GridChain (ZMod 2) n) :=
  LinearMap.ker G.fullyBlockedDifferential

/-- The boundaries of the fully blocked grid differential: chains hit by `∂`. -/
noncomputable def fullyBlockedBoundaries : Submodule (ZMod 2) (GridChain (ZMod 2) n) :=
  LinearMap.range G.fullyBlockedDifferential

/-- A chain is a fully blocked cycle exactly when its differential vanishes. -/
@[simp]
theorem mem_fullyBlockedCycles (c : GridChain (ZMod 2) n) :
    c ∈ G.fullyBlockedCycles ↔ G.fullyBlockedDifferential c = 0 :=
  by
    rw [fullyBlockedCycles]
    exact LinearMap.mem_ker

/-- A chain is a fully blocked boundary exactly when it is the differential of some chain. -/
@[simp]
theorem mem_fullyBlockedBoundaries (c : GridChain (ZMod 2) n) :
    c ∈ G.fullyBlockedBoundaries ↔
      ∃ b : GridChain (ZMod 2) n, G.fullyBlockedDifferential b = c :=
  by
    rw [fullyBlockedBoundaries]
    exact LinearMap.mem_range

/-- The zero chain is a fully blocked cycle. -/
theorem zero_mem_fullyBlockedCycles : (0 : GridChain (ZMod 2) n) ∈ G.fullyBlockedCycles := by
  simp [fullyBlockedCycles]

/-- The zero chain is a fully blocked boundary. -/
theorem zero_mem_fullyBlockedBoundaries :
    (0 : GridChain (ZMod 2) n) ∈ G.fullyBlockedBoundaries := by
  exact Submodule.zero_mem G.fullyBlockedBoundaries

/-- The differential of a cycle is zero, as an element of the chain module. -/
theorem fullyBlockedDifferential_eq_zero_of_mem_cycles
    {c : GridChain (ZMod 2) n} (hc : c ∈ G.fullyBlockedCycles) :
    G.fullyBlockedDifferential c = 0 :=
  (G.mem_fullyBlockedCycles c).mp hc

/-- The differential of a chain is always a boundary. -/
theorem fullyBlockedDifferential_mem_boundaries (c : GridChain (ZMod 2) n) :
    G.fullyBlockedDifferential c ∈ G.fullyBlockedBoundaries :=
  (G.mem_fullyBlockedBoundaries (G.fullyBlockedDifferential c)).mpr ⟨c, rfl⟩

/-- Boundaries lie in cycles once the fully blocked differential is square-zero. -/
theorem fullyBlockedBoundaries_le_cycles
    (hsq : G.fullyBlockedDifferential.comp G.fullyBlockedDifferential = 0) :
    G.fullyBlockedBoundaries ≤ G.fullyBlockedCycles := by
  change LinearMap.range G.fullyBlockedDifferential ≤ LinearMap.ker G.fullyBlockedDifferential
  exact LinearMap.range_le_ker_iff.mpr hsq

/-- The fully blocked cycle submodule is top when the differential is the zero map. -/
theorem fullyBlockedCycles_eq_top_of_fullyBlockedDifferential_eq_zero
    (h : G.fullyBlockedDifferential =
      (0 : GridChain (ZMod 2) n →ₗ[ZMod 2] GridChain (ZMod 2) n)) :
    G.fullyBlockedCycles = ⊤ := by
  unfold fullyBlockedCycles
  exact LinearMap.ker_eq_top.mpr h

/-- The fully blocked boundary submodule is bottom when the differential is the zero map. -/
theorem fullyBlockedBoundaries_eq_bot_of_fullyBlockedDifferential_eq_zero
    (h : G.fullyBlockedDifferential =
      (0 : GridChain (ZMod 2) n →ₗ[ZMod 2] GridChain (ZMod 2) n)) :
    G.fullyBlockedBoundaries = ⊥ := by
  unfold fullyBlockedBoundaries
  exact LinearMap.range_eq_bot.mpr h

/-- In grid size at most two, every chain is a cycle for the fully blocked differential. -/
theorem fullyBlockedCycles_eq_top_of_le_two (hn : n ≤ 2) :
    G.fullyBlockedCycles = ⊤ :=
  G.fullyBlockedCycles_eq_top_of_fullyBlockedDifferential_eq_zero
    (G.fullyBlockedDifferential_eq_zero_of_le_two hn)

/-- In grid size at most two, the only boundary for the fully blocked differential is zero. -/
theorem fullyBlockedBoundaries_eq_bot_of_le_two (hn : n ≤ 2) :
    G.fullyBlockedBoundaries = ⊥ :=
  G.fullyBlockedBoundaries_eq_bot_of_fullyBlockedDifferential_eq_zero
    (G.fullyBlockedDifferential_eq_zero_of_le_two hn)

/-- On every `2 × 2` grid, every chain is a cycle for the fully blocked differential. -/
@[simp]
theorem fullyBlockedCycles_eq_top_of_two (G : GridDiagram 2) :
    G.fullyBlockedCycles = ⊤ :=
  G.fullyBlockedCycles_eq_top_of_le_two le_rfl

/-- On every `2 × 2` grid, the only boundary for the fully blocked differential is zero. -/
@[simp]
theorem fullyBlockedBoundaries_eq_bot_of_two (G : GridDiagram 2) :
    G.fullyBlockedBoundaries = ⊥ :=
  G.fullyBlockedBoundaries_eq_bot_of_le_two le_rfl

/-- In grid size at most two, every chain is a fully blocked cycle. -/
theorem mem_fullyBlockedCycles_of_le_two (hn : n ≤ 2) (c : GridChain (ZMod 2) n) :
    c ∈ G.fullyBlockedCycles := by
  rw [G.fullyBlockedCycles_eq_top_of_le_two hn]
  exact Submodule.mem_top

/-- In grid size at most two, a fully blocked boundary is exactly the zero chain. -/
theorem mem_fullyBlockedBoundaries_iff_eq_zero_of_le_two
    (hn : n ≤ 2) (c : GridChain (ZMod 2) n) :
    c ∈ G.fullyBlockedBoundaries ↔ c = 0 := by
  rw [G.fullyBlockedBoundaries_eq_bot_of_le_two hn]
  exact Submodule.mem_bot (R := ZMod 2)

/-- On every `2 × 2` grid, every chain is a fully blocked cycle. -/
theorem mem_fullyBlockedCycles_of_two (G : GridDiagram 2) (c : GridChain (ZMod 2) 2) :
    c ∈ G.fullyBlockedCycles :=
  G.mem_fullyBlockedCycles_of_le_two le_rfl c

/-- On every `2 × 2` grid, a fully blocked boundary is exactly the zero chain. -/
theorem mem_fullyBlockedBoundaries_iff_eq_zero_of_two
    (G : GridDiagram 2) (c : GridChain (ZMod 2) 2) :
    c ∈ G.fullyBlockedBoundaries ↔ c = 0 :=
  G.mem_fullyBlockedBoundaries_iff_eq_zero_of_le_two le_rfl c

/-- Every `2 × 2` grid has four fully blocked cycles. -/
theorem natCard_fullyBlockedCycles_of_two (G : GridDiagram 2) :
  Nat.card G.fullyBlockedCycles = 4 := by
  classical
  rw [fullyBlockedCycles_eq_top_of_two]
  simp

/-- Every `2 × 2` grid has one fully blocked boundary. -/
theorem natCard_fullyBlockedBoundaries_of_two (G : GridDiagram 2) :
    Nat.card G.fullyBlockedBoundaries = 1 := by
  classical
  rw [fullyBlockedBoundaries_eq_bot_of_two]
  simp

end GridDiagram

end TauCeti
