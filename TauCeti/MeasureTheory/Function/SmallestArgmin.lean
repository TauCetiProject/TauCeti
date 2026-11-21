/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Order.Basic
public import TauCeti.Order.SmallestArgmin
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of the smallest argmin

Proves `TauCeti.measurable_smallestArgmin`: for measurable coordinate functions into a
second-countable linearly ordered topological space with order-closed topology, `ω ↦
smallestArgmin (c ω)` is measurable for any measurable space structure on the finite index type `ι`.
-/

public section

namespace TauCeti

/-- If each coordinate `ω ↦ c ω i` is measurable into a second-countable order-closed linearly
ordered space, then `ω ↦ smallestArgmin (c ω)` is measurable (no `MeasurableSingletonClass ι`). -/
@[fun_prop]
theorem measurable_smallestArgmin {Ω ι α : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] [LinearOrder ι] [MeasurableSpace ι]
    [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] [SecondCountableTopology α]
    [MeasurableSpace α] [OpensMeasurableSpace α]
    {c : Ω → ι → α} (hc : ∀ i, Measurable fun ω ↦ c ω i) :
    Measurable fun ω ↦ smallestArgmin (c ω) := by
  intro s _
  rw [← Set.biUnion_of_singleton s, Set.preimage_iUnion₂]
  refine MeasurableSet.biUnion s.to_countable fun j _ ↦ ?_
  have hset : (fun ω ↦ smallestArgmin (c ω)) ⁻¹' {j} =
      (⋂ i : ι, {ω | c ω j ≤ c ω i}) ∩
      (⋂ (i : ι) (_ : i < j), {ω | c ω j < c ω i}) := by
    ext ω; simp [smallestArgmin_eq_iff]
  rw [hset]
  exact (MeasurableSet.iInter fun i ↦ measurableSet_le (hc j) (hc i)).inter
    (MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦ measurableSet_lt (hc j) (hc i))

end TauCeti
