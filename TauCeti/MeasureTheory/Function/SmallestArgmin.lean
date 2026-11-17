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

For a finite nonempty linearly ordered index type `ι` and a family of measurable functions
`c : Ω → ι → α` into a second-countable linearly ordered topological space with order-closed
topology, the pointwise least minimizer `ω ↦ TauCeti.smallestArgmin (c ω)` is measurable for every
measurable space structure on `ι` (without assuming `MeasurableSingletonClass ι`).

## Main results

* `TauCeti.measurable_smallestArgmin`: measurability of `ω ↦ smallestArgmin (c ω)`.
-/

public section

namespace TauCeti

/-- If each coordinate function `ω ↦ c ω i` is measurable into a second-countable linearly ordered
topological space with order-closed topology, then `ω ↦ smallestArgmin (c ω)` is measurable for
every measurable structure on the finite index type `ι` (no `MeasurableSingletonClass ι` needed). -/
@[fun_prop]
theorem measurable_smallestArgmin {Ω ι α : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] [LinearOrder ι] [MeasurableSpace ι]
    [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] [SecondCountableTopology α]
    [MeasurableSpace α] [OpensMeasurableSpace α]
    {c : Ω → ι → α} (hc : ∀ i, Measurable fun ω ↦ c ω i) :
    Measurable fun ω ↦ smallestArgmin (c ω) := by
  intro s _
  have hsingle (j : ι) : MeasurableSet ((fun ω ↦ smallestArgmin (c ω)) ⁻¹' {j}) := by
    have hset : (fun ω ↦ smallestArgmin (c ω)) ⁻¹' {j} =
        (⋂ i : ι, {ω | c ω j ≤ c ω i}) ∩
        (⋂ (i : ι) (_ : i < j), {ω | c ω j < c ω i}) := by
      ext ω
      simp [smallestArgmin_eq_iff]
    rw [hset]
    exact MeasurableSet.inter
      (MeasurableSet.iInter fun i ↦ measurableSet_le (hc j) (hc i))
      (MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦ measurableSet_lt (hc j) (hc i))
  have hpre : (fun ω ↦ smallestArgmin (c ω)) ⁻¹' s =
      ⋃ j ∈ s, (fun ω ↦ smallestArgmin (c ω)) ⁻¹' {j} := by
    ext ω
    simp
  rw [hpre]
  exact MeasurableSet.biUnion s.to_countable fun j _ ↦ hsingle j

end TauCeti
