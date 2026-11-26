/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Order.Basic
public import TauCeti.Order.SmallestArgmin
import Mathlib.Logic.Encodable.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of tie-broken argmin selectors

Given measurable coordinate criteria `ω ↦ c ω i` on a countable index type `ι` into a
second-countable linearly ordered topological space with order-closed topology, any selector
`g : Ω → ι` characterized by minimizing `c ω` while strictly beating earlier indices under a
tie-break relation is measurable for any measurable-space structure on `ι` (without
`MeasurableSingletonClass ι`, `BorelSpace ι`, or continuity of `c`, in contrast to
`Continuous.exists_measurable_isMinOn`). This yields both `TauCeti.measurable_smallestArgmin` on a
finite linear order and `TauCeti.exists_measurable_forall_le` on a countable index type.
-/

public section

namespace TauCeti

section Countable

variable {Ω ι α : Type*} [MeasurableSpace Ω] [Countable ι] [MeasurableSpace ι]
  [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] [SecondCountableTopology α]
  [MeasurableSpace α] [OpensMeasurableSpace α]

/-- On a countable index type `ι` (with any measurable structure), if each `ω ↦ c ω i` is
measurable and `g : Ω → ι` is characterized by minimizing `c ω` while strictly beating indices `i`
with `r i j`, then `g` is measurable. -/
theorem measurable_of_forall_le_and_forall_lt {c : Ω → ι → α} {r : ι → ι → Prop} {g : Ω → ι}
    (hc : ∀ i, Measurable fun ω ↦ c ω i)
    (hg : ∀ ω j, g ω = j ↔ (∀ i, c ω j ≤ c ω i) ∧ ∀ i, r i j → c ω j < c ω i) :
    Measurable g := by
  intro s _
  rw [← Set.biUnion_of_singleton s, Set.preimage_iUnion₂]
  refine MeasurableSet.biUnion s.to_countable fun j _ ↦ ?_
  have hset : g ⁻¹' {j} =
      (⋂ i : ι, {ω | c ω j ≤ c ω i}) ∩
      (⋂ (i : ι) (_ : r i j), {ω | c ω j < c ω i}) := by
    ext ω; simp [hg ω j]
  rw [hset]
  exact (MeasurableSet.iInter fun i ↦ measurableSet_le (hc j) (hc i)).inter
    (MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦ measurableSet_lt (hc j) (hc i))

/-- If each coordinate `ω ↦ c ω i` on a countable index type `ι` is measurable and `c ω` attains a
global minimum for every `ω`, then `c` admits a measurable minimizer `g : Ω → ι` (without
`MeasurableSingletonClass ι`). -/
theorem exists_measurable_forall_le {c : Ω → ι → α} (hc : ∀ i, Measurable fun ω ↦ c ω i)
    (hmin : ∀ ω, ∃ j, ∀ i, c ω j ≤ c ω i) :
    ∃ g : Ω → ι, Measurable g ∧ ∀ ω i, c ω (g ω) ≤ c ω i := by
  classical
  let e : Encodable ι := Encodable.ofCountable ι
  have hex (ω : Ω) : ∃ k : ℕ, ∃ j : ι, e.encode j = k ∧ ∀ i, c ω j ≤ c ω i :=
    let ⟨j, hj⟩ := hmin ω; ⟨e.encode j, j, rfl, hj⟩
  let g : Ω → ι := fun ω ↦ Classical.choose (Nat.find_spec (hex ω))
  have hg_enc (ω : Ω) : e.encode (g ω) = Nat.find (hex ω) :=
    (Classical.choose_spec (Nat.find_spec (hex ω))).1
  have hg_min (ω : Ω) (i : ι) : c ω (g ω) ≤ c ω i :=
    (Classical.choose_spec (Nat.find_spec (hex ω))).2 i
  have hchar (ω : Ω) (j : ι) : g ω = j ↔
      (∀ i, c ω j ≤ c ω i) ∧ ∀ i, e.encode i < e.encode j → c ω j < c ω i := by
    refine ⟨fun h ↦ h ▸ ⟨hg_min ω, fun i hlt ↦ lt_of_not_ge fun hle ↦ ?_⟩, ?_⟩
    · have := Nat.find_min' (hex ω) ⟨i, rfl, fun k ↦ hle.trans (hg_min ω k)⟩
      have := hg_enc ω; omega
    · rintro ⟨hj_min, hj_lt⟩
      exact e.encode_injective <| le_antisymm
        (hg_enc ω ▸ Nat.find_min' (hex ω) ⟨j, rfl, hj_min⟩)
        (le_of_not_gt fun hlt ↦ not_le_of_gt (hj_lt (g ω) hlt) (hg_min ω j))
  exact ⟨g, measurable_of_forall_le_and_forall_lt hc hchar, hg_min⟩

end Countable

/-- If each coordinate `ω ↦ c ω i` is measurable into a second-countable order-closed linearly
ordered space, then `ω ↦ smallestArgmin (c ω)` is measurable (no `MeasurableSingletonClass ι`). -/
@[fun_prop]
theorem measurable_smallestArgmin {Ω ι α : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] [LinearOrder ι] [MeasurableSpace ι]
    [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] [SecondCountableTopology α]
    [MeasurableSpace α] [OpensMeasurableSpace α]
    {c : Ω → ι → α} (hc : ∀ i, Measurable fun ω ↦ c ω i) :
    Measurable fun ω ↦ smallestArgmin (c ω) :=
  measurable_of_forall_le_and_forall_lt hc fun _ _ ↦ smallestArgmin_eq_iff

end TauCeti
