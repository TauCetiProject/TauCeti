/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Cadlag

/-!
# Càdlàg step and monotone functions

A step taking its new value at its jump time is càdlàg, and every monotone right-continuous
function into a conditionally complete linear order with the order topology is càdlàg. For a
right-continuous function on a partial order, right continuity at a bottom element is full
continuity there. A monotone function into a locally finite order has only finitely many
discontinuities on each closed bounded interval, and at any discontinuity where a right-continuous
natural-valued monotone path jumps by at most one from some earlier time, its left limit is one
less than its current value.
-/

public section

open Filter Function Set
open scoped Topology

/-- Right continuity implies continuity at a bottom element, since no points lie strictly to its
left. -/
theorem IsRightContinuous.continuousAt_of_isBot {α β : Type*} [PartialOrder α]
    [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {a : α}
    (hf : IsRightContinuous f) (ha : IsBot a) : ContinuousAt f a := by
  simpa [ha.Ici_eq, continuousWithinAt_univ] using
    isRightContinuous_iff_continuousWithinAt_Ici.mp hf a

namespace Monotone

/-- Every monotone right-continuous function from a linear order into a conditionally complete
linear order (both with the order topology) is càdlàg. -/
theorem isCadlag {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} (hf : Monotone f) (hrc : IsRightContinuous f) : IsCadlag f :=
  ⟨hrc, fun x ↦ ⟨_, hf.tendsto_nhdsLT x⟩⟩

private theorem continuousAt_of_lt_of_eq {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [PartialOrder β] [TopologicalSpace β] {f : α → β}
    (hf : Monotone f) {x y z : α} (hxy : x < y) (hyz : y < z) (hxz : f x = f z) :
    ContinuousAt f y := by
  have hxy' : f x = f y := le_antisymm (hf hxy.le) (hxz ▸ hf hyz.le)
  refine (continuousAt_const (y := f y)).congr ?_
  filter_upwards [Ioo_mem_nhds hxy hyz] with w hw
  exact le_antisymm (hxy'.symm.trans_le (hf hw.1.le))
    ((hf hw.2.le).trans_eq (hxz.symm.trans hxy'))

private theorem finite_not_continuousAt_inter_preimage_singleton {α β : Type*}
    [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [PartialOrder β] [TopologicalSpace β]
    {f : α → β} (hf : Monotone f) (c : β) :
    {x | ¬ ContinuousAt f x ∧ f x = c}.Finite := by
  let S := {x | ¬ ContinuousAt f x ∧ f x = c}
  rcases S.eq_empty_or_nonempty with hS | ⟨x₀, hx₀⟩
  · simp [S, hS]
  · have hL : (S ∩ Iio x₀).Subsingleton := fun u hu v hv ↦ by
      by_contra huv
      rcases lt_or_gt_of_ne huv with hlt | hlt
      · exact hv.1.1 (hf.continuousAt_of_lt_of_eq hlt hv.2 (hu.1.2.trans hx₀.2.symm))
      · exact hu.1.1 (hf.continuousAt_of_lt_of_eq hlt hu.2 (hv.1.2.trans hx₀.2.symm))
    have hR : (S ∩ Ioi x₀).Subsingleton := fun u hu v hv ↦ by
      by_contra huv
      rcases lt_or_gt_of_ne huv with hlt | hlt
      · exact hu.1.1 (hf.continuousAt_of_lt_of_eq hu.2 hlt (hx₀.2.trans hv.1.2.symm))
      · exact hv.1.1 (hf.continuousAt_of_lt_of_eq hv.2 hlt (hx₀.2.trans hu.1.2.symm))
    refine ((hL.finite.union hR.finite).insert x₀).subset fun u hu ↦ ?_
    rcases lt_trichotomy u x₀ with hlt | rfl | hgt
    · exact Or.inr (Or.inl ⟨hu, hlt⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨hu, hgt⟩)

/-- A monotone function into a locally finite order has only finitely many discontinuities on each
closed bounded interval. Right continuity is not required. -/
theorem finite_Icc_not_continuousAt {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [PartialOrder β] [LocallyFiniteOrder β] [TopologicalSpace β]
    {f : α → β} (hf : Monotone f) (a b : α) :
    {x ∈ Icc a b | ¬ ContinuousAt f x}.Finite := by
  rcases le_or_gt a b with _ | hba
  · refine ((Set.finite_Icc (f a) (f b)).biUnion fun c _ ↦
        hf.finite_not_continuousAt_inter_preimage_singleton c).subset ?_
    rintro x ⟨hx, hnc⟩
    exact mem_biUnion ⟨hf hx.1, hf hx.2⟩ ⟨hnc, rfl⟩
  · simp [Icc_eq_empty_of_lt hba]

/-- At a discontinuity where a monotone right-continuous natural-valued function exceeds some
strictly earlier value by at most one, its left limit is exactly one below its current value. -/
theorem leftLim_add_one_eq_of_not_continuousAt {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] {f : α → ℕ} (hf : Monotone f)
    (hrc : IsRightContinuous f) {x : α} (hx : ¬ ContinuousAt f x)
    (hjump : ∃ s < x, f x ≤ f s + 1) :
    leftLim f x + 1 = f x := by
  obtain ⟨s, hsx, hfs⟩ := hjump
  have hr : rightLim f x = f x :=
    (isRightContinuous_iff_continuousWithinAt_Ici.mp hrc x).rightLim_eq
  have hne : leftLim f x ≠ f x := fun h ↦
    hx (hf.continuousAt_iff_leftLim_eq_rightLim.mpr (h.trans hr.symm))
  have hlt : leftLim f x < f x := lt_of_le_of_ne (hf.leftLim_le le_rfl) hne
  exact le_antisymm hlt (hfs.trans (Nat.add_le_add_right (hf.le_leftLim hsx) 1))

end Monotone

namespace TauCeti

/-- A single step, with the right-hand value at the jump, is càdlàg. -/
theorem isCadlag_ite_le {ι E : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderClosedTopology ι] [TopologicalSpace E] (a : ι) (x y : E) :
    IsCadlag (fun t => if a ≤ t then x else y) := by
  constructor
  · intro t
    by_cases hat : a ≤ t
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [hat.trans (le_of_lt hs), hat]
    · apply tendsto_const_nhds.congr'
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_of_not_ge hat))] with s hs
      simp [not_le.mpr hs, hat]
  · intro t
    by_cases hat : a < t
    · refine ⟨x, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hat)] with s hs
      simp [hs.le]
    · refine ⟨y, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [not_le.mpr (hs.trans_le (le_of_not_gt hat))]

end TauCeti
