/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Set.Finite.Basic

/-!
# Continuity and discontinuities of monotone functions

If a monotone function on a linearly ordered space with an order-closed topology takes the same
value at two points surrounding `y`, then it is constant on an open interval around `y` and hence
continuous at `y`. Consequently, a monotone function can be discontinuous at at most two points
within any single fiber, and a monotone function into a locally finite order has only finitely many
discontinuities on each closed bounded interval (without assuming right- or left-continuity).
-/

public section

open Filter Set

namespace Monotone

/-- If a monotone function on a linearly ordered space with an order-closed topology takes equal
values strictly to the left and right of `y`, then it is continuous at `y`. -/
theorem continuousAt_of_lt_of_eq {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [PartialOrder β] [TopologicalSpace β] {f : α → β}
    (hf : Monotone f) {x y z : α} (hxy : x < y) (hyz : y < z) (hxz : f x = f z) :
    ContinuousAt f y := by
  have hxy' : f x = f y := le_antisymm (hf hxy.le) (hxz ▸ hf hyz.le)
  refine (continuousAt_const (y := f y)).congr ?_
  filter_upwards [Ioo_mem_nhds hxy hyz] with w hw
  exact le_antisymm (hxy'.symm.trans_le (hf hw.1.le))
    ((hf hw.2.le).trans_eq (hxz.symm.trans hxy'))

/-- A monotone function on a linearly ordered space with an order-closed topology has only finitely
many discontinuities (in fact at most two) in each fiber `f ⁻¹' {c}`. -/
theorem finite_setOf_not_continuousAt_and_eq {α β : Type*}
    [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] [PartialOrder β]
    [TopologicalSpace β] {f : α → β} (hf : Monotone f) (c : β) :
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
    [OrderClosedTopology α] [PartialOrder β] [LocallyFiniteOrder β] [TopologicalSpace β]
    {f : α → β} (hf : Monotone f) (a b : α) :
    {x ∈ Icc a b | ¬ ContinuousAt f x}.Finite := by
  rcases le_or_gt a b with _ | hba
  · refine ((Set.finite_Icc (f a) (f b)).biUnion fun c _ ↦
        hf.finite_setOf_not_continuousAt_and_eq c).subset ?_
    rintro x ⟨hx, hnc⟩
    exact mem_biUnion ⟨hf hx.1, hf hx.2⟩ ⟨hnc, rfl⟩
  · simp [Icc_eq_empty_of_lt hba]

end Monotone
