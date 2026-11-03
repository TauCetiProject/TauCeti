/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Order.ProjIcc

/-!
# Partitions and clipped subdivisions of intervals

`unitInterval.Partition n` is a monotone sequence `0 = t₀ ≤ ⋯ ≤ tₙ = 1` in the unit interval.
It indexes the segments of the tube neighbourhoods of paths in
`TauCeti.Topology.Homotopy.TubeNeighborhood`.

Mathlib's `Set.Icc.addNSMul` gives equally spaced subdivisions clipped at the right endpoint.
We give its closed form and continuity in the step size. Positive steps continuous at a
parameter reach the endpoint after a single number of steps valid throughout a neighbourhood;
this permits locally finite compositions without a global positive lower bound.
-/

-- Ported from https://github.com/leanprover-community/mathlib4/pull/44183.

public section

namespace unitInterval

/-- A partition `0 = t₀ ≤ ⋯ ≤ tₙ = 1` of the unit interval into `n` segments. -/
structure Partition (n : ℕ) where
  /-- The partition points. -/
  t : Fin (n + 1) → I
  /-- The partition points are monotone. -/
  mono : Monotone t
  /-- The first partition point is `0`. -/
  t_zero : t 0 = 0
  /-- The last partition point is `1`. -/
  t_last : t (Fin.last n) = 1

namespace Partition

attribute [simp] t_zero t_last

/-- There is no partition into zero segments, since `t 0` would be both `0` and `1`. -/
instance : IsEmpty (Partition 0) :=
  ⟨fun p ↦ zero_ne_one (p.t_zero.symm.trans p.t_last)⟩

/-- Consecutive partition points are ordered. -/
theorem t_castSucc_le_succ {n : ℕ} (part : Partition n) (i : Fin n) :
    part.t i.castSucc ≤ part.t i.succ :=
  part.mono i.castSucc_lt_succ.le

end Partition

end unitInterval

open Filter Set Topology

namespace Set.Icc

/-- With a nonnegative step, the lower clipping in `addNSMul` is redundant. -/
@[simp]
theorem coe_addNSMul {α : Type*} [AddCommGroup α] [LinearOrder α]
    [IsOrderedAddMonoid α] {a b δ : α} (h : a ≤ b) (hδ : 0 ≤ δ) (n : ℕ) :
    (addNSMul h δ n : α) = min b (a + n • δ) := by
  rw [addNSMul, coe_projIcc, max_eq_right]
  exact le_min h (le_add_of_nonneg_right (nsmul_nonneg hδ n))

/-- Each point of the clipped subdivision varies continuously with its step size. -/
@[fun_prop]
theorem continuous_addNSMul {α : Type*} [AddCommGroup α] [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [ContinuousAdd α]
    {a b : α} (h : a ≤ b) (n : ℕ) :
    Continuous fun δ : α ↦ addNSMul h δ n := by
  unfold addNSMul
  exact continuous_projIcc.comp (continuous_const.add (continuous_id.nsmul n))

/-- Positive step sizes continuous at a parameter reach the right endpoint after a single
number of steps valid on a neighbourhood of that parameter. -/
theorem exists_eventually_addNSMul_eq_right {α X : Type*} [AddCommGroup α] [LinearOrder α]
    [IsOrderedAddMonoid α] [Archimedean α] [TopologicalSpace α] [OrderTopology α]
    [TopologicalSpace X] {a b : α} (h : a ≤ b) {δ : X → α} {x : X}
    (hδ : ContinuousAt δ x) (hpos : 0 < δ x) :
    ∃ N : ℕ, ∀ᶠ y in 𝓝 x, ∀ n ≥ N, addNSMul h (δ y) n = b := by
  have hlower : ∃ c > (0 : α), ∀ᶠ y in 𝓝 x, c ≤ δ y := by
    by_cases hbetween : ∃ c : α, 0 < c ∧ c < δ x
    · obtain ⟨c, hc, hcx⟩ := hbetween
      exact ⟨c, hc, (hδ.eventually (Ioi_mem_nhds hcx)).mono fun _ hy ↦ hy.le⟩
    · refine ⟨δ x, hpos, ?_⟩
      filter_upwards [hδ.eventually (Ioi_mem_nhds hpos)] with y hy
      exact le_of_not_gt fun hlt ↦ hbetween ⟨δ y, hy, hlt⟩
  obtain ⟨c, hc, hnear⟩ := hlower
  obtain ⟨N, hN⟩ := Archimedean.arch (b - a) hc
  refine ⟨N, ?_⟩
  filter_upwards [hnear] with y hy n hn
  have hbound : b - a ≤ n • δ y :=
    hN.trans ((nsmul_le_nsmul_left hc.le hn).trans (nsmul_le_nsmul_right hy n))
  rw [coe_addNSMul h (hc.le.trans hy), min_eq_left]
  exact sub_le_iff_le_add'.mp hbound

end Set.Icc
