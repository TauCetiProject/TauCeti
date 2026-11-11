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
We give its closed form and continuity in the step size. Step sizes tending to a positive limit
along a filter reach the endpoint after a single number of steps, eventually along the filter;
for positive step sizes continuous at a parameter, this number is valid throughout a
neighbourhood, which permits locally finite compositions without a global positive lower bound.

Finally, `unitInterval.abs_coe_le_one` and `Set.abs_projIcc_le` bound the absolute value of a
point of the unit interval by `1`, and that of the projection onto a symmetric interval
`[-a, a]` by `a`. These are the side conditions for scaling by a factor `b` with `|b| ≤ 1`.
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
  part.mono i.castSucc_le_succ

end Partition

/-- A point of the unit interval has absolute value at most one. -/
theorem abs_coe_le_one (t : I) : |(t : ℝ)| ≤ 1 :=
  (abs_of_nonneg t.2.1).trans_le t.2.2

end unitInterval

open Filter Set Topology

namespace Set

/-- The projection onto a symmetric interval `[-a, a]` has absolute value at most `a`. -/
theorem abs_projIcc_le {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    {a : α} (h : -a ≤ a) (x : α) : |(projIcc (-a) a h x : α)| ≤ a :=
  abs_le.2 (projIcc (-a) a h x).2

end Set

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
  fun_prop

/-- Step sizes tending to a positive limit along a filter reach the right endpoint after a single
number of steps, eventually along that filter. In particular, positive step sizes continuous at a
parameter do so on a neighbourhood of that parameter. -/
theorem exists_eventually_addNSMul_eq_right {α X : Type*} [AddCommGroup α] [LinearOrder α]
    [IsOrderedAddMonoid α] [Archimedean α] [TopologicalSpace α] [OrderTopology α]
    {a b : α} (h : a ≤ b) {δ : X → α} {l : Filter X} {c : α}
    (hδ : Tendsto δ l (𝓝 c)) (hc : 0 < c) :
    ∃ N : ℕ, ∀ᶠ y in l, ∀ n ≥ N, addNSMul h (δ y) n = b := by
  obtain ⟨d, e, hcde, hde, hpos⟩ := exists_Icc_mem_subset_of_mem_nhds (Ioi_mem_nhds hc)
  have hd0 : 0 < d := hpos (left_mem_Icc.2 (hcde.1.trans hcde.2))
  obtain ⟨N, hN⟩ := Archimedean.arch (b - a) hd0
  refine ⟨N, ?_⟩
  filter_upwards [hδ hde] with y hy n hn
  rw [coe_addNSMul h (hd0.le.trans hy.1), min_eq_left]
  exact sub_le_iff_le_add'.mp
    (hN.trans ((nsmul_le_nsmul_left hd0.le hn).trans (nsmul_le_nsmul_right hy.1 n)))

end Set.Icc
