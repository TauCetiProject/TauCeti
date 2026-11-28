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
Similarly `unitInterval.abs_two_mul_sub_one_le_one` bounds `|2t - 1|` by `1`, for the
reparametrisation `t ↦ 2t - 1` of the unit interval onto `[-1, 1]`.

The subdivision of the unit interval into `r` equal arcs `[i/r, (i+1)/r]` is described by
`unitInterval.arcPoint r i a`, the point `(i + a) / r` at parameter `a` of the `i`-th arc, and
conversely by `unitInterval.arcIndex r s` and `unitInterval.arcParam r s`, the arc containing a
point `s` and the position of `s` in it, the end point `1` being counted in the last arc.
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
  (abs_of_nonneg t.property.1).trans_le t.property.2

/-- For a point `t` of the unit interval, `2t - 1` lies in `[-1, 1]`. -/
theorem abs_two_mul_sub_one_le_one (t : I) : |2 * (t : ℝ) - 1| ≤ 1 :=
  abs_le.2 ⟨by linarith [t.property.1], by linarith [t.property.2]⟩

end unitInterval

open Filter Set Topology

namespace Set

/-- The projection onto a symmetric interval `[-a, a]` has absolute value at most `a`. -/
theorem abs_projIcc_le {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    {a : α} (h : -a ≤ a) (x : α) : |(projIcc (-a) a h x : α)| ≤ a :=
  abs_le.2 (projIcc (-a) a h x).property

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

/-! ### Equal subdivisions of the unit interval -/

namespace unitInterval

/-- The point `(i + a) / r` of the unit interval: the point at parameter `a` of the `i`-th of the
`r` equal arcs `[i/r, (i+1)/r]`. -/
noncomputable def arcPoint (r i : ℕ) (a : I) : I :=
  projIcc 0 1 zero_le_one ((i + a) / r)

theorem coe_arcPoint {r i : ℕ} (hi : i < r) (a : I) : (arcPoint r i a : ℝ) = (i + a) / r := by
  have hr : (0 : ℝ) < r := by exact_mod_cast (Nat.zero_le i).trans_lt hi
  have hir : (i : ℝ) + 1 ≤ r := by exact_mod_cast hi
  rw [arcPoint, projIcc_of_mem]
  exact ⟨by have := a.property.1; positivity, (div_le_one hr).2 (by linarith [a.property.2])⟩

@[fun_prop]
theorem continuous_arcPoint (r i : ℕ) : Continuous (arcPoint r i) := by
  unfold arcPoint
  fun_prop

/-- With no arcs, every arc point is `0`. -/
@[simp]
theorem arcPoint_zero_left (i : ℕ) (a : I) : arcPoint 0 i a = 0 := by
  simp [arcPoint]

/-- The end of an arc is the start of the next one. -/
theorem arcPoint_one (r i : ℕ) : arcPoint r i 1 = arcPoint r (i + 1) 0 := by
  simp [arcPoint]

/-- The first arc starts at `0`. -/
@[simp]
theorem arcPoint_zero_zero (r : ℕ) : arcPoint r 0 0 = 0 := by
  simp [arcPoint]

/-- The start of the arc after the last of the `r` arcs is the end point `1`. -/
theorem arcPoint_self_zero {r : ℕ} (hr : 0 < r) : arcPoint r r 0 = 1 := by
  simp [arcPoint, hr.ne']

/-- The index of the arc containing a point `s` of the unit interval, `⌊r s⌋`, except that the
end point `1` belongs to the last arc. -/
noncomputable def arcIndex (r : ℕ) (s : I) : ℕ :=
  min ⌊(r : ℝ) * s⌋₊ (r - 1)

/-- The position `r s - arcIndex r s` of `s` inside its arc, rescaled to the unit interval. -/
noncomputable def arcParam (r : ℕ) (s : I) : I :=
  projIcc 0 1 zero_le_one ((r : ℝ) * s - arcIndex r s)

/-- With no arcs, every point is counted in the arc of index `0`. -/
@[simp]
theorem arcIndex_zero_left (s : I) : arcIndex 0 s = 0 := by
  simp [arcIndex]

theorem arcIndex_lt {r : ℕ} (hr : 0 < r) (s : I) : arcIndex r s < r :=
  (min_le_right _ _).trans_lt (Nat.sub_lt hr one_pos)

theorem arcIndex_le_mul (r : ℕ) (s : I) : (arcIndex r s : ℝ) ≤ r * s :=
  (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le (by have := s.property.1; positivity))

theorem mul_le_arcIndex_add_one {r : ℕ} (hr : 0 < r) (s : I) :
    (r : ℝ) * s ≤ arcIndex r s + 1 := by
  rcases le_total ⌊(r : ℝ) * s⌋₊ (r - 1) with h | h
  · rw [arcIndex, min_eq_left h]
    exact (Nat.lt_floor_add_one _).le
  · rw [arcIndex, min_eq_right h]
    push_cast [Nat.cast_sub hr]
    simpa using mul_le_of_le_one_right (Nat.cast_nonneg r) s.property.2

theorem coe_arcParam {r : ℕ} (hr : 0 < r) (s : I) :
    (arcParam r s : ℝ) = r * s - arcIndex r s := by
  rw [arcParam, projIcc_of_mem]
  exact ⟨sub_nonneg.2 (arcIndex_le_mul r s), by linarith [mul_le_arcIndex_add_one hr s]⟩

/-- A point is the point of its arc at its position in the arc. -/
theorem arcPoint_arcIndex_arcParam {r : ℕ} (hr : 0 < r) (s : I) :
    arcPoint r (arcIndex r s) (arcParam r s) = s := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  ext
  rw [coe_arcPoint (arcIndex_lt hr s), coe_arcParam hr, add_sub_cancel, mul_div_cancel_left₀ _ hr']

/-- A point of the `i`-th arc lies in the `i`-th arc, or it is the common end point of the `i`-th
and the `(i+1)`-th arcs and is counted in the latter. -/
theorem arcIndex_eq_or {r i : ℕ} (hi : i < r) {s : I} (h₀ : (i : ℝ) ≤ r * s)
    (h₁ : (r : ℝ) * s ≤ i + 1) :
    arcIndex r s = i ∨ arcIndex r s = i + 1 ∧ (r : ℝ) * s = i + 1 := by
  have hs : (0 : ℝ) ≤ r * s := by have := s.property.1; positivity
  have hle : i ≤ ⌊(r : ℝ) * s⌋₊ := Nat.le_floor h₀
  have hge : ⌊(r : ℝ) * s⌋₊ ≤ i + 1 := Nat.floor_le_of_le (by exact_mod_cast h₁)
  rcases (show ⌊(r : ℝ) * s⌋₊ = i ∨ ⌊(r : ℝ) * s⌋₊ = i + 1 by omega) with h | h
  · left
    rw [arcIndex, h]
    omega
  · have hrs : (r : ℝ) * s = i + 1 :=
      le_antisymm h₁ (by exact_mod_cast h ▸ Nat.floor_le hs)
    rcases Nat.lt_or_ge (i + 1) r with hi' | hi'
    · exact Or.inr ⟨by rw [arcIndex, h]; omega, hrs⟩
    · left
      rw [arcIndex, h]
      omega

/-- The point at a parameter `a < 1` of the `i`-th arc, `i < r`, lies in the `i`-th arc. -/
theorem arcIndex_arcPoint {r i : ℕ} (hi : i < r) {a : I} (ha : a < 1) :
    arcIndex r (arcPoint r i a) = i := by
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast ((Nat.zero_le i).trans_lt hi).ne'
  have ha' : (a : ℝ) < 1 := ha
  have hfloor : ⌊(i : ℝ) + a⌋₊ = i :=
    (Nat.floor_eq_iff (by have := a.property.1; positivity)).2 ⟨le_add_of_nonneg_right a.property.1,
        by linarith⟩
  rw [arcIndex, coe_arcPoint hi, mul_div_cancel₀ _ hr, hfloor]
  omega

/-- The point at a parameter `a < 1` of the `i`-th arc, `i < r`, is at parameter `a` in its arc. -/
theorem arcParam_arcPoint {r i : ℕ} (hi : i < r) {a : I} (ha : a < 1) :
    arcParam r (arcPoint r i a) = a := by
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast ((Nat.zero_le i).trans_lt hi).ne'
  ext
  rw [coe_arcParam ((Nat.zero_le i).trans_lt hi), arcIndex_arcPoint hi ha, coe_arcPoint hi,
    mul_div_cancel₀ _ hr, add_sub_cancel_left]

/-- The end point `1` lies in the last arc. -/
@[simp]
theorem arcIndex_one (r : ℕ) : arcIndex r 1 = r - 1 := by
  rw [arcIndex, Icc.coe_one, mul_one, Nat.floor_natCast]
  omega

/-- The end point `1` is at parameter `1` in the last arc. -/
theorem arcParam_one {r : ℕ} (hr : 0 < r) : arcParam r 1 = 1 := by
  ext
  rw [coe_arcParam hr, arcIndex_one]
  push_cast [Nat.cast_sub hr]
  ring

end unitInterval
