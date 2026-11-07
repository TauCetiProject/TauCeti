/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Ring.Periodic

/-!
# Floors and decompositions into intervals

A point of `[0, n)` in an ordered ring with a floor operation is the sum of an index in
`Fin n` and a remainder in `[0, 1)`. This describes, for example, time along one of the
finitely many edges in a polygonal boundary parametrization. In the same way, a `1`-periodic
function is determined by its values on `[0, 1)`: it takes the same value at `t` and at the
fractional part of `t`.

For a step `δ > 0` in a linearly ordered field with an integer floor, the multiples of `δ` cut
the line into the closed intervals `[δ m, δ (m + 1)]` with `m ∈ ℤ`. Every point `x` lies in the
interval indexed by `⌊x / δ⌋`, and an interval meeting `[-R, R]` has its index between
`⌈-R / δ⌉ - 1` and `⌊R / δ⌋`.

## Main results

* `TauCeti.exists_eq_natCast_add_of_mem_Ico`: a point of `[0, n)` is an index in `Fin n` plus
  a remainder in `[0, 1)`.
* `Function.Periodic.apply_fract`: a `1`-periodic function takes the same value at `t` and at
  its fractional part `Int.fract t`.
* `TauCeti.mem_Icc_mul_floor_div`: `x ∈ [δ ⌊x / δ⌋, δ (⌊x / δ⌋ + 1)]`.
* `TauCeti.mem_Icc_ceil_floor_of_mem_Icc`: if `x ∈ [δ m, δ (m + 1)]` and `|x| ≤ R`, then
  `m ∈ [⌈-R / δ⌉ - 1, ⌊R / δ⌋]`.
* `TauCeti.abs_sub_lt_two_thirds_of_natFloor_eq`: elements whose shifts have equal floors of
  `x * (3 / 2)` differ by less than `2 / 3`.
-/

public section

namespace TauCeti

/-- A point of `[0, n)` is an index in `Fin n` plus a remainder in `[0, 1)`. -/
theorem exists_eq_natCast_add_of_mem_Ico {R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] {n : ℕ} {t : R} (ht : t ∈ Set.Ico (0 : R) n) :
    ∃ j : Fin n, ∃ u ∈ Set.Ico (0 : R) 1, t = (j : ℕ) + u :=
  ⟨⟨⌊t⌋₊, (Nat.floor_lt ht.1).2 ht.2⟩, t - ⌊t⌋₊,
    ⟨sub_nonneg.2 (Nat.floor_le ht.1),
      (sub_lt_iff_lt_add).2 (by simpa only [add_comm] using Nat.lt_floor_add_one t)⟩, by simp⟩

/-- A `1`-periodic function takes the same value at `t` and at its fractional part. -/
theorem _root_.Function.Periodic.apply_fract {R β : Type*} [Ring R] [LinearOrder R]
    [FloorRing R] {f : R → β} (hf : Function.Periodic f 1) (t : R) : f (Int.fract t) = f t := by
  simpa [Int.self_sub_floor] using hf.sub_int_mul_eq (x := t) ⌊t⌋

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] {δ : K}

/-- For a step `δ > 0`, the point `x` lies in the interval `[δ m, δ (m + 1)]` with
`m = ⌊x / δ⌋`. -/
theorem mem_Icc_mul_floor_div (hδ : 0 < δ) (x : K) :
    x ∈ Set.Icc (δ * ⌊x / δ⌋) (δ * (⌊x / δ⌋ + 1)) := by
  constructor
  · rw [mul_comm, ← le_div_iff₀ hδ]
    exact Int.floor_le _
  · rw [mul_comm, ← div_le_iff₀ hδ]
    exact (Int.lt_floor_add_one _).le

/-- For a step `δ > 0`, an interval `[δ m, δ (m + 1)]` that meets `[-R, R]` has its index `m`
in the finite range `[⌈-R / δ⌉ - 1, ⌊R / δ⌋]`. -/
theorem mem_Icc_ceil_floor_of_mem_Icc (hδ : 0 < δ) {R x : K} {m : ℤ}
    (hx : x ∈ Set.Icc (δ * m) (δ * (m + 1))) (hxR : |x| ≤ R) :
    m ∈ Set.Icc (⌈-R / δ⌉ - 1) ⌊R / δ⌋ := by
  obtain ⟨hxR₁, hxR₂⟩ := abs_le.1 hxR
  constructor
  · have : ⌈-R / δ⌉ ≤ m + 1 := Int.ceil_le.2 <| by
      rw [div_le_iff₀ hδ]
      push_cast
      linarith [hx.2]
    omega
  · refine Int.le_floor.2 ?_
    rw [le_div_iff₀ hδ]
    linarith [hx.1]

/-- Two elements of an ordered field whose images under `x ↦ ⌊x * (3 / 2)⌋₊` agree after a common
shift `m` differ by less than `2 / 3`: the cells of the pigeonhole grid have side `2 / 3`. -/
theorem abs_sub_lt_two_thirds_of_natFloor_eq {u v m : K} (hu : 0 ≤ u + m) (hv : 0 ≤ v + m)
    (h : ⌊(u + m) * (3 / 2)⌋₊ = ⌊(v + m) * (3 / 2)⌋₊) : |u - v| < 2 / 3 := by
  have hcell := Int.abs_sub_lt_one_of_floor_eq_floor
    (a := (u + m) * (3 / 2)) (b := (v + m) * (3 / 2)) <| by
    rw [← Int.natCast_floor_eq_floor (by positivity), ← Int.natCast_floor_eq_floor (by positivity),
      h]
  rw [← sub_mul, add_sub_add_right_eq_sub, abs_mul, abs_of_pos (by norm_num : (0 : K) < 3 / 2)]
    at hcell
  linarith

end TauCeti
