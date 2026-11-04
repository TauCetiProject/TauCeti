/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Floors and decompositions into intervals

A point of `[0, n)` in an ordered ring with a floor operation is the sum of an index in
`Fin n` and a remainder in `[0, 1)`. This describes, for example, time along one of the
finitely many edges in a polygonal boundary parametrization.

For a step `δ > 0` in a linearly ordered field with an integer floor, the multiples of `δ` cut
the line into the closed intervals `[δ m, δ (m + 1)]` with `m ∈ ℤ`. Every point `x` lies in the
interval indexed by `⌊x / δ⌋`, and an interval meeting `[-R, R]` has its index between
`⌈-R / δ⌉ - 1` and `⌊R / δ⌋`.

## Main results

* `TauCeti.exists_eq_natCast_add_of_mem_Ico`: a point of `[0, n)` is an index in `Fin n` plus
  a remainder in `[0, 1)`.
* `TauCeti.mem_Icc_mul_floor_div`: `x ∈ [δ ⌊x / δ⌋, δ (⌊x / δ⌋ + 1)]`.
* `TauCeti.mem_Icc_ceil_floor_of_mem_Icc`: if `x ∈ [δ m, δ (m + 1)]` and `|x| ≤ R`, then
  `m ∈ [⌈-R / δ⌉ - 1, ⌊R / δ⌋]`.
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

end TauCeti
