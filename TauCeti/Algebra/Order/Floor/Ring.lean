/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Int.Interval
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Set.Finite.Range

/-!
# Floors and decompositions into intervals

A point of `[0, n)` in an ordered ring with a floor operation is the sum of an index in
`Fin n` and a remainder in `[0, 1)`. This describes, for example, time along one of the
finitely many edges in a polygonal boundary parametrization. In the same way, a `1`-periodic
function is determined by its values on `[0, 1)`: it takes the same value at `t` and at the
fractional part of `t`. The integers in `[a, y)` number `max (y - a) 0` up to one.

For a step `δ > 0` in a linearly ordered field with an integer floor, the multiples of `δ` cut
the line into the closed intervals `[δ m, δ (m + 1)]` with `m ∈ ℤ`. Every point `x` lies in the
interval indexed by `⌊x / δ⌋`, and an interval meeting `[-R, R]` has its index between
`⌈-R / δ⌉ - 1` and `⌊R / δ⌋`. Rounding up to the multiples of `δ` moves a point by less than
`δ`, and on a finite index type only finitely many rounded families have entries in `[-R, R]`.

## Main results

* `TauCeti.exists_eq_natCast_add_of_mem_Ico`: a point of `[0, n)` is an index in `Fin n` plus
  a remainder in `[0, 1)`.
* `Function.Periodic.apply_fract`: a `1`-periodic function takes the same value at `t` and at
  its fractional part `Int.fract t`.
* `Nat.cast_lt_iff_le_ceil_sub_one`: `(n : R) < a ↔ (n : R) ≤ ⌈a⌉₊ - 1` for natural `n`.
* `TauCeti.mem_Ico_ceil_iff`, `TauCeti.mem_Ico_ceil_neg_iff`: membership of `n` in
  `Finset.Ico ⌈a⌉₊ ⌈b⌉₊` and `Finset.Ico ⌈-b⌉₊ ⌈-a⌉₊` as `(n : R) ∈ [a, b)` and `-(n : R) ∈ (a, b]`.
* `TauCeti.abs_card_Ico_ceil_sub_le`: `|#[a, ⌈y⌉) - max (y - a) 0| ≤ 1` for an integer `a`.
* `TauCeti.mem_Icc_mul_floor_div`: `x ∈ [δ ⌊x / δ⌋, δ (⌊x / δ⌋ + 1)]`.
* `TauCeti.mem_Icc_ceil_floor_of_mem_Icc`: if `x ∈ [δ m, δ (m + 1)]` and `|x| ≤ R`, then
  `m ∈ [⌈-R / δ⌉ - 1, ⌊R / δ⌋]`.
* `TauCeti.exists_finset_forall_exists_le_lt_add`: finitely many families round up, by less
  than `δ` in each entry, every family with entries in `[-R, R]`.
* `TauCeti.abs_sub_lt_one_div_of_natFloor_mul_eq`: for `t > 0`, nonnegative elements `a`, `b`
  with `⌊a * t⌋₊ = ⌊b * t⌋₊` differ by less than `1 / t`.
* `TauCeti.exists_pos_lt_abs_add_natCast`: any element avoiding `-ℕ` stays a positive distance
  away from all `-n` (`n : ℕ`).
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

/-- In an ordered ring with a natural ceiling, a natural number lies strictly below `a` exactly
when it is at most `⌈a⌉₊ - 1`. This turns a strict cutoff into an inclusive one. -/
theorem _root_.Nat.cast_lt_iff_le_ceil_sub_one {R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorSemiring R] (n : ℕ) {a : R} :
    (n : R) < a ↔ (n : R) ≤ ⌈a⌉₊ - 1 := by
  rw [← Nat.lt_ceil, le_sub_iff_add_le, ← Nat.cast_add_one, Nat.cast_le, Nat.add_one_le_iff]

/-- In a linearly ordered semiring with a natural ceiling, `n ∈ [⌈a⌉₊, ⌈b⌉₊)` if and only if
`(n : R) ∈ [a, b)`. -/
theorem mem_Ico_ceil_iff {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]
    {a b : R} {n : ℕ} :
    n ∈ Finset.Ico ⌈a⌉₊ ⌈b⌉₊ ↔ (n : R) ∈ Set.Ico a b := by
  rw [Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil, Set.mem_Ico]

/-- In a linearly ordered ring with a natural ceiling, `n ∈ [⌈-b⌉₊, ⌈-a⌉₊)` if and only if
`-(n : R) ∈ (a, b]`. -/
theorem mem_Ico_ceil_neg_iff {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] {a b : R} {n : ℕ} :
    n ∈ Finset.Ico ⌈-b⌉₊ ⌈-a⌉₊ ↔ -(n : R) ∈ Set.Ioc a b := by
  rw [mem_Ico_ceil_iff, Set.mem_Ico, Set.mem_Ioc, neg_le, lt_neg, and_comm]

/-- In a linearly ordered field with a natural floor, any element `x` avoiding the nonpositive
integers `-ℕ` stays at a positive uniform distance `ε > 0` from all `-n` (`n : ℕ`). -/
theorem exists_pos_lt_abs_add_natCast {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorSemiring K] {x : K} (hx : ∀ n : ℕ, x ≠ -n) :
    ∃ ε : K, 0 < ε ∧ ∀ n : ℕ, ε < |x + n| := by
  rcases lt_or_ge 0 x with hx0 | hx0
  · refine ⟨x / 2, half_pos hx0, fun n ↦ ?_⟩
    rw [abs_of_pos (by linarith [n.cast_nonneg (α := K)])]
    linarith [n.cast_nonneg (α := K)]
  · set N : ℕ := ⌊-x⌋₊
    have hlo : -((N + 1 : ℕ) : K) < x := by
      have hlt : -x < (N : K) + 1 := Nat.lt_floor_add_one (-x)
      push_cast
      linarith
    have hhi : x < -(N : K) :=
      lt_of_le_of_ne (le_neg.mp (Nat.floor_le (neg_nonneg.mpr hx0))) (hx N)
    set ε : K := min (x + ((N + 1 : ℕ) : K)) (-(N : K) - x) / 2
    have hε : 0 < ε := half_pos (lt_min (by linarith) (by linarith))
    refine ⟨ε, hε, fun n ↦ ?_⟩
    rcases le_or_gt n N with hn | hn
    · have hle : (n : K) ≤ N := Nat.cast_le.mpr hn
      have h1 : 2 * ε ≤ -(N : K) - x := by
        dsimp [ε]
        linarith [min_le_right (x + ((N + 1 : ℕ) : K)) (-(N : K) - x)]
      have hneg : x + (n : K) < -ε := by linarith
      exact (lt_neg.mp hneg).trans_le (neg_le_abs _)
    · have hle : ((N + 1 : ℕ) : K) ≤ n := Nat.cast_le.mpr hn
      have h1 : 2 * ε ≤ x + ((N + 1 : ℕ) : K) := by
        dsimp [ε]
        linarith [min_le_left (x + ((N + 1 : ℕ) : K)) (-(N : K) - x)]
      have hpos : ε < x + (n : K) := by linarith
      exact hpos.trans_le (le_abs_self _)

/-- The number of integers in `[a, y)` is `max (y - a) 0` up to an error of at most one. -/
theorem abs_card_Ico_ceil_sub_le {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] (a : ℤ) (y : R) :
    |((Finset.Ico a ⌈y⌉).card : R) - max (y - a) 0| ≤ 1 := by
  rw [Int.card_Ico]
  rcases le_or_gt ⌈y⌉ a with h | h
  · rw [Int.toNat_of_nonpos (by omega), max_eq_right (sub_nonpos.2 (Int.ceil_le.1 h))]
    simp
  · rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega),
      max_eq_left (sub_nonneg.2 (Int.lt_ceil.1 h).le), Int.cast_sub, sub_sub_sub_cancel_right,
      abs_le]
    exact ⟨(neg_nonpos.2 zero_le_one).trans (sub_nonneg.2 (Int.le_ceil y)),
      (sub_lt_iff_lt_add'.2 (Int.ceil_lt_add_one y)).le⟩

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

/-- **Rounding up to a grid.** For a step `δ > 0` and a bound `R`, finitely many families on a
finite index type round up every family `a` with entries in `[-R, R]`: some `c` among them has
`a k ≤ c k < a k + δ` for every `k`. The families are those with entries `δ m`,
`m ∈ [⌈-R / δ⌉, ⌈R / δ⌉]`, and `c k = δ ⌈a k / δ⌉`. -/
theorem exists_finset_forall_exists_le_lt_add {κ : Type*} [Finite κ] (hδ : 0 < δ) (R : K) :
    ∃ T : Finset (κ → K), ∀ a : κ → K, (∀ k, |a k| ≤ R) →
      ∃ c ∈ T, ∀ k, a k ≤ c k ∧ c k < a k + δ := by
  classical
  refine ⟨(Set.finite_range fun (g : κ → Set.Icc ⌈-R / δ⌉ ⌈R / δ⌉) k ↦ δ * (g k : ℤ)).toFinset,
    fun a ha ↦ ⟨fun k ↦ δ * ⌈a k / δ⌉, ?_, fun k ↦ ⟨?_, ?_⟩⟩⟩
  · -- rounding up preserves the bounds `-R ≤ a k ≤ R`
    refine (Set.Finite.mem_toFinset _).2 ⟨fun k ↦ ⟨⌈a k / δ⌉, ?_, ?_⟩, rfl⟩ <;>
      refine Int.ceil_mono (div_le_div_of_nonneg_right ?_ hδ.le)
    exacts [(abs_le.1 (ha k)).1, (abs_le.1 (ha k)).2]
  · dsimp only
    rw [mul_comm, ← div_le_iff₀ hδ]
    exact Int.le_ceil _
  · dsimp only
    rw [mul_comm, ← lt_div_iff₀ hδ, add_div, div_self hδ.ne']
    exact Int.ceil_lt_add_one _

/-- For `t > 0`, two nonnegative elements `a`, `b` of an ordered field with the same natural
floor of `x * t` differ by less than `1 / t`: on the nonnegative half-line the cells of the grid of
scale `t` have side `1 / t`. -/
theorem abs_sub_lt_one_div_of_natFloor_mul_eq {a b t : K} (ht : 0 < t) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ⌊a * t⌋₊ = ⌊b * t⌋₊) : |a - b| < 1 / t := by
  have hcell := Int.abs_sub_lt_one_of_floor_eq_floor (a := a * t) (b := b * t) <| by
    rw [← Int.natCast_floor_eq_floor (by positivity), ← Int.natCast_floor_eq_floor (by positivity),
      h]
  rw [← sub_mul, abs_mul, abs_of_pos ht] at hcell
  rw [lt_div_iff₀ ht]
  exact hcell

end TauCeti
