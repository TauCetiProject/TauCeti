/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

/-!
# Weights of regular parameters

A highest weight of the compact unitary group `U(n)` is given by column multiplicities and a
power of the determinant: `κ h` columns of height `h` for `0 < h < n`, and the `e`-th power of the
determinant. Its entry at the position `p` (counted from `0`) is
`μ p = e + ∑_{p < h < n} κ h` (`TauCeti.columnHighestWeight`), a weakly decreasing sequence of
integers, and twice its Harish-Chandra parameter `μ + ρ` has the entries
`2 μ p + n - 1 - 2 p` (`TauCeti.doubledHCParameter`), a strictly decreasing sequence of integers of
the parity of `n - 1`. A vector `l : ι → ℤ`, with `card ι = n`, is the doubled parameter of
`(κ, e)` (`TauCeti.IsDoubledHCParameter`) if it lists these entries in some order.

The doubled Harish-Chandra parameters of the discrete series of a unitary group `U(p, q)` with a
gap, the regular parameters, have distinct entries of the parity of `n - 1`. This file shows that
every such vector is the doubled parameter of an explicit weight, with prescribed columns of the
heights above `n` and control of the determinant power from below
(`TauCeti.exists_isDoubledHCParameter_of_le`): the column multiplicities are the gaps between
consecutive entries of the sorted vector. Conversely a bound `β` on the entries of the
parameter bounds the weight: it has at most `n · β` boxes in the columns of height below `n`
(`TauCeti.IsDoubledHCParameter.boxesBelow_le`), and its determinant power has absolute value at
most `β` (`TauCeti.IsDoubledHCParameter.abs_le`).

In the application the weights form a family indexed by the infinite places of a CM field, and
the box bound is summed over the places (`TauCeti.sum_boxesBelow_le`).

## Main declarations

* `TauCeti.columnHighestWeight`, `TauCeti.doubledHCParameter`: the highest weight and its doubled
  Harish-Chandra parameter.
* `TauCeti.IsDoubledHCParameter`: `l` lists the doubled parameter of `(κ, e)`.
* `TauCeti.boxesBelow`: the number of boxes in the columns of height below `n`.
* `TauCeti.exists_isDoubledHCParameter_of_le`, `TauCeti.exists_isDoubledHCParameter`: every vector
  with distinct entries of the parity of `n - 1` is a doubled parameter.
* `TauCeti.IsDoubledHCParameter.boxesBelow_le`, `TauCeti.IsDoubledHCParameter.abs_le`: bounds on the
  weight by the entries of its parameter.

## References

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
  Anthropic, PBC), `src/New/Determinant/AuxiliaryForms/RegularParameters.lean`:
  `New.Exchange.exists_isHCParam_of_hasGap`, `New.Exchange.exists_isHCParam_of_le`,
  `New.Exchange.boxes_le_card_mul_of_isHCParam` and `New.Exchange.natAbs_le_of_isHCParam`, with
  the definitions `New.hcParameter` and `New.IsHCParam` of
  `src/Lib/GLn/SchurModule/SchurOrthogonality.lean`.
* A. W. Knapp, *Representation Theory of Semisimple Groups*, Princeton University Press (1986),
  §IX.7 (Harish-Chandra parameters of discrete series and their lowest `K`-types).
-/

public section

open Finset

namespace TauCeti

/-- The entry at the position `p` (counted from `0`) of the highest weight of `U(n)` with `κ h`
columns of height `h` (`0 < h < n`) and the `e`-th power of the determinant:
`e + ∑_{p < h < n} κ h`. -/
def columnHighestWeight (n : ℕ) (κ : ℕ → ℕ) (e : ℤ) (p : ℕ) : ℤ :=
  e + ∑ h ∈ Ioo p n, (κ h : ℤ)

/-- The entry at the position `p` (counted from `0`) of twice the Harish-Chandra parameter
`μ + ρ` of the highest weight `μ` of `U(n)` with column multiplicities `κ` and determinant power
`e`: `2 μ p + n - 1 - 2 p`. -/
def doubledHCParameter (n : ℕ) (κ : ℕ → ℕ) (e : ℤ) (p : ℕ) : ℤ :=
  2 * columnHighestWeight n κ e p + n - 1 - 2 * p

/-- `l : ι → ℤ` lists twice the Harish-Chandra parameter of the weight `(κ, e)` of `U(card ι)` in
some order: its entries are distinct, and each is the entry of `doubledHCParameter` at some
position `p < card ι`. -/
def IsDoubledHCParameter {ι : Type*} [Fintype ι] (κ : ℕ → ℕ) (e : ℤ) (l : ι → ℤ) : Prop :=
  l.Injective ∧ ∀ i, ∃ p < Fintype.card ι, l i = doubledHCParameter (Fintype.card ι) κ e p

/-- The number of boxes in the columns of height below `n` of a diagram with `κ h` columns of
height `h`. -/
def boxesBelow (n : ℕ) (κ : ℕ → ℕ) : ℕ :=
  ∑ h ∈ range n, h * κ h

/-- The doubled parameter in terms of the column multiplicities. -/
theorem doubledHCParameter_eq (n : ℕ) (κ : ℕ → ℕ) (e : ℤ) (p : ℕ) :
    doubledHCParameter n κ e p = 2 * (e + ∑ h ∈ Ioo p n, (κ h : ℤ)) + n - 1 - 2 * p := by
  rw [doubledHCParameter, columnHighestWeight]

/-- The last entry of the doubled parameter, at the position `n - 1`, is `2 e + 1 - n`. -/
theorem doubledHCParameter_sub_one {n : ℕ} (hn : 0 < n) (κ : ℕ → ℕ) (e : ℤ) :
    doubledHCParameter n κ e (n - 1) = 2 * e + 1 - n := by
  have h_empty : Ioo (n - 1) n = ∅ := by grind
  rw [doubledHCParameter_eq, h_empty, sum_empty]
  omega

/-- The doubled parameter sees only the columns of height below `n`. -/
theorem doubledHCParameter_congr {n : ℕ} {κ κ' : ℕ → ℕ} (h : ∀ k < n, κ k = κ' k) (e : ℤ)
    (p : ℕ) : doubledHCParameter n κ e p = doubledHCParameter n κ' e p := by
  rw [doubledHCParameter_eq, doubledHCParameter_eq,
    sum_congr rfl fun k hk => by rw [h k (mem_Ioo.mp hk).2]]

/-- The boxes of the columns of height below `n`, counted by rows: the row `p` has
`∑_{p < h < n} κ h` boxes. -/
theorem boxesBelow_eq_sum_sum_Ioo (n : ℕ) (κ : ℕ → ℕ) :
    boxesBelow n κ = ∑ p ∈ range n, ∑ h ∈ Ioo p n, κ h := by
  induction n with
  | zero => simp [boxesBelow]
  | succ n ih =>
    have h_row (p : ℕ) (hp : p ∈ range n) :
        ∑ h ∈ Ioo p (n + 1), κ h = ∑ h ∈ Ioo p n, κ h + κ n := by
      rw [Ioo_add_one_right_eq_Ioc, sum_Ioo_add_eq_sum_Ioc (mem_range.mp hp)]
    rw [boxesBelow, sum_range_succ, ← boxesBelow, ih, sum_range_succ, Ioo_add_one_right_eq_Ioc,
      Ioc_self, sum_empty, add_zero, sum_congr rfl h_row, sum_add_distrib, sum_const, card_range,
      nsmul_eq_mul, Nat.cast_id]

namespace IsDoubledHCParameter

variable {ι : Type*} [Fintype ι] {κ κ' : ℕ → ℕ} {e : ℤ} {l : ι → ℤ}

/-- Being the doubled parameter of `(κ, e)` depends only on the columns of height below
`card ι`. -/
theorem congr (h : IsDoubledHCParameter κ e l) (hκ : ∀ k < Fintype.card ι, κ k = κ' k) :
    IsDoubledHCParameter κ' e l :=
  ⟨h.1, fun i => by
    obtain ⟨p, hp, hi⟩ := h.2 i
    exact ⟨p, hp, hi.trans (doubledHCParameter_congr hκ e p)⟩⟩

/-- Every entry of the doubled parameter occurs in `l`. -/
theorem exists_eq (h : IsDoubledHCParameter κ e l) {p : ℕ} (hp : p < Fintype.card ι) :
    ∃ i, l i = doubledHCParameter (Fintype.card ι) κ e p := by
  -- The positions of the entries of `l` are distinct, so they fill all of `Fin (card ι)`.
  choose pos hpos hl using h.2
  have h_inj : Function.Injective fun i => (⟨pos i, hpos i⟩ : Fin (Fintype.card ι)) :=
    fun i i' hii' => h.1 <| by rw [hl i, hl i', Fin.mk.inj_iff.mp hii']
  obtain ⟨i, hi⟩ := ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨h_inj, (Fintype.card_fin _).symm⟩).2 ⟨p, hp⟩
  exact ⟨i, by rw [hl i, Fin.mk.inj_iff.mp hi]⟩

/-- If the entries of the doubled parameter of `(κ, e)` are bounded by `β`, each row of the
diagram of the columns of height below `card ι` has at most `β` boxes. -/
theorem sum_Ioo_le (h : IsDoubledHCParameter κ e l) {β : ℕ} (hβ : ∀ i, |l i| ≤ β) {p : ℕ}
    (hp : p < Fintype.card ι) : ∑ k ∈ Ioo p (Fintype.card ι), κ k ≤ β := by
  -- The row length is at most half the difference between the entry at `p` and the last entry.
  obtain ⟨i, hi⟩ := h.exists_eq hp
  obtain ⟨i', hi'⟩ := h.exists_eq (Nat.sub_one_lt_of_lt hp)
  rw [doubledHCParameter_sub_one (by omega)] at hi'
  rw [doubledHCParameter_eq] at hi
  have hβi := _root_.abs_le.mp (hβ i)
  have hβi' := _root_.abs_le.mp (hβ i')
  have h_cast := Nat.cast_sum (R := ℤ) (Ioo p (Fintype.card ι)) κ
  omega

/-- **Boxes of a weight bounded by its parameter.** If `l` is the doubled parameter of `(κ, e)` and
`|l i| ≤ β` for all `i`, then the columns of height below `card ι` have at most `card ι * β`
boxes. -/
theorem boxesBelow_le (h : IsDoubledHCParameter κ e l) {β : ℕ} (hβ : ∀ i, |l i| ≤ β) :
    boxesBelow (Fintype.card ι) κ ≤ Fintype.card ι * β := by
  rw [boxesBelow_eq_sum_sum_Ioo]
  calc ∑ p ∈ range (Fintype.card ι), ∑ k ∈ Ioo p (Fintype.card ι), κ k
      ≤ ∑ _p ∈ range (Fintype.card ι), β :=
        sum_le_sum fun p hp => h.sum_Ioo_le hβ (mem_range.mp hp)
    _ = Fintype.card ι * β := by simp

/-- **The determinant power bounded by the parameter.** If `l` is the doubled parameter of
`(κ, e)`, `ι` is nonempty and `|l i| ≤ β` for all `i`, then `|e| ≤ β`. -/
theorem abs_le [Nonempty ι] (h : IsDoubledHCParameter κ e l) {β : ℕ} (hβ : ∀ i, |l i| ≤ β) :
    |e| ≤ β := by
  -- The first entry of `l` is at least `2 e + card ι - 1` and the last is `2 e + 1 - card ι`.
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  obtain ⟨i, hi⟩ := h.exists_eq hn
  obtain ⟨i', hi'⟩ := h.exists_eq (Nat.sub_one_lt_of_lt hn)
  rw [doubledHCParameter_sub_one hn] at hi'
  rw [doubledHCParameter_eq] at hi
  have h_sum : 0 ≤ ∑ k ∈ Ioo 0 (Fintype.card ι), (κ k : ℤ) := sum_nonneg fun _ _ => by positivity
  have hβi := _root_.abs_le.mp (hβ i)
  have hβi' := _root_.abs_le.mp (hβ i')
  rw [_root_.abs_le]
  constructor <;> omega

end IsDoubledHCParameter

/-- For a finite family of weights `(κ w, e w)` whose doubled parameters `l w` have entries
bounded by `β`, the columns of height below `card ι` have at most `card Φ * card ι * β` boxes in
total. -/
theorem sum_boxesBelow_le {Φ ι : Type*} [Fintype Φ] [Fintype ι] {κ : Φ → ℕ → ℕ} {e : Φ → ℤ}
    {l : Φ → ι → ℤ} (hl : ∀ w, IsDoubledHCParameter (κ w) (e w) (l w)) {β : ℕ}
    (hβ : ∀ w i, |l w i| ≤ β) :
    ∑ w, boxesBelow (Fintype.card ι) (κ w) ≤ Fintype.card Φ * Fintype.card ι * β := by
  calc ∑ w, boxesBelow (Fintype.card ι) (κ w) ≤ ∑ _w : Φ, Fintype.card ι * β :=
        sum_le_sum fun w _ => (hl w).boxesBelow_le (hβ w)
    _ = Fintype.card Φ * Fintype.card ι * β := by simp [mul_assoc]

/-- Let `v` be injective and `g ≤ v i` on a finite set `S`. There are column multiplicities `κ`,
equal to a given `f` above the height `#S`, such that each `v i` with `i ∈ S` is
`g + #S - 1 - p + ∑_{p < k ≤ #S} κ k` for a position `p < #S`. The numbers `κ k`, `k < #S`, are the
gaps between consecutive values of `v` less one, and `κ #S` is the gap between the least value and
`g`. -/
private theorem exists_eq_add_card_add_sum_Ioc {ι : Type*} {v : ι → ℤ} (hv : v.Injective)
    (S : Finset ι) (g : ℤ) (f : ℕ → ℕ) (hg : ∀ i ∈ S, g ≤ v i) :
    ∃ κ : ℕ → ℕ, (∀ k > #S, κ k = f k) ∧
      ∀ i ∈ S, ∃ p < #S, v i + p + 1 = g + (#S + ∑ k ∈ Ioc p #S, κ k : ℕ) := by
  classical
  induction S using induction_on_min_value v generalizing g f with
  | empty => exact ⟨f, fun _ _ ↦ rfl, by simp⟩
  | insert a S ha h_min ih =>
    -- The index `a` of the least value takes the last position.
    have h_gap (i : ι) (hi : i ∈ S) : v a + 1 ≤ v i :=
      (h_min i hi).lt_of_ne (hv.ne (ne_of_mem_of_not_mem hi ha).symm)
    have h_le : g ≤ v a := hg a (mem_insert_self a S)
    obtain ⟨κ, h_high, h_position⟩ :=
      ih (v a + 1) (Function.update f (#S + 1) (v a - g).toNat) h_gap
    have h_new : (κ (#S + 1) : ℤ) = v a - g := by simp [h_high, Int.toNat_sub_of_le h_le]
    simp only [card_insert_of_notMem ha, forall_mem_insert]
    refine ⟨κ, fun k hk ↦ ?_, ⟨#S, Nat.lt_succ_self _, ?_⟩, fun i hi ↦ ?_⟩
    · rw [h_high k (by omega), Function.update_of_ne hk.ne']
    · simp
      omega
    · obtain ⟨p, hp_lt, hp_eq⟩ := h_position i hi
      exact ⟨p, by omega, by grind [sum_Ioc_succ_top]⟩

/-- **Weights of regular parameters, with control of the determinant power.** Let `l : ι → ℤ` have
distinct entries of the parity of `n - 1`, `n = card ι`, and let `2 e₀ + 1 - n ≤ l i` for all `i`
(by parity, `e₀ ≤ ⌊l i / 2⌋ + ⌊n / 2⌋`). For any prescribed numbers `κ₀ h` of columns of the
heights `h > n`, `l` is the doubled Harish-Chandra parameter of a weight `(κ, e₀ + κ n)` with
`κ h = κ₀ h` for `h > n`. The parameter sees neither the columns of height at least `n` nor the
split of the determinant power between `e₀` and the `κ n` full columns. -/
theorem exists_isDoubledHCParameter_of_le {ι : Type*} [Fintype ι] {l : ι → ℤ}
    (hl : l.Injective) (hpar : ∀ i, Even (l i + Fintype.card ι - 1)) {e₀ : ℤ}
    (he : ∀ i, 2 * e₀ + 1 - Fintype.card ι ≤ l i) (κ₀ : ℕ → ℕ) :
    ∃ κ : ℕ → ℕ, (∀ h > Fintype.card ι, κ h = κ₀ h) ∧
      IsDoubledHCParameter κ (e₀ + κ (Fintype.card ι)) l := by
  classical
  set n := Fintype.card ι
  -- By parity `l i` is determined by `u i = (l i + n - 1) / 2`, so the `u i` are distinct.
  have h_half (i : ι) : 2 * ((l i + n - 1) / 2) = l i + n - 1 :=
    Int.two_mul_ediv_two_of_even (hpar i)
  have hu : Function.Injective fun i => (l i + n - 1) / 2 := fun i i' hii' =>
    hl (by have := h_half i; have := h_half i'; simp only at hii'; omega)
  obtain ⟨κ, h_high, h_position⟩ := exists_eq_add_card_add_sum_Ioc hu univ e₀ κ₀ fun i _ => by
    have := h_half i
    have := he i
    omega
  refine ⟨κ, fun h hh => h_high h (by rwa [card_univ]), hl, fun i => ?_⟩
  obtain ⟨p, hp_lt, hp_eq⟩ := h_position i (mem_univ i)
  rw [card_univ] at hp_lt hp_eq
  refine ⟨p, hp_lt, ?_⟩
  have h_split : ∑ k ∈ Ioo p n, κ k + κ n = ∑ k ∈ Ioc p n, κ k := sum_Ioo_add_eq_sum_Ioc hp_lt
  have h_cast := Nat.cast_sum (R := ℤ) (Ioo p n) κ
  have := h_half i
  rw [doubledHCParameter_eq, ← h_cast]
  rw [← h_split] at hp_eq
  push_cast at hp_eq ⊢
  omega

/-- **Every regular parameter is the parameter of a weight.** A vector `l : ι → ℤ` with distinct
entries of the parity of `card ι - 1` is the doubled Harish-Chandra parameter of some weight
`(κ, e)`. -/
theorem exists_isDoubledHCParameter {ι : Type*} [Fintype ι] {l : ι → ℤ} (hl : l.Injective)
    (hpar : ∀ i, Even (l i + Fintype.card ι - 1)) :
    ∃ (κ : ℕ → ℕ) (e : ℤ), IsDoubledHCParameter κ e l := by
  -- Any `e` below all the entries will do, for instance `-∑ i, |l i|`.
  obtain ⟨κ, -, h⟩ := exists_isDoubledHCParameter_of_le hl hpar (e₀ := -∑ i, |l i|) (fun i => by
    have h_single : |l i| ≤ ∑ i, |l i| := single_le_sum (fun i _ => abs_nonneg (l i)) (mem_univ i)
    have : (0 : ℤ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
    have := neg_abs_le (l i)
    have := abs_nonneg (l i)
    omega) 0
  exact ⟨κ, _, h⟩

end TauCeti
