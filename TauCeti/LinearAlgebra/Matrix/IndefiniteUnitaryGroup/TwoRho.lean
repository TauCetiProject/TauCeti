/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

/-!
# Positive-root sums and shifted Harish-Chandra parameters

For an integer vector `l : n → ℤ` (representing a doubled Harish-Chandra parameter `2λ`) and a
binary relation `r : n → n → Prop`, `TauCeti.twoRho l r i` is the sum of the roots `e_i - e_j`
selected by `r` that are positive for `l`:

`twoRho l r i = #{j | r i j ∧ l j < l i} - #{j | r i j ∧ l i < l j}`.

This file proves the monotonicity, symmetry, and norm bound of `twoRho`, together with exact
doubling formulas for the shifted parameter `λ + ρ = (l + 2ρ)/2` (`TauCeti.paramAddRho`) and the
lowest `K`-type `Λ = λ + ρ - 2ρ_c` (`TauCeti.lowestKType`) attached to a sign labelling `ε`.

## Main definitions

* `TauCeti.twoRho`: the positive-root sum `2ρ` restricted to a relation `r`.
* `TauCeti.paramAddRho`: the integer vector `(l i + twoRho l ⊤ i) / 2`.
* `TauCeti.lowestKType`: the lowest `K`-type `paramAddRho l i - twoRho l (fun a b ↦ ε a = ε b) i`.

## Main results

* `TauCeti.twoRho_lt_twoRho`: `twoRho l ⊤` is strictly monotone in the entries of `l`.
* `TauCeti.abs_twoRho_le`: `|twoRho l r i| ≤ Fintype.card n`.
* `TauCeti.twoRho_neg`: `twoRho (-l) r i = -twoRho l r i`.
* `TauCeti.two_mul_paramAddRho`: `2 * paramAddRho l i = l i + twoRho l ⊤ i` for injective `l`
  with `Even (l i + Fintype.card n - 1)`.
* `TauCeti.two_mul_lowestKType`: `2 * lowestKType ε l i = l i + 2ρ_n i - 2ρ_c i`.

## References

* Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0),
  `src/Lib/DiscreteSeries/FlenstedJensen/Defs.lean` (`New.twoRho`, `New.twoRho_lt_twoRho`,
  `New.abs_twoRho_le`, `New.twoRho_neg`, `New.paramAddRho`, `New.two_mul_paramAddRho`,
  `New.HCParam.lowestKType`, `New.two_mul_lowestKType`).
-/

public section

open Finset

namespace TauCeti

variable {n : Type*} [Fintype n]

/-- The vector whose `i`-th entry is `#{j | r i j ∧ l j < l i} - #{j | r i j ∧ l i < l j}`,
the sum of the roots `e_i - e_j` selected by `r` that are positive for `l`. -/
def twoRho (l : n → ℤ) (r : n → n → Prop) [DecidableRel r] (i : n) : ℤ :=
  (#{j : n | r i j ∧ l j < l i} - #{j : n | r i j ∧ l i < l j} : ℤ)

/-- The integer vector `(l i + twoRho l ⊤ i) / 2`, equal to `λ + ρ` for a doubled parameter
`l = 2λ`. -/
def paramAddRho (l : n → ℤ) (i : n) : ℤ :=
  (l i + twoRho l ⊤ i) / 2

/-- For a labelling `ε : n → α` (e.g. signs `ε : n → ℤˣ`), the lowest `K`-type
`Λ = paramAddRho l - 2ρ_c`, where `2ρ_c` sums the compact roots (`ε a = ε b`) positive for `l`. -/
def lowestKType {α : Type*} [DecidableEq α] (ε : n → α) (l : n → ℤ) (i : n) : ℤ :=
  paramAddRho l i - twoRho l (fun a b ↦ ε a = ε b) i

/-- `twoRho l ⊤` preserves strict inequalities between entries of `l`. -/
theorem twoRho_lt_twoRho {l : n → ℤ} {a b : n} (hab : l a < l b) :
    twoRho l ⊤ a < twoRho l ⊤ b := by
  have h_sum (i : n) : twoRho l ⊤ i =
      ∑ j : n, ((if l j < l i then (1 : ℤ) else 0) - (if l i < l j then 1 else 0)) := by
    simp [twoRho, ← sum_boole, sum_sub_distrib]
  rw [h_sum, h_sum]
  exact sum_lt_sum (fun j _ ↦ by split_ifs <;> omega) ⟨a, mem_univ a, by split_ifs <;> omega⟩

/-- Every entry of `twoRho l r` has absolute value at most `Fintype.card n`. -/
theorem abs_twoRho_le (l : n → ℤ) (r : n → n → Prop) [DecidableRel r] (i : n) :
    |twoRho l r i| ≤ Fintype.card n := by
  have h1 : (#{j : n | r i j ∧ l j < l i} : ℤ) ≤ Fintype.card n := by
    exact_mod_cast card_le_univ _
  have h2 : (#{j : n | r i j ∧ l i < l j} : ℤ) ≤ Fintype.card n := by
    exact_mod_cast card_le_univ _
  unfold twoRho
  rw [abs_le]
  omega

/-- Negating `l` negates `twoRho l r`. -/
theorem twoRho_neg (l : n → ℤ) (r : n → n → Prop) [DecidableRel r] (i : n) :
    twoRho (-l) r i = -twoRho l r i := by
  simp [twoRho]

/-- For injective `l` with `Even (l i + Fintype.card n - 1)`, division by `2` in `paramAddRho` is
exact: `2 * paramAddRho l i = l i + twoRho l ⊤ i`. -/
theorem two_mul_paramAddRho {l : n → ℤ} (hl : Function.Injective l) {i : n}
    (hpar : Even (l i + Fintype.card n - 1)) :
    2 * paramAddRho l i = l i + twoRho l ⊤ i := by
  classical
  set below : Finset n := univ.filter (fun j ↦ l j < l i)
  set above : Finset n := univ.filter (fun j ↦ l i < l j)
  have hdisj : Disjoint below above :=
    disjoint_filter.mpr fun j _ hlt hgt ↦ lt_asymm hlt hgt
  have hnot : i ∉ below ∪ above := by simp [below, above]
  have huniv : insert i (below ∪ above) = univ := by
    ext j
    simp only [mem_insert, mem_union, mem_filter, mem_univ, true_and, iff_true, below, above]
    rcases lt_trichotomy (l j) (l i) with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl (hl h)
    · exact Or.inr (Or.inr h)
  have hcard : #below + #above + 1 = Fintype.card n := by
    rw [← card_union_of_disjoint hdisj, ← card_insert_of_notMem hnot, huniv, card_univ]
  have heven : Even (l i + twoRho l ⊤ i) := by
    obtain ⟨k, hk⟩ := hpar
    refine ⟨k - #above, ?_⟩
    simp only [twoRho, Pi.top_apply, Prop.top_eq_true, true_and]
    change l i + (#below - #above : ℤ) = _
    omega
  rw [paramAddRho, Int.mul_ediv_cancel' heven.two_dvd]

/-- For injective `l` with `Even (l i + Fintype.card n - 1)`, twice the lowest `K`-type equals
`l i + 2ρ_n i - 2ρ_c i`. -/
theorem two_mul_lowestKType {α : Type*} [DecidableEq α] (ε : n → α) {l : n → ℤ}
    (hl : Function.Injective l) {i : n} (hpar : Even (l i + Fintype.card n - 1)) :
    2 * lowestKType ε l i =
      l i + twoRho l (fun a b ↦ ε a ≠ ε b) i - twoRho l (fun a b ↦ ε a = ε b) i := by
  have hcount (p : n → Prop) [DecidablePred p] :
      #{j : n | p j} = #{j : n | ε i ≠ ε j ∧ p j} + #{j : n | ε i = ε j ∧ p j} := by
    rw [← card_filter_add_card_filter_not (s := {j | p j}) (fun j ↦ ε i ≠ ε j)]
    simp [filter_filter, and_comm]
  have hsplit : twoRho l ⊤ i =
      twoRho l (fun a b ↦ ε a ≠ ε b) i + twoRho l (fun a b ↦ ε a = ε b) i := by
    simp only [twoRho, Pi.top_apply, Prop.top_eq_true, true_and]
    have h1 := hcount (fun j ↦ l j < l i)
    have h2 := hcount (fun j ↦ l i < l j)
    omega
  rw [lowestKType, mul_sub, two_mul_paramAddRho hl hpar, hsplit]
  ring

end TauCeti
