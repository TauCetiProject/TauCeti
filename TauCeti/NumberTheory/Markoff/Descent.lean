/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TauCeti.NumberTheory.Markoff.Basic

import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.WLOG

/-!
# Descent for positive Markoff triples and Markoff's theorem

Let `1 ≤ a ≤ b ≤ c` be integers with `a² + b² + c² = 3abc` and `(a, b, c) ≠ (1, 1, 1)`. As a
quadratic in its last coordinate, the Markoff equation has the roots `c` and `c' = 3ab - c`, and
the value of that quadratic at `b` is `a² + (2 - 3a) b² ≤ 0`. Hence `c` is the unique largest
coordinate and the other root satisfies `0 < c' ≤ b < c`, with `c' = b` only for `(1, 1, 2)`.
So the Vieta move in the position of the largest coordinate strictly decreases it, while the
other two moves strictly increase it.

Descending along these moves proves **Markoff's theorem**: every positive Markoff triple is
obtained from `(1, 1, 1)` by a finite word in the Vieta moves `R₀, R₁, R₂`, with no coordinate
permutations. Equivalently, the Markoff graph on the positive triples is connected.

## Main results

* `TauCeti.three_mul_mul_sub_le_of_markoff`, `TauCeti.lt_of_markoff`,
  `TauCeti.three_mul_mul_sub_lt_of_markoff`, `TauCeti.three_mul_mul_sub_eq_iff_of_markoff`:
  the descent inequality for an increasing positive Markoff triple.
* `TauCeti.markoffVieta_apply_self_lt`: the move in the position of a largest coordinate
  strictly decreases it, unless the triple is `(1, 1, 1)`.
* `TauCeti.lt_markoffVieta_apply_self_of_ne`: the other two moves strictly increase it.
* `TauCeti.mem_positiveMarkoffTriples_iff_exists_foldr`: Markoff's theorem, the positive
  Markoff triples are exactly the words in the moves applied to `(1, 1, 1)`.
* `TauCeti.markoffGraph_connected`: the Markoff graph is connected.

## References

* Y. Zhang, *Congruence and uniqueness of certain Markoff numbers*, Acta Arith. 128 (2007), §1,
  Theorem A and the descent inequality after it.
* Y. Zhang, *An elementary proof of Markoff conjecture for prime powers*, §3. The descent there
  is on the sum of the coordinates; we descend in the position of the largest coordinate, so no
  rearrangement of the coordinates is needed.
-/

public section

namespace TauCeti

/-! ### The descent inequality -/

section Inequality

variable {a b c : ℤ}

/-- If the quadratic `t² - 3abt + a² + b²` vanishes at `t = b` with `0 < a ≤ b`, then
`a = b = 1`. -/
private lemma eq_one_and_eq_one_of_markoff_root {a b : ℤ} (h : a ^ 2 + 2 * b ^ 2 = 3 * a * b ^ 2)
    (ha : 0 < a) (hab : a ≤ b) : a = 1 ∧ b = 1 := by
  have hb : 0 < b := ha.trans_le hab
  -- `a² - b² = 3 (a - 1) b²`, where the left side is `≤ 0` and the right side is `≥ 0`.
  have hsq : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  have ha1 : a = 1 := by nlinarith [pow_pos hb 2]
  subst ha1
  exact ⟨rfl, by nlinarith⟩

/-- The other root `3ab - c` of a positive Markoff triple is positive. -/
theorem three_mul_mul_sub_pos_of_markoff (h : a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c)
    (ha : 0 < a) (hc : 0 < c) : 0 < 3 * a * b - c := by
  have hmul : c * (3 * a * b - c) = a ^ 2 + b ^ 2 := by linear_combination -h
  have : 0 < c * (3 * a * b - c) := by rw [hmul]; positivity
  exact pos_of_mul_pos_right this hc.le

/-- In an increasing positive Markoff triple `a ≤ b ≤ c` other than `(1, 1, 1)`, the last
coordinate is strictly largest. -/
theorem lt_of_markoff (h : a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c) (ha : 0 < a) (hab : a ≤ b)
    (hbc : b ≤ c) (hne : ¬(a = 1 ∧ b = 1 ∧ c = 1)) : b < c := by
  refine hbc.lt_of_ne fun hbc => hne ?_
  subst hbc
  obtain ⟨rfl, rfl⟩ := eq_one_and_eq_one_of_markoff_root (by linear_combination h) ha hab
  exact ⟨rfl, rfl, rfl⟩

/-- **The descent inequality.** In an increasing positive Markoff triple `a ≤ b ≤ c` other than
`(1, 1, 1)`, the other root `3ab - c` in the last coordinate is at most `b`. -/
theorem three_mul_mul_sub_le_of_markoff (h : a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c)
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (hne : ¬(a = 1 ∧ b = 1 ∧ c = 1)) :
    3 * a * b - c ≤ b := by
  have hlt := lt_of_markoff h ha hab hbc hne
  -- The quadratic `(t - c) (t - (3ab - c))` takes the value `a² + (2 - 3a) b² ≤ 0` at `t = b`.
  have hq : (b - c) * (b - (3 * a * b - c)) = a ^ 2 + (2 - 3 * a) * b ^ 2 := by
    linear_combination -h
  have hsq : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  have hneg : (b - c) * (b - (3 * a * b - c)) ≤ 0 := by
    rw [hq]
    nlinarith [sq_nonneg b]
  by_contra hgt
  have : 0 < (b - c) * (b - (3 * a * b - c)) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  linarith

/-- The other root `3ab - c` equals the middle coordinate `b` only for the triple `(1, 1, 2)`. -/
theorem three_mul_mul_sub_eq_iff_of_markoff (h : a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c)
    (ha : 0 < a) (hab : a ≤ b) : 3 * a * b - c = b ↔ a = 1 ∧ b = 1 ∧ c = 2 := by
  constructor
  · intro hc
    obtain ⟨rfl, rfl⟩ := eq_one_and_eq_one_of_markoff_root
      (by linear_combination (c - b) * hc + h) ha hab
    exact ⟨rfl, rfl, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

/-- In a positive Markoff triple other than `(1, 1, 1)` whose last coordinate `c` is a largest
one, the other root `3ab - c` in that coordinate is strictly smaller than `c`. -/
theorem three_mul_mul_sub_lt_of_markoff (h : a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c)
    (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) (hbc : b ≤ c) (hne : ¬(a = 1 ∧ b = 1 ∧ c = 1)) :
    3 * a * b - c < c := by
  wlog hab : a ≤ b generalizing a b
  · have := this (b := a) (a := b) (by linear_combination h) hb ha hbc hac (by tauto) (by omega)
    linarith
  exact (three_mul_mul_sub_le_of_markoff h ha hab hbc hne).trans_lt
    (lt_of_markoff h ha hab hbc hne)

end Inequality

/-! ### Descent along the Vieta moves -/

variable {x : Fin 3 → ℤ} {i j : Fin 3}

/-- The Markoff equation read with the `i`-th coordinate in the last position. -/
private lemma markoff_rotate {x : Fin 3 → ℤ} (hx : x ∈ markoffSet ℤ) (i : Fin 3) :
    x (i + 1) ^ 2 + x (i + 2) ^ 2 + x i ^ 2 = 3 * x (i + 1) * x (i + 2) * x i := by
  rw [mem_markoffSet] at hx
  fin_cases i <;> simp <;> linear_combination hx

/-- **Descent.** If `x_i` is a largest coordinate of a positive Markoff triple `x ≠ (1, 1, 1)`,
then the Vieta move `R_i` strictly decreases it. -/
theorem markoffVieta_apply_self_lt (hx : x ∈ positiveMarkoffTriples) (hmax : ∀ j, x j ≤ x i)
    (hne : x ≠ 1) : markoffVieta i x i < x i := by
  obtain ⟨hx, hpos⟩ := mem_positiveMarkoffTriples.mp hx
  rw [markoffVieta_apply_self]
  refine three_mul_mul_sub_lt_of_markoff (markoff_rotate hx i) (hpos _) (hpos _) (hmax _)
    (hmax _) fun ⟨h1, h2, h3⟩ => hne ?_
  ext j
  fin_cases i <;> fin_cases j <;> simp_all

/-- If `x_i` is a largest coordinate of a triple of positive integers, for instance of a positive
Markoff triple, the Vieta moves in the other two positions produce a coordinate strictly larger
than `x_i`. -/
theorem lt_markoffVieta_apply_self_of_ne (hpos : ∀ k, 0 < x k) (hmax : ∀ k, x k ≤ x i)
    (hji : j ≠ i) : x i < markoffVieta j x j := by
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  rw [markoffVieta_apply_self]
  fin_cases i <;> fin_cases j <;> simp at hji hmax ⊢ <;> nlinarith [hmax 0, hmax 1, hmax 2]

/-- Every positive Markoff triple other than `(1, 1, 1)` has a Vieta move that strictly decreases
one of its coordinates. -/
theorem exists_markoffVieta_apply_self_lt (hx : x ∈ positiveMarkoffTriples) (hne : x ≠ 1) :
    ∃ i, markoffVieta i x i < x i := by
  obtain ⟨i, hi⟩ := Finite.exists_max x
  exact ⟨i, markoffVieta_apply_self_lt hx hi hne⟩

/-! ### Markoff's theorem -/

/-- Every word in the Vieta moves applied to `(1, 1, 1)` is a positive Markoff triple. -/
theorem foldr_markoffVieta_mem_positiveMarkoffTriples (l : List (Fin 3)) :
    l.foldr markoffVieta 1 ∈ positiveMarkoffTriples := by
  induction l with
  | nil => exact one_mem_positiveMarkoffTriples
  | cons i l ih => exact markoffVieta_mem_positiveMarkoffTriples ih i

/-- **Markoff's theorem.** Every positive Markoff triple `x` is obtained from `(1, 1, 1)` by a
finite word in the Vieta moves: `x = R_{i₁} (R_{i₂} ⋯ (R_{i_k} (1, 1, 1)))`. No coordinate
permutation is needed. -/
theorem exists_foldr_markoffVieta_eq (hx : x ∈ positiveMarkoffTriples) :
    ∃ l : List (Fin 3), l.foldr markoffVieta 1 = x := by
  -- Strong induction on the sum of the coordinates, which is positive.
  induction hn : (∑ j, x j).toNat using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  by_cases h1 : x = 1
  · exact ⟨[], h1.symm⟩
  obtain ⟨i, hi⟩ := exists_markoffVieta_apply_self_lt hx h1
  have hx' := markoffVieta_mem_positiveMarkoffTriples hx i
  have hpos : 0 < ∑ j, markoffVieta i x j :=
    Finset.sum_pos (fun j _ => (mem_positiveMarkoffTriples.mp hx').2 j) ⟨0, by simp⟩
  have hlt : (∑ j, markoffVieta i x j).toNat < n := by
    rw [← hn]
    rw [sum_markoffVieta] at hpos ⊢
    omega
  obtain ⟨l, hl⟩ := ih _ hlt hx' rfl
  exact ⟨i :: l, by rw [List.foldr_cons, hl, markoffVieta_markoffVieta]⟩

/-- **Markoff's theorem**, as a characterisation: the positive Markoff triples are exactly the
words in the Vieta moves applied to `(1, 1, 1)`. -/
theorem mem_positiveMarkoffTriples_iff_exists_foldr :
    x ∈ positiveMarkoffTriples ↔ ∃ l : List (Fin 3), l.foldr markoffVieta 1 = x :=
  ⟨exists_foldr_markoffVieta_eq, fun ⟨l, hl⟩ =>
    hl ▸ foldr_markoffVieta_mem_positiveMarkoffTriples l⟩

/-- The integer Markoff graph is connected: every positive Markoff triple is joined to
`(1, 1, 1)` by a path of Vieta moves. -/
theorem markoffGraph_connected : markoffGraph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨1, one_mem_positiveMarkoffTriples⟩, fun ⟨x, hx⟩ => ?_⟩
  obtain ⟨l, rfl⟩ := exists_foldr_markoffVieta_eq hx
  induction l with
  | nil => rfl
  | cons i l ih =>
    refine (ih (foldr_markoffVieta_mem_positiveMarkoffTriples l)).trans ?_
    by_cases heq : (⟨_, foldr_markoffVieta_mem_positiveMarkoffTriples l⟩ :
        positiveMarkoffTriples) = ⟨_, foldr_markoffVieta_mem_positiveMarkoffTriples (i :: l)⟩
    · rw [heq]
    · exact (markoffGraph_adj.mpr ⟨heq, i, rfl⟩).reachable

/-! ### Examples -/

/-- `(2, 5, 29) = R₂ (R₁ (R₀ (1, 1, 1)))`: `R₀` gives `(2, 1, 1)`, `R₁` gives `(2, 5, 1)` and
`R₂` gives `(2, 5, 29)`. -/
example : [2, 1, 0].foldr markoffVieta (1 : Fin 3 → ℤ) = ![2, 5, 29] := by
  ext j
  fin_cases j <;> simp [markoffVieta_apply_of_ne]

/-- The triple `(3, 3, 3)` solves the coefficient-one equation `x² + y² + z² = xyz`, but it is
not a point of the coefficient-three Markoff surface. -/
example : ![(3 : ℤ), 3, 3] ∉ markoffSet ℤ := by
  simp [mem_markoffSet]

end TauCeti
