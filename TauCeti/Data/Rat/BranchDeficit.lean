/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.one_div_forty_two_le_hyperbolic_triangle_deficit` is the extremal case of the bound
-- below.
public import TauCeti.Data.Rat.HurwitzTriangle
-- `Multiset.sum` over the branch indices occurs in the statements below, and the ordered field
-- structure of `ℚ` it sums in is what the estimates are read in.
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Order.Field.Rat
-- Non-public: `Multiset.card_nsmul_le_sum` and `Multiset.sum_le_card_nsmul` bound that sum by the
-- number of branch points, and the arithmetic is closed by `linarith` and `positivity`, in the
-- proofs only.
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The deficit of branch data

**Branch data** is a genus `γ` together with a multiset of ramification indices `e₁, …, e_r`, each
at least two, and its **deficit** is

`2γ - 2 + ∑ᵢ (1 - 1/eᵢ)`.

For a quotient of a function field of genus `g` by a finite tame group of automorphisms `G`,
Riemann--Hurwitz makes the deficit of the branch data of `F / F^G` equal to `(2g - 2)/|G|`, so a
lower bound on a positive deficit is an upper bound on `|G|`.

The sharp bound is `1/42`, attained by the genus-zero data `(2, 3, 7)`. It is reached only there:
each branch point contributes between `1/2` and `1`, so genus at least two leaves at least `2` and
genus one at least `1/2`, while genus zero needs more than two branch points, and with four or more
of them a positive deficit is at least `1/6`. Only genus-zero data with exactly three branch points
comes closer, and there the deficit `1 - 1/a - 1/b - 1/c` is the hyperbolic triple bound of
`TauCeti/Data/Rat/HurwitzTriangle.lean`, whose values do drop below `1/6` — `(2, 3, 8)` gives
`1/24` — down to `1/42`.

## Main results

* `TauCeti.one_div_forty_two_le_hyperbolic_deficit`: a positive deficit is at least `1/42`.
* `TauCeti.hyperbolic_deficit_two_three_seven`: the genus-zero data `(2, 3, 7)` attains it.
* `TauCeti.half_le_one_sub_one_div` and `Nat.one_sub_one_div_le_one`: the contribution of one
  branch point, with the sums `TauCeti.card_div_two_le_sum_one_sub_one_div`,
  `Multiset.sum_one_sub_one_div_le_card` and `TauCeti.sum_one_sub_one_div_eq_card_div_two`.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Exercise 3.18.
-/

public section

/-- The contribution `1 - 1/n` of a branch point is at most `1`. -/
theorem Nat.one_sub_one_div_le_one (n : ℕ) : 1 - 1 / (n : ℚ) ≤ 1 := by
  have hnonneg : (0 : ℚ) ≤ 1 / n := by positivity
  linarith

/-- The total contribution of the branch points is at most their number. -/
theorem Multiset.sum_one_sub_one_div_le_card (e : Multiset ℕ) :
    (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum ≤ e.card := by
  have hcard : (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).card = e.card := Multiset.card_map _ _
  have hhigh : ∀ x ∈ e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ), x ≤ 1 := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp hx
    exact Nat.one_sub_one_div_le_one n
  have := Multiset.sum_le_card_nsmul _ 1 hhigh
  rwa [hcard, nsmul_eq_mul, mul_one] at this

namespace TauCeti

variable {e : Multiset ℕ}

/-- The contribution `1 - 1/n` of a branch point of index at least two is at least `1/2`. -/
theorem half_le_one_sub_one_div {n : ℕ} (hn : 2 ≤ n) : (1 : ℚ) / 2 ≤ 1 - 1 / n := by
  have hn2 : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hle : (1 : ℚ) / n ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le <;> linarith
  linarith

/-- Half the number of branch points is at most their total contribution. -/
theorem card_div_two_le_sum_one_sub_one_div (he : ∀ n ∈ e, 2 ≤ n) :
    (e.card : ℚ) / 2 ≤ (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum := by
  have hcard : (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).card = e.card := Multiset.card_map _ _
  have hlow : ∀ x ∈ e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ), (1 : ℚ) / 2 ≤ x := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp hx
    exact half_le_one_sub_one_div (he n hn)
  have := Multiset.card_nsmul_le_sum hlow
  rw [hcard, nsmul_eq_mul] at this
  linarith

/-- If every index is two, the total contribution of the branch points is half their number: this
is the boundary case, where four branch points in genus zero give deficit zero. -/
theorem sum_one_sub_one_div_eq_card_div_two (he : ∀ n ∈ e, n = 2) :
    (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum = (e.card : ℚ) / 2 := by
  have hconst : (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)) = Multiset.replicate e.card ((1 : ℚ) / 2) := by
    rw [← Multiset.card_map (fun n : ℕ ↦ 1 - 1 / (n : ℚ)) e]
    refine Multiset.eq_replicate_card.mpr fun x hx ↦ ?_
    obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp hx
    rw [he n hn]
    norm_num
  rw [hconst, Multiset.sum_replicate, nsmul_eq_mul, mul_one_div]

/-- **The sharp numerical bound for hyperbolic branch data**: for a genus `γ` and ramification
indices all at least two, a positive deficit `2γ - 2 + ∑ᵢ (1 - 1/eᵢ)` is at least `1/42`.

For a function field of genus `g` and a finite tame group of automorphisms `G`, Riemann--Hurwitz
makes the deficit of the branch data of `F / F^G` equal to `(2g - 2)/|G|`, so this is the numerical
half of the bound `|G| ≤ 84 (g - 1)`. Outside genus-zero data with exactly three branch points a
positive deficit is at least `1/6`; the smaller values, down to `1/42` at `(2, 3, 7)`, are the
hyperbolic triples. -/
theorem one_div_forty_two_le_hyperbolic_deficit {γ : ℕ} (he : ∀ n ∈ e, 2 ≤ n)
    (hpos : 0 < 2 * (γ : ℚ) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum) :
    (1 : ℚ) / 42 ≤ 2 * (γ : ℚ) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum := by
  have hlow := card_div_two_le_sum_one_sub_one_div he
  have hhigh := Multiset.sum_one_sub_one_div_le_card e
  have hcard0 : (0 : ℚ) ≤ e.card := by positivity
  rcases Nat.lt_or_ge γ 2 with hγ | hγ
  · rcases Nat.lt_or_ge γ 1 with hγ0 | hγ1
    -- Genus zero: there are at least three branch points.
    · have hγ0 : γ = 0 := by omega
      subst hγ0
      have hsum : 2 < (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum := by push_cast at hpos ⊢; linarith
      have hcard3 : 3 ≤ e.card := by
        have h2 : (2 : ℚ) < e.card := lt_of_lt_of_le hsum hhigh
        have : (2 : ℕ) < e.card := by exact_mod_cast h2
        omega
      rcases eq_or_lt_of_le hcard3 with hc3 | hc4
      -- Exactly three: the triple bound.
      · obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp hc3.symm
        have ha : 2 ≤ a := he a (by simp)
        have hb : 2 ≤ b := he b (by simp)
        have hc : 2 ≤ c := he c (by simp)
        simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
          Multiset.map_singleton, Multiset.sum_singleton] at hpos ⊢
        have hhyper : (1 : ℚ) / a + 1 / b + 1 / c < 1 := by push_cast at hpos; linarith
        have := one_div_forty_two_le_hyperbolic_triangle_deficit ha hb hc hhyper
        push_cast
        linarith
      -- At least four: either every index is two, and then there are at least five, or one index
      -- is at least three.
      · by_cases hall : ∀ n ∈ e, n = 2
        · have hsum2 := sum_one_sub_one_div_eq_card_div_two hall
          have hcard5 : 5 ≤ e.card := by
            have h4 : (4 : ℚ) < e.card := by rw [hsum2] at hsum; linarith
            have : (4 : ℕ) < e.card := by exact_mod_cast h4
            omega
          have : (5 : ℚ) ≤ e.card := by exact_mod_cast hcard5
          rw [hsum2]
          push_cast
          linarith
        · simp only [not_forall] at hall
          obtain ⟨n, hn, hne2⟩ := hall
          obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hn
          have hn3 : 3 ≤ n := by
            have := he n hn
            omega
          have hn3' : (3 : ℚ) ≤ n := by exact_mod_cast hn3
          have hdef : (2 : ℚ) / 3 ≤ 1 - 1 / n := by
            have : (1 : ℚ) / n ≤ 1 / 3 := by apply one_div_le_one_div_of_le <;> linarith
            linarith
          have ht : ∀ m ∈ t, 2 ≤ m := fun m hm ↦ he m (Multiset.mem_cons_of_mem hm)
          have htlow := card_div_two_le_sum_one_sub_one_div ht
          have htcard : (3 : ℚ) ≤ t.card := by
            have : 3 ≤ t.card := by
              have := hc4
              simp only [Multiset.card_cons] at this
              omega
            exact_mod_cast this
          simp only [Multiset.map_cons, Multiset.sum_cons]
          push_cast
          linarith
    -- Genus one: a positive deficit needs a branch point.
    · have hγ1 : γ = 1 := by omega
      subst hγ1
      have hne : e ≠ 0 := by
        intro h0
        rw [h0] at hpos
        simp at hpos
      have hcard1 : (1 : ℚ) ≤ e.card := by
        have : 1 ≤ e.card := Multiset.card_pos.mpr hne
        exact_mod_cast this
      push_cast
      linarith
  -- Genus at least two: the deficit is already at least two.
  · have hγ2 : (2 : ℚ) ≤ γ := by exact_mod_cast hγ
    have hsum0 : (0 : ℚ) ≤ (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum := le_trans (by positivity) hlow
    linarith

/-- The genus-zero branch data `(2, 3, 7)` attains the bound `1/42`, so the constant in
`TauCeti.one_div_forty_two_le_hyperbolic_deficit` cannot be improved.  Whether a function field and
a group of automorphisms realize this datum is a separate question. -/
theorem hyperbolic_deficit_two_three_seven :
    2 * ((0 : ℕ) : ℚ) - 2 + (({2, 3, 7} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum =
      1 / 42 := by
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton]
  norm_num

end TauCeti
