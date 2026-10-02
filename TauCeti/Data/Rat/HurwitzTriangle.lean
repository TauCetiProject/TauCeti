/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
-- `Multiset.sum` over the branch indices occurs in the statements below, and the additive monoid
-- structure of `ℚ` it sums in comes with the field structure.
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Field.Rat
-- Non-public: `Multiset.card_nsmul_le_sum` and `Multiset.sum_le_card_nsmul` bound that sum by the
-- number of branch points, in the proofs only.
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Tactic.Linarith

/-!
# The sharp reciprocal bound for hyperbolic triples

For natural numbers `a, b, c ≥ 2` with `1/a + 1/b + 1/c < 1`, the deficit
`1 - 1/a - 1/b - 1/c` is at least `1/42`, attained at `(2, 3, 7)`. Applied to
ramification indices, this is the numerical part of Hurwitz's sharp `84(g - 1)`
bound for finite automorphism groups.

The result is stated for arbitrary orders of the three indices.

General **branch data** is a genus `γ` together with a multiset of ramification indices
`e₁, …, e_r ≥ 2`, and its **deficit** is `2γ - 2 + ∑ᵢ (1 - 1/eᵢ)`; for a quotient of a function
field by a finite tame group of automorphisms the deficit is `(2g - 2)/|G|`. The triple bound is
the extremal case of the general one: a positive deficit is at least `1/42`
(`TauCeti.one_div_forty_two_le_hyperbolic_deficit`), because every other shape of branch data
leaves a deficit of at least `1/6`. Only three branch points in genus zero can come that close to
zero, and `(2, 3, 7)` is where it happens.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Exercise 3.18.
-/

public section

namespace TauCeti

/-- For ordered hyperbolic triangle indices, the orbifold deficit is at least `1/42`.
The equality case is realized by `(2, 3, 7)`. -/
private theorem one_div_forty_two_le_hyperbolic_triangle_deficit_ordered
    {a b c : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hhyper : (1 : ℚ) / a + 1 / b + 1 / c < 1) :
    (1 : ℚ) / 42 ≤ 1 - 1 / a - 1 / b - 1 / c := by
  have hc0 : 0 < c := by omega
  -- If the least index is at least four, every reciprocal is at most `1/4`.
  by_cases ha4 : 4 ≤ a
  · have h₁ := one_div_le_one_div_of_le (a := (4 : ℚ)) (b := (a : ℚ))
        (by norm_num) (by exact_mod_cast ha4)
    have h₂ := one_div_le_one_div_of_le (a := (4 : ℚ)) (b := (b : ℚ))
        (by norm_num) (by exact_mod_cast (by omega : 4 ≤ b))
    have h₃ := one_div_le_one_div_of_le (a := (4 : ℚ)) (b := (c : ℚ))
        (by norm_num) (by exact_mod_cast (by omega : 4 ≤ c))
    norm_num at h₁ h₂ h₃ ⊢
    linarith
  -- For least index three, the next is three or at least four.
  by_cases ha3 : a = 3
  · subst a
    by_cases hb4 : 4 ≤ b
    · have h₂ := one_div_le_one_div_of_le (a := (4 : ℚ)) (b := (b : ℚ))
        (by norm_num) (by exact_mod_cast hb4)
      have h₃ := one_div_le_one_div_of_le (a := (4 : ℚ)) (b := (c : ℚ))
        (by norm_num) (by exact_mod_cast (hb4.trans hbc))
      norm_num at h₂ h₃ ⊢
      linarith
    · have hb3 : b = 3 := by omega
      subst b
      have hc4 : 4 ≤ c := by
        by_contra h
        have : c = 3 := by omega
        subst c
        norm_num at hhyper
      have h₃ := one_div_le_one_div_of_le (a := (4 : ℚ)) (b := (c : ℚ))
        (by norm_num) (by exact_mod_cast hc4)
      norm_num at h₃ ⊢
      linarith
  · have ha2 : a = 2 := by omega
    subst a
    -- Only the second indices two, three and four need separate treatment.
    by_cases hb5 : 5 ≤ b
    · have h₂ := one_div_le_one_div_of_le (a := (5 : ℚ)) (b := (b : ℚ))
        (by norm_num) (by exact_mod_cast hb5)
      have h₃ := one_div_le_one_div_of_le (a := (5 : ℚ)) (b := (c : ℚ))
        (by norm_num) (by exact_mod_cast (hb5.trans hbc))
      norm_num at h₂ h₃ ⊢
      linarith
    by_cases hb4 : b = 4
    · subst b
      have hc5 : 5 ≤ c := by
        by_contra h
        have : c = 4 := by omega
        subst c
        norm_num at hhyper
      have h₃ := one_div_le_one_div_of_le (a := (5 : ℚ)) (b := (c : ℚ))
        (by norm_num) (by exact_mod_cast hc5)
      norm_num at h₃ ⊢
      linarith
    by_cases hb3 : b = 3
    · subst b
      have hc7 : 7 ≤ c := by
        by_contra h
        have hc6 : c ≤ 6 := by omega
        have h₃ := one_div_le_one_div_of_le (a := (c : ℚ)) (b := (6 : ℚ))
          (by exact_mod_cast hc0) (by exact_mod_cast hc6)
        simp only [one_div] at hhyper
        norm_num at h₃ hhyper
        linarith
      have h₃ := one_div_le_one_div_of_le (a := (7 : ℚ)) (b := (c : ℚ))
        (by norm_num) (by exact_mod_cast hc7)
      norm_num at h₃ ⊢
      linarith
    · have hb2 : b = 2 := by omega
      subst b
      have hc : 0 ≤ (1 : ℚ) / c := by positivity
      norm_num at hhyper
      linarith

/-- The sharp numerical bound for a hyperbolic triple of natural numbers.
The equality case is realized by the indices `(2, 3, 7)`. -/
theorem one_div_forty_two_le_hyperbolic_triangle_deficit
    {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hhyper : (1 : ℚ) / a + 1 / b + 1 / c < 1) :
    (1 : ℚ) / 42 ≤ 1 - 1 / a - 1 / b - 1 / c := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact one_div_forty_two_le_hyperbolic_triangle_deficit_ordered ha hab hbc hhyper
    · rcases le_total a c with hac | hca
      · have h := one_div_forty_two_le_hyperbolic_triangle_deficit_ordered ha hac hcb
          (by linarith : (1 : ℚ) / a + 1 / c + 1 / b < 1)
        linarith
      · have h := one_div_forty_two_le_hyperbolic_triangle_deficit_ordered hc hca hab
          (by linarith : (1 : ℚ) / c + 1 / a + 1 / b < 1)
        linarith
  · rcases le_total a c with hac | hca
    · have h := one_div_forty_two_le_hyperbolic_triangle_deficit_ordered hb hba hac
        (by linarith : (1 : ℚ) / b + 1 / a + 1 / c < 1)
      linarith
    · rcases le_total b c with hbc | hcb
      · have h := one_div_forty_two_le_hyperbolic_triangle_deficit_ordered hb hbc hca
          (by linarith : (1 : ℚ) / b + 1 / c + 1 / a < 1)
        linarith
      · have h := one_div_forty_two_le_hyperbolic_triangle_deficit_ordered hc hcb hba
          (by linarith : (1 : ℚ) / c + 1 / b + 1 / a < 1)
        linarith

/-- The triangle indices `(2, 3, 7)` attain the bound. -/
theorem two_three_seven_deficit_eq_one_div_forty_two :
    (1 : ℚ) - 1 / 2 - 1 / 3 - 1 / 7 = 1 / 42 := by
  norm_num

section BranchData

variable {e : Multiset ℕ}

/-- The deficit `1 - 1/e` of one branch point of index `e ≥ 2` lies between `1/2` and `1`. -/
private theorem branchDeficit_bounds {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℚ) / 2 ≤ 1 - 1 / n ∧ 1 - 1 / (n : ℚ) ≤ 1 := by
  have hn2 : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hle : (1 : ℚ) / n ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le <;> linarith
  have hnonneg : (0 : ℚ) ≤ 1 / n := by positivity
  constructor <;> linarith

/-- Half the number of branch points is at most the total deficit of the branch points, which in
turn is at most their number. -/
private theorem sum_branchDeficit_bounds (he : ∀ n ∈ e, 2 ≤ n) :
    (e.card : ℚ) / 2 ≤ (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum ∧
      (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum ≤ e.card := by
  have hcard : (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).card = e.card := Multiset.card_map _ _
  constructor
  · have hlow : ∀ x ∈ e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ), (1 : ℚ) / 2 ≤ x := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp hx
      exact (branchDeficit_bounds (he n hn)).1
    have := Multiset.card_nsmul_le_sum hlow
    rw [hcard, nsmul_eq_mul] at this
    linarith
  · have hhigh : ∀ x ∈ e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ), x ≤ 1 := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp hx
      exact (branchDeficit_bounds (he n hn)).2
    have := Multiset.sum_le_card_nsmul _ 1 hhigh
    rwa [hcard, nsmul_eq_mul, mul_one] at this

/-- If every index is two, the total deficit of the branch points is half their number: this is the
boundary case, where four branch points in genus zero give deficit zero. -/
private theorem sum_branchDeficit_of_forall_eq_two (he : ∀ n ∈ e, n = 2) :
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
half of the bound `|G| ≤ 84(g - 1)`. The bound is attained only in genus zero with three branch
points of indices `(2, 3, 7)`; every other shape leaves at least `1/6`. -/
theorem one_div_forty_two_le_hyperbolic_deficit {γ : ℕ} (he : ∀ n ∈ e, 2 ≤ n)
    (hpos : 0 < 2 * (γ : ℚ) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum) :
    (1 : ℚ) / 42 ≤ 2 * (γ : ℚ) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum := by
  obtain ⟨hlow, hhigh⟩ := sum_branchDeficit_bounds he
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
        · have hsum2 := sum_branchDeficit_of_forall_eq_two hall
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
          obtain ⟨htlow, -⟩ := sum_branchDeficit_bounds ht
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

/-- The genus-zero branch data `(2, 3, 7)` attains the bound, so `84(g - 1)` is sharp. -/
theorem hyperbolic_deficit_two_three_seven :
    2 * ((0 : ℕ) : ℚ) - 2 + (({2, 3, 7} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum =
      1 / 42 := by
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton]
  norm_num

end BranchData

end TauCeti
