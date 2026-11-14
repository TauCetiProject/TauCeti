/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Multiset.Filter
public import TauCeti.Algebra.Order.Field.HurwitzTriangle
public import TauCeti.Data.Set.Multiset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sharp lower bounds and equality cases for hyperbolic orbifold signature deficits

An orbifold signature `(g; m₁, …, m_r; c)` consists of a genus `g : ℕ`, a multiset `e` of elliptic
orders, and a cusp count `c : ℕ`. Its **orbifold deficit** (the negative orbifold Euler
characteristic) in a linearly ordered field `K` is

`2g - 2 + ∑ᵢ (1 - 1 / mᵢ) + c`,

or more generally `-(χ : K) + ∑ᵢ (1 - 1 / mᵢ) + c` for an integer Euler characteristic `χ ≤ 2`
(with `χ = 2 - 2g` in the orientable surface case). For a cofinite Fuchsian group `Γ` of signature
`(g; m₁, …, m_r; c)`, the Gauss–Bonnet area formula expresses the hyperbolic covolume of `Γ` as
`2π` times this deficit, while positivity of covolume forces the deficit to be strictly positive;
for a finite tame group of automorphisms of a function field of genus `g ≥ 2`, Riemann–Hurwitz
identifies the cuspless (`c = 0`) deficit with `(2g - 2) / |G|`, yielding Hurwitz's `84(g - 1)`
bound (`TauCeti.card_le_eighty_four_mul_sub_one`).

This file proves the two sharp positive lower bounds on orbifold deficits, their spectral gaps to
the second-smallest values, and their exact equality characterizations, in an arbitrary linearly
ordered field `K`:

1. **Unconditional minimum `1/42` (Siegel / Hurwitz)**: whenever `χ ≤ 2` and the deficit is
   positive, it is at least `1/42`, attained uniquely (among multisets `e` with `1 ∉ e`) at `χ = 2`
   (`g = 0`), `c = 0` and `e = {2, 3, 7}`. Every other positive deficit with `χ ≤ 2` and `1 ∉ e` is
   at least `1/24`, attained at `(0; 2, 3, 8; 0)`. When `c ≥ 1`, replacing each cusp by an elliptic
   point of sufficiently large order `m` lowers the deficit by `c / m` while keeping it positive,
   reducing the `1/42` bound to the cuspless case.
2. **Cusped minimum `1/6`**: whenever `χ ≤ 2`, `1 ≤ c`, and the deficit is positive, it is at least
   `1/6`, attained uniquely (among multisets `e` with `1 ∉ e`) at `χ = 2` (`g = 0`), `c = 1` and
   `e = {2, 3}` (the signature of `PSL(2, ℤ)`). Every other positive cusped deficit with `χ ≤ 2` and
   `1 ∉ e` is at least `1/4`, attained at `(0; 2, 4; 1)`. The hypothesis `1 ≤ c` is essential for
   uniqueness: without cusps, `(0; 2, 2, 2, 3; 0)` also has deficit `1/6`.

Because `1 - 1 / (1 : K) = 0` and `1 - 1 / (0 : K) = 1`
(`Multiset.sum_one_sub_one_div_eq_sum_filter_add_count_zero`), the lower bounds `1/42` and `1/6`
(and hence `TauCeti.card_le_eighty_four_mul_sub_one`) hold for all multisets `e : Multiset ℕ` and
all order maps `f : α → ℕ` without any lower-bound or finiteness assumptions. The multiset
uniqueness and spectral-gap theorems require only `1 ∉ e`. Combining the multiset bounds and
characterizations with `Set.exists_finsum_mem_comp_eq_multiset_sum_map`,
`Set.Finite.finsum_mem_comp_eq_multiset_sum_map`, and `Set.Finite.map_toFinset_val_eq_iff` yields
the unconditional `finsum` lower bounds and, under `hs : s.Finite` and `∀ x ∈ s, f x ≠ 1`, the
`finsum` equality characterizations over an orbit set `s : Set α` with stabilizer-order function
`f : α → ℕ`, characterizing the minimal signatures directly via the fibre cardinalities
`Nat.card {x // x ∈ s ∧ f x = m}`.

## Main results

* `Multiset.sum_one_sub_one_div_nonneg`, `Multiset.sum_one_sub_one_div_le_card`,
  `Multiset.sum_map_add_replicate_one_sub_one_div`,
  `Multiset.sum_one_sub_one_div_eq_sum_filter_add_count_zero`,
  `TauCeti.half_le_one_sub_one_div`, `TauCeti.card_div_two_le_sum_one_sub_one_div`, and
  `TauCeti.sum_one_sub_one_div_eq_card_div_two`: bounds and identities for elliptic defect sums.
* `TauCeti.one_div_forty_two_le_orbifold_deficit`,
  `TauCeti.one_div_twenty_four_le_orbifold_deficit_of_ne`, and
  `TauCeti.orbifold_deficit_eq_one_div_forty_two_iff`: Siegel's `1/42` lower bound, the `1/24` gap,
  and the `(0; 2, 3, 7; 0)` equality characterization, with cuspless specializations
  `TauCeti.one_div_forty_two_le_hyperbolic_deficit`,
  `TauCeti.one_div_twenty_four_le_hyperbolic_deficit_of_ne`,
  `TauCeti.hyperbolic_deficit_eq_one_div_forty_two_iff`, and Hurwitz's `84(g - 1)` bound
  `TauCeti.card_le_eighty_four_mul_sub_one`.
* `TauCeti.one_div_six_le_orbifold_deficit`,
  `TauCeti.one_div_four_le_orbifold_deficit_of_ne`, and
  `TauCeti.orbifold_deficit_eq_one_div_six_iff`: the `1/6` lower bound, `1/4` gap, and
  `(0; 2, 3; 1)` equality characterization for cusped signatures (`1 ≤ c`).
* `TauCeti.one_div_forty_two_le_orbifold_deficit_finsum`,
  `TauCeti.orbifold_deficit_finsum_eq_one_div_forty_two_iff`,
  `TauCeti.one_div_six_le_orbifold_deficit_finsum`, and
  `TauCeti.orbifold_deficit_finsum_eq_one_div_six_iff`: `finsum` and fibre-count forms.

## References

* C. L. Siegel, *Some remarks on discontinuous groups*, Ann. of Math. (2) 46 (1945), 708–718.
* G. Martin, *The geometry and arithmetic of Kleinian groups*, Handbook of Group Actions, Vol. III,
  ALM 40 (2018), Theorems 2.1–2.2.
* S. Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago Press, 1992,
  §4.3.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Exercise 3.18.
-/

public section

namespace Multiset

variable {K : Type*}

/-- Every term `1 - 1 / n` for `n : ℕ` is nonnegative in a linearly ordered field, so the total
elliptic defect `(e.map fun n ↦ 1 - 1 / n).sum` is nonnegative. -/
theorem sum_one_sub_one_div_nonneg [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (e : Multiset ℕ) :
    0 ≤ (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  refine Multiset.sum_nonneg fun x hx ↦ ?_
  obtain ⟨n, _, rfl⟩ := Multiset.mem_map.mp hx
  exact Nat.one_sub_one_div_cast_nonneg n

/-- The total contribution of the branch points is at most their number. -/
theorem sum_one_sub_one_div_le_card [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (e : Multiset ℕ) :
    (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum ≤ e.card := by
  have hcard : (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).card = e.card := Multiset.card_map _ _
  have hhigh : ∀ x ∈ e.map fun n : ℕ ↦ 1 - 1 / (n : K), x ≤ 1 := by
    intro x hx
    obtain ⟨n, _, rfl⟩ := Multiset.mem_map.mp hx
    exact Nat.one_sub_one_div_cast_le_one n
  have := Multiset.sum_le_card_nsmul _ 1 hhigh
  rwa [hcard, nsmul_eq_mul, mul_one] at this

/-- **Cusp-replacement identity.** Appending `c` elliptic orders equal to `m` adds `c - c / m` to
the defect sum: replacing `c` cusps (each contributing `1`) by `c` elliptic points of order `m`
subtracts `c / m` from the orbifold deficit. -/
theorem sum_map_add_replicate_one_sub_one_div [DivisionRing K] (e : Multiset ℕ) (c m : ℕ) :
    ((e + Multiset.replicate c m).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum =
      (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c - (c : K) / m := by
  rw [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate, Multiset.sum_replicate,
    nsmul_eq_mul, mul_sub, mul_one, mul_one_div, add_sub_assoc]

/-- Separating out `0` and `1` from `(e.map fun n ↦ 1 - 1 / n).sum`: each `1` contributes `0`, while
each `0` contributes `1 - 1 / 0 = 1`. -/
theorem sum_one_sub_one_div_eq_sum_filter_add_count_zero [DivisionRing K] (e : Multiset ℕ) :
    (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum =
      ((e.filter (2 ≤ ·)).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + e.count 0 := by
  induction e using Multiset.induction_on with
  | empty => simp
  | cons a e ih =>
    rcases (by omega : a = 0 ∨ a = 1 ∨ 2 ≤ a) with rfl | rfl | ha2
    · have h0 : ¬ 2 ≤ (0 : ℕ) := by decide
      simp only [Multiset.map_cons, Nat.cast_zero, div_zero, sub_zero, Multiset.sum_cons,
        Multiset.filter_cons_of_neg _ h0, Multiset.count_cons_self, Nat.cast_add, Nat.cast_one, ih]
      abel
    · have h1 : ¬ 2 ≤ (1 : ℕ) := by decide
      have h01 : (0 : ℕ) ≠ 1 := by decide
      simp only [Multiset.map_cons, Nat.cast_one, div_one, sub_self, Multiset.sum_cons, zero_add,
        Multiset.filter_cons_of_neg _ h1, Multiset.count_cons_of_ne h01, ih]
    · have h0a : (0 : ℕ) ≠ a := by omega
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.filter_cons_of_pos _ ha2,
        Multiset.count_cons_of_ne h0a, ih, add_assoc]

end Multiset

namespace TauCeti

section CharZero

variable {K : Type*} [DivisionRing K] [CharZero K]

/-- If every index is two, the total contribution of the branch points is half their number: this
is the boundary case, where four branch points in genus zero give deficit zero. -/
theorem sum_one_sub_one_div_eq_card_div_two {e : Multiset ℕ} (he : ∀ n ∈ e, n = 2) :
    (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum = (e.card : K) / 2 := by
  have hconst : (e.map fun n : ℕ ↦ 1 - 1 / (n : K)) =
      Multiset.replicate e.card ((1 : K) / 2) := by
    rw [← Multiset.card_map (fun n : ℕ ↦ 1 - 1 / (n : K)) e]
    refine Multiset.eq_replicate_card.mpr fun x hx ↦ ?_
    obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp hx
    rw [he n hn]
    norm_num
  rw [hconst, Multiset.sum_replicate, nsmul_eq_mul, mul_one_div]

private theorem ratCast_neg_intCast_add_sum_add_natCast (χ : ℤ) (e : Multiset ℕ) (c : ℕ) :
    ((-(χ : ℚ) + (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum + c : ℚ) : K) =
      -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  simp

end CharZero

private theorem filter_two_le_eq_self_of_notMem_one {e : Multiset ℕ}
    (he : 1 ∉ e) (hz : e.count 0 = 0) :
    e.filter (2 ≤ ·) = e := by
  rw [Multiset.filter_eq_self]
  intro n hn
  have hn1 : n ≠ 1 := fun h ↦ he (h ▸ hn)
  have hn0 : n ≠ 0 := fun h ↦ Multiset.count_eq_zero.mp hz (h ▸ hn)
  omega

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Core defect estimates for multisets with entries at least `2` -/

/-- The contribution `1 - 1 / n` of a branch point of index at least two is at least `1 / 2`. -/
theorem half_le_one_sub_one_div {n : ℕ} (hn : 2 ≤ n) : (1 : K) / 2 ≤ 1 - 1 / n := by
  have hn2 : (2 : K) ≤ n := by exact_mod_cast hn
  linarith [one_div_le_one_div_of_le (by norm_num : (0 : K) < 2) hn2]

/-- Half the number of branch points is at most their total contribution when every index is at
least two. -/
theorem card_div_two_le_sum_one_sub_one_div {e : Multiset ℕ} (he : ∀ n ∈ e, 2 ≤ n) :
    (e.card : K) / 2 ≤ (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  have hcard : (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).card = e.card := Multiset.card_map _ _
  have hlow : ∀ x ∈ e.map fun n : ℕ ↦ 1 - 1 / (n : K), (1 : K) / 2 ≤ x := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp hx
    exact half_le_one_sub_one_div (he n hn)
  have := Multiset.card_nsmul_le_sum hlow
  rw [hcard, nsmul_eq_mul] at this
  linarith

private theorem one_div_four_le_neg_one_add_sum_of_two_le_of_ne {e : Multiset ℕ}
    (he : ∀ n ∈ e, 2 ≤ n)
    (hpos : 0 < -1 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum)
    (hne : e ≠ {2, 3}) :
    (1 : K) / 4 ≤ -1 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  have hlow : (e.card : K) / 2 ≤ (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum :=
    card_div_two_le_sum_one_sub_one_div he
  have hhigh : (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum ≤ e.card := e.sum_one_sub_one_div_le_card
  have hcard2 : 2 ≤ e.card := by
    have h1 : (1 : K) < e.card := by linarith
    have : (1 : ℕ) < e.card := by exact_mod_cast h1
    omega
  rcases eq_or_lt_of_le hcard2 with hc2 | hc3
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hc2.symm
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton] at hpos ⊢
    have hhyper : (1 : K) / a + 1 / b < 1 := by linarith
    linarith [one_div_four_le_hyperbolic_pair_deficit_of_ne hhyper hne]
  · have hc3' : (3 : K) ≤ e.card := by exact_mod_cast hc3
    linarith

/-- With at least four branch points of index at least `2` and sum strictly above `2`, the
genus-zero deficit `-2 + ∑ (1 - 1 / n)` is at least `1 / 6` (attained at `{2, 2, 2, 3}`). -/
private theorem one_div_six_le_neg_two_add_sum_of_four_le_card {e : Multiset ℕ}
    (he : ∀ n ∈ e, 2 ≤ n) (hc4 : 4 ≤ e.card)
    (hsum : 2 < (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum) :
    (1 : K) / 6 ≤ -2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  rcases lt_or_eq_of_le hc4 with hc5 | hc4'
  · have h5 : (5 : K) ≤ e.card := by exact_mod_cast hc5
    linarith [card_div_two_le_sum_one_sub_one_div (K := K) he]
  · obtain ⟨n, hn, hne2⟩ : ∃ n ∈ e, n ≠ 2 := by
      by_contra! hall
      rw [sum_one_sub_one_div_eq_card_div_two (K := K) hall, ← hc4'] at hsum
      norm_num at hsum
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hn
    have hn3 : (3 : K) ≤ n := by
      have := he n hn
      exact_mod_cast (by omega : 3 ≤ n)
    have hdef : (2 : K) / 3 ≤ 1 - 1 / n := by
      linarith [one_div_le_one_div_of_le (by norm_num : (0 : K) < 3) hn3]
    have ht : ∀ m ∈ t, 2 ≤ m := fun m hm ↦ he m (Multiset.mem_cons_of_mem hm)
    have ht3 : (t.card : K) = 3 := by
      have : t.card = 3 := by simpa using hc4'.symm
      exact_mod_cast this
    simp only [Multiset.map_cons, Multiset.sum_cons]
    linarith [card_div_two_le_sum_one_sub_one_div (K := K) ht, ht3, hdef]

private theorem one_div_twenty_four_le_neg_intCast_add_sum_of_two_le_of_ne
    {χ : ℤ} {e : Multiset ℕ} (hχ : χ ≤ 2) (he : ∀ n ∈ e, 2 ≤ n)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum)
    (hne : ¬ (χ = 2 ∧ e = {2, 3, 7})) :
    (1 : K) / 24 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  have hlow : (e.card : K) / 2 ≤ (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum :=
    card_div_two_le_sum_one_sub_one_div he
  have hhigh : (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum ≤ e.card := e.sum_one_sub_one_div_le_card
  rcases (by omega : χ ≤ -1 ∨ χ = 0 ∨ χ = 1 ∨ χ = 2) with hneg | rfl | rfl | rfl
  · have hχ' : (χ : K) ≤ -1 := by exact_mod_cast hneg
    linarith [e.sum_one_sub_one_div_nonneg (K := K)]
  · have hne0 : e ≠ 0 := by
      rintro rfl
      simp at hpos
    have h1 : (1 : K) ≤ e.card := by exact_mod_cast Multiset.card_pos.mpr hne0
    simp only [Int.cast_zero, neg_zero, zero_add]
    linarith
  · simp only [Int.cast_one] at hpos ⊢
    by_cases h23 : e = {2, 3}
    · subst h23
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_ofNat]
      norm_num
    · linarith [one_div_four_le_neg_one_add_sum_of_two_le_of_ne he hpos h23]
  · have hne7 : e ≠ {2, 3, 7} := fun h ↦ hne ⟨rfl, h⟩
    simp only [Int.cast_ofNat] at hpos ⊢
    have hcard3 : 3 ≤ e.card := by
      have h2 : (2 : K) < e.card := by linarith
      have : (2 : ℕ) < e.card := by exact_mod_cast h2
      omega
    rcases eq_or_lt_of_le hcard3 with hc3 | hc4
    · obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp hc3.symm
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton] at hpos ⊢
      have hhyper : (1 : K) / a + 1 / b + 1 / c < 1 := by linarith
      linarith [one_div_twenty_four_le_hyperbolic_triangle_deficit_of_ne hhyper hne7]
    · linarith [one_div_six_le_neg_two_add_sum_of_four_le_card (K := K) he hc4 (by linarith)]

/-! ### Cusped orbifold deficits (`1 ≤ c`): `1 / 6` bound, `1 / 4` gap, and `(0; 2, 3; 1)` case -/

private theorem one_div_four_le_neg_intCast_add_sum_add_natCast_of_two_le_of_ne
    {χ : ℤ} {c : ℕ} {e : Multiset ℕ}
    (hχ : χ ≤ 2) (hc : 1 ≤ c) (he : ∀ n ∈ e, 2 ≤ n)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c)
    (hne : ¬ (χ = 2 ∧ c = 1 ∧ e = {2, 3})) :
    (1 : K) / 4 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  rcases (by omega : -(χ : ℤ) + (c : ℤ) ≥ 1 ∨ -(χ : ℤ) + (c : ℤ) = 0 ∨
      (χ = 2 ∧ c = 1)) with hge1 | heq0 | ⟨rfl, rfl⟩
  · have hge1K : (1 : K) ≤ -(χ : K) + c := by exact_mod_cast hge1
    linarith [e.sum_one_sub_one_div_nonneg (K := K)]
  · have heq0K : -(χ : K) + c = 0 := by exact_mod_cast heq0
    have hne0 : e ≠ 0 := by
      rintro rfl
      simp only [Multiset.map_zero, Multiset.sum_zero] at hpos
      linarith
    have hlow : (e.card : K) / 2 ≤ (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum :=
      card_div_two_le_sum_one_sub_one_div he
    have h1 : (1 : K) ≤ e.card := by exact_mod_cast Multiset.card_pos.mpr hne0
    linarith
  · have hne23 : e ≠ {2, 3} := fun h ↦ hne ⟨rfl, rfl, h⟩
    simp only [Int.cast_ofNat, Nat.cast_one] at hpos ⊢
    have hpos1 : 0 < -1 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by linarith
    linarith [one_div_four_le_neg_one_add_sum_of_two_le_of_ne he hpos1 hne23]

/-- For `χ ≤ 2`, `1 ≤ c`, and `1 ∉ e`, every positive orbifold deficit
`-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) + c` other than `(χ, c, e) = (2, 1, {2, 3})` is at least `1 / 4`,
attained at `(2, 1, {2, 4})` (genus `0`, one cusp, and elliptic orders `2, 4`). -/
theorem one_div_four_le_neg_intCast_add_sum_add_natCast_of_ne {χ : ℤ} {c : ℕ} {e : Multiset ℕ}
    (hχ : χ ≤ 2) (hc : 1 ≤ c) (he : 1 ∉ e)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c)
    (hne : ¬ (χ = 2 ∧ c = 1 ∧ e = {2, 3})) :
    (1 : K) / 4 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  have hsplit : -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c =
      -(χ : K) + ((e.filter (2 ≤ ·)).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum +
        ((c + e.count 0 : ℕ) : K) := by
    rw [e.sum_one_sub_one_div_eq_sum_filter_add_count_zero, Nat.cast_add]
    ring
  rw [hsplit] at hpos ⊢
  refine one_div_four_le_neg_intCast_add_sum_add_natCast_of_two_le_of_ne hχ (by omega)
    (fun _ hn ↦ (Multiset.mem_filter.mp hn).2) hpos ?_
  rintro ⟨rfl, hc1, hf23⟩
  have hz : e.count 0 = 0 := by omega
  rw [filter_two_le_eq_self_of_notMem_one he hz] at hf23
  exact hne ⟨rfl, by omega, hf23⟩

/-- For `χ ≤ 2`, `1 ≤ c`, and any multiset `e : Multiset ℕ`, a positive orbifold deficit
`-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) + c` is at least `1 / 6`. -/
theorem one_div_six_le_neg_intCast_add_sum_add_natCast {χ : ℤ} {c : ℕ} {e : Multiset ℕ}
    (hχ : χ ≤ 2) (hc : 1 ≤ c)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c) :
    (1 : K) / 6 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  have hsplit : -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c =
      -(χ : K) + ((e.filter (2 ≤ ·)).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum +
        ((c + e.count 0 : ℕ) : K) := by
    rw [e.sum_one_sub_one_div_eq_sum_filter_add_count_zero, Nat.cast_add]
    ring
  rw [hsplit] at hpos ⊢
  by_cases h : χ = 2 ∧ c + e.count 0 = 1 ∧ e.filter (2 ≤ ·) = {2, 3}
  · rcases h with ⟨rfl, hc1, hf23⟩
    rw [hc1, hf23]
    simp only [Int.cast_ofNat, Nat.cast_one, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_ofNat]
    norm_num
  · exact (by norm_num : (1 : K) / 6 ≤ 1 / 4).trans
      (one_div_four_le_neg_intCast_add_sum_add_natCast_of_two_le_of_ne hχ (by omega)
        (fun _ hn ↦ (Multiset.mem_filter.mp hn).2) hpos h)

/-- For `χ ≤ 2`, `1 ≤ c`, and `1 ∉ e`, `-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) + c = 1 / 6` holds if and
only if `χ = 2`, `c = 1`, and `e = {2, 3}`. -/
theorem neg_intCast_add_sum_add_natCast_eq_one_div_six_iff {χ : ℤ} {c : ℕ} {e : Multiset ℕ}
    (hχ : χ ≤ 2) (hc : 1 ≤ c) (he : 1 ∉ e) :
    -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c = 1 / 6 ↔
      χ = 2 ∧ c = 1 ∧ e = {2, 3} := by
  refine ⟨fun heq ↦ ?_, ?_⟩
  · by_contra hne
    have hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by linarith
    linarith [one_div_four_le_neg_intCast_add_sum_add_natCast_of_ne hχ hc he hpos hne]
  · rintro ⟨rfl, rfl, rfl⟩
    simp only [Int.cast_ofNat, Nat.cast_one, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_ofNat]
    norm_num

/-- **Second-smallest cusped orbifold deficit**: for `1 ≤ c` and `1 ∉ e`, every positive deficit
`2g - 2 + ∑_{n ∈ e} (1 - 1 / n) + c` other than `(g, c, e) = (0, 1, {2, 3})` is at least `1 / 4`,
attained at `(0, 1, {2, 4})`. -/
theorem one_div_four_le_orbifold_deficit_of_ne {g c : ℕ} {e : Multiset ℕ}
    (hc : 1 ≤ c) (he : 1 ∉ e)
    (hpos : 0 < 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c)
    (hne : ¬ (g = 0 ∧ c = 1 ∧ e = {2, 3})) :
    (1 : K) / 4 ≤ 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  have hχ : (2 - 2 * (g : ℤ)) ≤ 2 := by omega
  have hne' : ¬ ((2 - 2 * (g : ℤ)) = 2 ∧ c = 1 ∧ e = {2, 3}) := by
    rintro ⟨hg0, hc1, he23⟩
    exact hne ⟨by omega, hc1, he23⟩
  have hcast : -((2 - 2 * (g : ℤ) : ℤ) : K) = 2 * (g : K) - 2 := by push_cast; ring
  rw [← hcast] at hpos ⊢
  exact one_div_four_le_neg_intCast_add_sum_add_natCast_of_ne hχ hc he hpos hne'

/-- **Sharp lower bound for cusped orbifold deficits**: for `1 ≤ c` and any multiset `e`, a
positive deficit `2g - 2 + ∑_{n ∈ e} (1 - 1 / n) + c` is at least `1 / 6`. -/
theorem one_div_six_le_orbifold_deficit {g c : ℕ} {e : Multiset ℕ}
    (hc : 1 ≤ c)
    (hpos : 0 < 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c) :
    (1 : K) / 6 ≤ 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  have hχ : (2 - 2 * (g : ℤ)) ≤ 2 := by omega
  have hcast : -((2 - 2 * (g : ℤ) : ℤ) : K) = 2 * (g : K) - 2 := by push_cast; ring
  rw [← hcast] at hpos ⊢
  exact one_div_six_le_neg_intCast_add_sum_add_natCast hχ hc hpos

/-- **Equality case for cusped orbifold deficits**: for `1 ≤ c` and `1 ∉ e`, the deficit
`2g - 2 + ∑_{n ∈ e} (1 - 1 / n) + c` equals `1 / 6` if and only if `g = 0`, `c = 1`, and
`e = {2, 3}`. -/
theorem orbifold_deficit_eq_one_div_six_iff {g c : ℕ} {e : Multiset ℕ}
    (hc : 1 ≤ c) (he : 1 ∉ e) :
    2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c = 1 / 6 ↔
      g = 0 ∧ c = 1 ∧ e = {2, 3} := by
  have hχ : (2 - 2 * (g : ℤ)) ≤ 2 := by omega
  have hcast : -((2 - 2 * (g : ℤ) : ℤ) : K) = 2 * (g : K) - 2 := by push_cast; ring
  rw [← hcast, neg_intCast_add_sum_add_natCast_eq_one_div_six_iff hχ hc he]
  exact and_congr_left' ⟨by omega, by omega⟩

/-! ### Specializations at `χ = 1, c = 0` (`-1 + ∑ (1 - 1 / n)`) -/

/-- If `1 ∉ e`, `-1 + ∑_{n ∈ e} (1 - 1 / n) > 0`, and `e ≠ {2, 3}`, then
`-1 + ∑_{n ∈ e} (1 - 1 / n) ≥ 1 / 4`. -/
theorem one_div_four_le_neg_one_add_sum_of_ne {e : Multiset ℕ}
    (he : 1 ∉ e)
    (hpos : 0 < -1 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum)
    (hne : e ≠ {2, 3}) :
    (1 : K) / 4 ≤ -1 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  have hcast : -1 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum =
      -((2 : ℤ) : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + ((1 : ℕ) : K) := by
    push_cast; ring
  rw [hcast] at hpos ⊢
  exact one_div_four_le_neg_intCast_add_sum_add_natCast_of_ne le_rfl le_rfl he hpos
    fun ⟨_, _, h23⟩ ↦ hne h23

/-- For any multiset `e : Multiset ℕ` with `-1 + ∑_{n ∈ e} (1 - 1 / n) > 0`,
`-1 + ∑_{n ∈ e} (1 - 1 / n) ≥ 1 / 6`. -/
theorem one_div_six_le_neg_one_add_sum {e : Multiset ℕ}
    (hpos : 0 < -1 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum) :
    (1 : K) / 6 ≤ -1 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  have hcast : -1 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum =
      -((2 : ℤ) : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + ((1 : ℕ) : K) := by
    push_cast; ring
  rw [hcast] at hpos ⊢
  exact one_div_six_le_neg_intCast_add_sum_add_natCast le_rfl le_rfl hpos

/-- For `1 ∉ e`, `-1 + ∑_{n ∈ e} (1 - 1 / n) = 1 / 6` holds if and only if `e = {2, 3}`. -/
theorem neg_one_add_sum_eq_one_div_six_iff {e : Multiset ℕ} (he : 1 ∉ e) :
    -1 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum = 1 / 6 ↔ e = {2, 3} := by
  have hcast : -1 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum =
      -((2 : ℤ) : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + ((1 : ℕ) : K) := by
    push_cast; ring
  rw [hcast, neg_intCast_add_sum_add_natCast_eq_one_div_six_iff le_rfl le_rfl he]
  simp

/-! ### General orbifold deficits (`c : ℕ`): cusp replacement and Siegel's `1 / 42` bound -/

/-- For `χ ≤ 2`, arbitrary `c : ℕ`, and `1 ∉ e`, every positive orbifold deficit
`-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) + c` other than `(χ, c, e) = (2, 0, {2, 3, 7})` is at least
`1 / 24`, attained at `(2, 0, {2, 3, 8})`. -/
theorem one_div_twenty_four_le_neg_intCast_add_sum_add_natCast_of_ne
    {χ : ℤ} {c : ℕ} {e : Multiset ℕ}
    (hχ : χ ≤ 2) (he : 1 ∉ e)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c)
    (hne : ¬ (χ = 2 ∧ c = 0 ∧ e = {2, 3, 7})) :
    (1 : K) / 24 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  have hsplit : -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c =
      -(χ : K) + ((e.filter (2 ≤ ·)).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum +
        ((c + e.count 0 : ℕ) : K) := by
    rw [e.sum_one_sub_one_div_eq_sum_filter_add_count_zero, Nat.cast_add]
    ring
  rw [hsplit] at hpos ⊢
  rcases (c + e.count 0).eq_zero_or_pos with hcz | hcpos
  · rw [hcz, Nat.cast_zero, add_zero] at hpos ⊢
    have hc0 : c = 0 := by omega
    have hz : e.count 0 = 0 := by omega
    refine one_div_twenty_four_le_neg_intCast_add_sum_of_two_le_of_ne hχ
      (fun _ hn ↦ (Multiset.mem_filter.mp hn).2) hpos fun ⟨hχ2, hf7⟩ ↦ ?_
    rw [filter_two_le_eq_self_of_notMem_one he hz] at hf7
    exact hne ⟨hχ2, hc0, hf7⟩
  · exact (by norm_num : (1 : K) / 24 ≤ 1 / 6).trans
      (one_div_six_le_neg_intCast_add_sum_add_natCast hχ hcpos hpos)

/-- For any integer `χ ≤ 2` and multiset `e : Multiset ℕ`, a positive deficit
`-(χ : K) + ∑_{n ∈ e} (1 - 1 / n)` is at least `1 / 42`. -/
theorem one_div_forty_two_le_neg_intCast_add_sum {χ : ℤ} {e : Multiset ℕ}
    (hχ : χ ≤ 2)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum) :
    (1 : K) / 42 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  have hsplit : -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum =
      -((χ - e.count 0 : ℤ) : K) +
        ((e.filter (2 ≤ ·)).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
    rw [e.sum_one_sub_one_div_eq_sum_filter_add_count_zero]
    push_cast
    ring
  rw [hsplit] at hpos ⊢
  by_cases h : (χ - e.count 0 : ℤ) = 2 ∧ e.filter (2 ≤ ·) = {2, 3, 7}
  · rcases h with ⟨hχ2, hf7⟩
    rw [hχ2, hf7]
    simp only [Int.cast_ofNat, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_ofNat]
    norm_num
  · exact (by norm_num : (1 : K) / 42 ≤ 1 / 24).trans
      (one_div_twenty_four_le_neg_intCast_add_sum_of_two_le_of_ne (by omega)
        (fun _ hn ↦ (Multiset.mem_filter.mp hn).2) hpos h)

/-- **Cusp replacement for positive orbifold deficits.** When `χ ≤ 2` and the orbifold deficit
`δ = -(χ : K) + ∑_{n ∈ e} (1 - 1 / n) + c` is positive, there exists an integer `m ≥ 2` such that
replacing the `c` cusps by `c` elliptic points of order `m` yields a cuspless datum
`e + Multiset.replicate c m` whose deficit `δ - c / m` is still positive and therefore at least
`1 / 42`. No Archimedean assumption on `K` is needed because `δ` is a rational cast. -/
theorem exists_two_le_and_one_div_forty_two_le_neg_intCast_add_sum_map_add_replicate
    {χ : ℤ} {c : ℕ} {e : Multiset ℕ} (hχ : χ ≤ 2)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c) :
    ∃ m : ℕ, 2 ≤ m ∧
      (1 : K) / 42 ≤
        -(χ : K) + ((e + Multiset.replicate c m).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  set δQ : ℚ := -(χ : ℚ) + (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum + c
  have hδpos : 0 < δQ := by
    rw [← Rat.cast_pos (K := K), ratCast_neg_intCast_add_sum_add_natCast]
    exact hpos
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt ((c : ℚ) / δQ)
  refine ⟨max 2 m₀, le_max_left 2 m₀, ?_⟩
  set m := max 2 m₀
  have hmQ : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlt : (c : ℚ) / m < δQ := by
    rw [div_lt_iff₀ hmQ]
    have := (div_lt_iff₀ hδpos).mp (hm₀.trans_le (Nat.cast_le.mpr (le_max_right 2 m₀)))
    linarith
  have hpos' : 0 <
      -(χ : K) + ((e + Multiset.replicate c m).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
    have hcast : ((δQ - (c : ℚ) / m : ℚ) : K) =
        -(χ : K) + ((e + Multiset.replicate c m).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
      rw [Multiset.sum_map_add_replicate_one_sub_one_div, Rat.cast_sub,
        ratCast_neg_intCast_add_sum_add_natCast, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]
      ring
    rw [← hcast]
    exact Rat.cast_pos.mpr (sub_pos.mpr hlt)
  exact one_div_forty_two_le_neg_intCast_add_sum hχ hpos'

/-- **Siegel's numerical `1 / 42` bound with cusps (Euler-characteristic form).** For `χ ≤ 2`,
arbitrary `c : ℕ`, and any multiset `e : Multiset ℕ`, a positive orbifold deficit
`-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) + c` is at least `1 / 42`. -/
theorem one_div_forty_two_le_neg_intCast_add_sum_add_natCast
    {χ : ℤ} {c : ℕ} {e : Multiset ℕ}
    (hχ : χ ≤ 2)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c) :
    (1 : K) / 42 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  obtain ⟨m, _, hm⟩ :=
    exists_two_le_and_one_div_forty_two_le_neg_intCast_add_sum_map_add_replicate hχ hpos
  rw [Multiset.sum_map_add_replicate_one_sub_one_div] at hm
  have hdiv : (0 : K) ≤ (c : K) / m := by positivity
  linarith [hm, hdiv]

/-- For `χ ≤ 2`, arbitrary `c : ℕ`, and `1 ∉ e`,
`-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) + c = 1 / 42` holds if and only if `χ = 2`, `c = 0`, and
`e = {2, 3, 7}`. -/
theorem neg_intCast_add_sum_add_natCast_eq_one_div_forty_two_iff
    {χ : ℤ} {c : ℕ} {e : Multiset ℕ}
    (hχ : χ ≤ 2) (he : 1 ∉ e) :
    -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c = 1 / 42 ↔
      χ = 2 ∧ c = 0 ∧ e = {2, 3, 7} := by
  refine ⟨fun heq ↦ ?_, ?_⟩
  · by_contra hne
    have hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by linarith
    linarith [one_div_twenty_four_le_neg_intCast_add_sum_add_natCast_of_ne hχ he hpos hne]
  · rintro ⟨rfl, rfl, rfl⟩
    simp only [Int.cast_ofNat, Nat.cast_zero, add_zero, Multiset.insert_eq_cons,
      Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton,
      Nat.cast_ofNat]
    norm_num

/-- **Second-smallest orbifold deficit**: for any `g c : ℕ` and `1 ∉ e`, every positive deficit
`2g - 2 + ∑_{n ∈ e} (1 - 1 / n) + c` other than `(g, c, e) = (0, 0, {2, 3, 7})` is at least
`1 / 24`, attained at `(0, 0, {2, 3, 8})`. -/
theorem one_div_twenty_four_le_orbifold_deficit_of_ne {g c : ℕ} {e : Multiset ℕ}
    (he : 1 ∉ e)
    (hpos : 0 < 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c)
    (hne : ¬ (g = 0 ∧ c = 0 ∧ e = {2, 3, 7})) :
    (1 : K) / 24 ≤ 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  have hχ : (2 - 2 * (g : ℤ)) ≤ 2 := by omega
  have hne' : ¬ ((2 - 2 * (g : ℤ)) = 2 ∧ c = 0 ∧ e = {2, 3, 7}) := by
    rintro ⟨hg0, hc0, he7⟩
    exact hne ⟨by omega, hc0, he7⟩
  have hcast : -((2 - 2 * (g : ℤ) : ℤ) : K) = 2 * (g : K) - 2 := by push_cast; ring
  rw [← hcast] at hpos ⊢
  exact one_div_twenty_four_le_neg_intCast_add_sum_add_natCast_of_ne hχ he hpos hne'

/-- **Siegel's numerical `1 / 42` bound for orbifold deficits**: for any genus `g`, cusp count `c`,
and multiset `e`, a positive deficit `2g - 2 + ∑_{n ∈ e} (1 - 1 / n) + c` is at least `1 / 42`. -/
theorem one_div_forty_two_le_orbifold_deficit {g c : ℕ} {e : Multiset ℕ}
    (hpos : 0 < 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c) :
    (1 : K) / 42 ≤ 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  have hχ : (2 - 2 * (g : ℤ)) ≤ 2 := by omega
  have hcast : -((2 - 2 * (g : ℤ) : ℤ) : K) = 2 * (g : K) - 2 := by push_cast; ring
  rw [← hcast] at hpos ⊢
  exact one_div_forty_two_le_neg_intCast_add_sum_add_natCast hχ hpos

/-- **Equality case of Siegel's `1 / 42` bound**: for any genus `g`, cusp count `c`, and `1 ∉ e`,
`2g - 2 + ∑_{n ∈ e} (1 - 1 / n) + c = 1 / 42` holds if and only if `g = 0`, `c = 0`, and
`e = {2, 3, 7}`. -/
theorem orbifold_deficit_eq_one_div_forty_two_iff {g c : ℕ} {e : Multiset ℕ}
    (he : 1 ∉ e) :
    2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c = 1 / 42 ↔
      g = 0 ∧ c = 0 ∧ e = {2, 3, 7} := by
  have hχ : (2 - 2 * (g : ℤ)) ≤ 2 := by omega
  have hcast : -((2 - 2 * (g : ℤ) : ℤ) : K) = 2 * (g : K) - 2 := by push_cast; ring
  rw [← hcast, neg_intCast_add_sum_add_natCast_eq_one_div_forty_two_iff hχ he]
  exact and_congr_left' ⟨by omega, by omega⟩

/-! ### Cuspless specializations (`c = 0`) and Hurwitz's `84(g - 1)` bound -/

/-- For `χ ≤ 2` and `1 ∉ e`, every positive deficit `-(χ : K) + ∑_{n ∈ e} (1 - 1 / n)` other than
`(χ, e) = (2, {2, 3, 7})` is at least `1 / 24`. (The companion `1 / 42` bound is
`TauCeti.one_div_forty_two_le_neg_intCast_add_sum` above.) -/
theorem one_div_twenty_four_le_neg_intCast_add_sum_of_ne {χ : ℤ} {e : Multiset ℕ}
    (hχ : χ ≤ 2) (he : 1 ∉ e)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum)
    (hne : ¬ (χ = 2 ∧ e = {2, 3, 7})) :
    (1 : K) / 24 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  simpa only [Nat.cast_zero, add_zero] using
    one_div_twenty_four_le_neg_intCast_add_sum_add_natCast_of_ne (c := 0) hχ he
      (by simpa only [Nat.cast_zero, add_zero] using hpos) fun ⟨hχ2, _, he7⟩ ↦ hne ⟨hχ2, he7⟩

/-- For `χ ≤ 2` and `1 ∉ e`, `-(χ : K) + ∑_{n ∈ e} (1 - 1 / n)` equals `1 / 42` if and only if
`χ = 2` and `e = {2, 3, 7}`. -/
theorem neg_intCast_add_sum_eq_one_div_forty_two_iff {χ : ℤ} {e : Multiset ℕ}
    (hχ : χ ≤ 2) (he : 1 ∉ e) :
    -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum = 1 / 42 ↔ χ = 2 ∧ e = {2, 3, 7} := by
  simpa only [Nat.cast_zero, add_zero, true_and] using
    neg_intCast_add_sum_add_natCast_eq_one_div_forty_two_iff (K := K) (c := 0) hχ he

/-- Every positive cuspless deficit `2γ - 2 + ∑_{n ∈ e} (1 - 1 / n)` with `1 ∉ e` other than
`(γ, e) = (0, {2, 3, 7})` is at least `1 / 24`, attained at `(0, {2, 3, 8})`. -/
theorem one_div_twenty_four_le_hyperbolic_deficit_of_ne {γ : ℕ} {e : Multiset ℕ}
    (he : 1 ∉ e)
    (hpos : 0 < 2 * (γ : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum)
    (hne : ¬ (γ = 0 ∧ e = {2, 3, 7})) :
    (1 : K) / 24 ≤ 2 * (γ : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  simpa only [Nat.cast_zero, add_zero] using
    one_div_twenty_four_le_orbifold_deficit_of_ne (g := γ) (c := 0) he
      (by simpa only [Nat.cast_zero, add_zero] using hpos) fun ⟨hγ0, _, he7⟩ ↦ hne ⟨hγ0, he7⟩

/-- **The sharp numerical bound for hyperbolic branch data**: for any genus `γ : ℕ` and multiset
`e : Multiset ℕ`, a positive cuspless deficit `2γ - 2 + ∑_{n ∈ e} (1 - 1 / n)` is at least
`1 / 42`. -/
theorem one_div_forty_two_le_hyperbolic_deficit {γ : ℕ} {e : Multiset ℕ}
    (hpos : 0 < 2 * (γ : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum) :
    (1 : K) / 42 ≤ 2 * (γ : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  simpa only [Nat.cast_zero, add_zero] using
    one_div_forty_two_le_orbifold_deficit (g := γ) (c := 0)
      (by simpa only [Nat.cast_zero, add_zero] using hpos)

/-- **Uniqueness of the `(0; 2, 3, 7)` cuspless datum**: for `γ : ℕ` and `1 ∉ e`, the deficit
`2γ - 2 + ∑_{n ∈ e} (1 - 1 / n)` equals `1 / 42` if and only if `γ = 0` and `e = {2, 3, 7}`. -/
theorem hyperbolic_deficit_eq_one_div_forty_two_iff {γ : ℕ} {e : Multiset ℕ}
    (he : 1 ∉ e) :
    2 * (γ : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum = 1 / 42 ↔
      γ = 0 ∧ e = {2, 3, 7} := by
  simpa only [Nat.cast_zero, add_zero, true_and] using
    orbifold_deficit_eq_one_div_forty_two_iff (K := K) (g := γ) (c := 0) he

/-- **The numerical half of the Hurwitz bound**: if `n * (2γ - 2 + ∑ᵢ (1 - 1 / eᵢ)) = 2g - 2` in a
linearly ordered field `K` with `n > 0` and `g ≥ 2`, then `n ≤ 84 (g - 1)`. -/
theorem card_le_eighty_four_mul_sub_one {n g γ : ℕ} {e : Multiset ℕ} (hg : 2 ≤ g) (hn : 0 < n)
    (hkey : (n : K) * (2 * (γ : K) - 2 + (e.map fun m : ℕ ↦ 1 - 1 / (m : K)).sum) =
      2 * (g : K) - 2) :
    n ≤ 84 * (g - 1) := by
  have hnK : (0 : K) < n := by exact_mod_cast hn
  have hgK : (2 : K) ≤ g := by exact_mod_cast hg
  have hDpos : 0 < 2 * (γ : K) - 2 + (e.map fun m : ℕ ↦ 1 - 1 / (m : K)).sum := by
    by_contra hcon
    have hle := mul_nonpos_of_nonneg_of_nonpos hnK.le (not_lt.mp hcon)
    rw [hkey] at hle
    linarith
  have hmul := mul_le_mul_of_nonneg_left (one_div_forty_two_le_hyperbolic_deficit hDpos) hnK.le
  rw [hkey] at hmul
  have hnat : (n : K) ≤ ((84 * (g - 1) : ℕ) : K) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ g)]
    linarith
  exact_mod_cast hnat

/-! ### `finsum` forms for elliptic orbit sets -/

/-- **Siegel's `1 / 42` bound in `finsum` form (Euler-characteristic version).** For any `χ ≤ 2`,
cusp count `c : ℕ`, set `s : Set α`, and map `f : α → ℕ`, if
`0 < -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c`, then that deficit is at least `1 / 42`. Neither
finiteness of `s` nor a lower bound on `f` is needed. -/
theorem one_div_forty_two_le_neg_intCast_add_finsum_add_natCast {α : Type*} {s : Set α}
    {f : α → ℕ} {χ : ℤ} {c : ℕ} (hχ : χ ≤ 2)
    (hpos : 0 < -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c) :
    (1 : K) / 42 ≤ -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c := by
  obtain ⟨e, he⟩ := s.exists_finsum_mem_comp_eq_multiset_sum_map f fun n : ℕ ↦ 1 - 1 / (n : K)
  simp_rw [← one_div, he] at hpos ⊢
  exact one_div_forty_two_le_neg_intCast_add_sum_add_natCast hχ hpos

/-- **Siegel's `1 / 42` bound in `finsum` form (genus version).** For any `g c : ℕ`, set `s : Set α`
and `f : α → ℕ`, if `0 < 2g - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c`, then
`1 / 42 ≤ 2g - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c`. -/
theorem one_div_forty_two_le_orbifold_deficit_finsum {α : Type*} {s : Set α}
    {f : α → ℕ} {g c : ℕ}
    (hpos : 0 < 2 * (g : K) - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c) :
    (1 : K) / 42 ≤ 2 * (g : K) - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c := by
  have hχ : (2 - 2 * (g : ℤ)) ≤ 2 := by omega
  have hcast : -((2 - 2 * (g : ℤ) : ℤ) : K) = 2 * (g : K) - 2 := by push_cast; ring
  rw [← hcast] at hpos ⊢
  exact one_div_forty_two_le_neg_intCast_add_finsum_add_natCast hχ hpos

/-- **Equality case of Siegel's `1 / 42` bound in `finsum` form (Euler-characteristic version).**
For a finite set `s : Set α`, `f : α → ℕ` with `∀ x ∈ s, f x ≠ 1`, and `χ ≤ 2`,
`-(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 42` holds if and only if `χ = 2`, `c = 0`, and
each fibre `{x // x ∈ s ∧ f x = m}` has cardinality `Multiset.count m {2, 3, 7}`. Finiteness of `s`
is necessary for the converse because `Nat.card` vanishes on infinite fibres. -/
theorem neg_intCast_add_finsum_add_natCast_eq_one_div_forty_two_iff {α : Type*} {s : Set α}
    (hs : s.Finite) {f : α → ℕ} {χ : ℤ} {c : ℕ} (hχ : χ ≤ 2) (hf : ∀ x ∈ s, f x ≠ 1) :
    -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 42 ↔
      χ = 2 ∧ c = 0 ∧ ∀ m : ℕ, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3, 7} := by
  have hsum : ∑ᶠ x ∈ s, (1 - (f x : K)⁻¹) =
      ((hs.toFinset.val.map f).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
    simpa only [one_div] using
      hs.finsum_mem_comp_eq_multiset_sum_map f fun n : ℕ ↦ 1 - (n : K)⁻¹
  have he : 1 ∉ hs.toFinset.val.map f := by
    intro h1
    obtain ⟨x, hx, hfx⟩ := Multiset.mem_map.mp h1
    exact hf x (hs.mem_toFinset.mp hx) hfx
  rw [hsum, neg_intCast_add_sum_add_natCast_eq_one_div_forty_two_iff hχ he,
    hs.map_toFinset_val_eq_iff]

/-- **Equality case of Siegel's `1 / 42` bound in `finsum` form (genus version).** For a finite set
`s : Set α` and `f : α → ℕ` with `∀ x ∈ s, f x ≠ 1`,
`2g - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 42` holds if and only if `g = 0`, `c = 0`, and
`∀ m, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3, 7}`. -/
theorem orbifold_deficit_finsum_eq_one_div_forty_two_iff {α : Type*} {s : Set α}
    (hs : s.Finite) {f : α → ℕ} {g c : ℕ} (hf : ∀ x ∈ s, f x ≠ 1) :
    2 * (g : K) - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 42 ↔
      g = 0 ∧ c = 0 ∧ ∀ m : ℕ, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3, 7} := by
  have hχ : (2 - 2 * (g : ℤ)) ≤ 2 := by omega
  have hcast : -((2 - 2 * (g : ℤ) : ℤ) : K) = 2 * (g : K) - 2 := by push_cast; ring
  rw [← hcast, neg_intCast_add_finsum_add_natCast_eq_one_div_forty_two_iff hs hχ hf]
  exact and_congr_left' ⟨by omega, by omega⟩

/-- **Cusped `1 / 6` bound in `finsum` form (Euler-characteristic version).** For `χ ≤ 2`, `1 ≤ c`,
any set `s : Set α`, and any `f : α → ℕ`, a positive deficit
`-(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c` is at least `1 / 6`. -/
theorem one_div_six_le_neg_intCast_add_finsum_add_natCast {α : Type*} {s : Set α}
    {f : α → ℕ} {χ : ℤ} {c : ℕ} (hχ : χ ≤ 2) (hc : 1 ≤ c)
    (hpos : 0 < -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c) :
    (1 : K) / 6 ≤ -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c := by
  obtain ⟨e, he⟩ := s.exists_finsum_mem_comp_eq_multiset_sum_map f fun n : ℕ ↦ 1 - 1 / (n : K)
  simp_rw [← one_div, he] at hpos ⊢
  exact one_div_six_le_neg_intCast_add_sum_add_natCast hχ hc hpos

/-- **Cusped `1 / 6` bound in `finsum` form (genus version).** For `1 ≤ c`, any set `s : Set α`,
and any `f : α → ℕ`, if `0 < 2g - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c`, then
`1 / 6 ≤ 2g - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c`. -/
theorem one_div_six_le_orbifold_deficit_finsum {α : Type*} {s : Set α}
    {f : α → ℕ} {g c : ℕ} (hc : 1 ≤ c)
    (hpos : 0 < 2 * (g : K) - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c) :
    (1 : K) / 6 ≤ 2 * (g : K) - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c := by
  have hχ : (2 - 2 * (g : ℤ)) ≤ 2 := by omega
  have hcast : -((2 - 2 * (g : ℤ) : ℤ) : K) = 2 * (g : K) - 2 := by push_cast; ring
  rw [← hcast] at hpos ⊢
  exact one_div_six_le_neg_intCast_add_finsum_add_natCast hχ hc hpos

/-- **Equality case of the cusped `1 / 6` bound in `finsum` form (Euler-characteristic version).**
For a finite set `s : Set α`, `f : α → ℕ` with `∀ x ∈ s, f x ≠ 1`, `χ ≤ 2`, and `1 ≤ c`,
`-(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 6` holds if and only if `χ = 2`, `c = 1`, and
`∀ m, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3}`. -/
theorem neg_intCast_add_finsum_add_natCast_eq_one_div_six_iff {α : Type*} {s : Set α}
    (hs : s.Finite) {f : α → ℕ} {χ : ℤ} {c : ℕ} (hχ : χ ≤ 2) (hc : 1 ≤ c)
    (hf : ∀ x ∈ s, f x ≠ 1) :
    -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 6 ↔
      χ = 2 ∧ c = 1 ∧ ∀ m : ℕ, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3} := by
  have hsum : ∑ᶠ x ∈ s, (1 - (f x : K)⁻¹) =
      ((hs.toFinset.val.map f).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
    simpa only [one_div] using
      hs.finsum_mem_comp_eq_multiset_sum_map f fun n : ℕ ↦ 1 - (n : K)⁻¹
  have he : 1 ∉ hs.toFinset.val.map f := by
    intro h1
    obtain ⟨x, hx, hfx⟩ := Multiset.mem_map.mp h1
    exact hf x (hs.mem_toFinset.mp hx) hfx
  rw [hsum, neg_intCast_add_sum_add_natCast_eq_one_div_six_iff hχ hc he,
    hs.map_toFinset_val_eq_iff]

/-- **Equality case of the cusped `1 / 6` bound in `finsum` form (genus version).** For a finite
set `s : Set α`, `f : α → ℕ` with `∀ x ∈ s, f x ≠ 1`, and `1 ≤ c`,
`2g - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 6` holds if and only if `g = 0`, `c = 1`, and
`∀ m, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3}`. -/
theorem orbifold_deficit_finsum_eq_one_div_six_iff {α : Type*} {s : Set α}
    (hs : s.Finite) {f : α → ℕ} {g c : ℕ} (hc : 1 ≤ c) (hf : ∀ x ∈ s, f x ≠ 1) :
    2 * (g : K) - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 6 ↔
      g = 0 ∧ c = 1 ∧ ∀ m : ℕ, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3} := by
  have hχ : (2 - 2 * (g : ℤ)) ≤ 2 := by omega
  have hcast : -((2 - 2 * (g : ℤ) : ℤ) : K) = 2 * (g : K) - 2 := by push_cast; ring
  rw [← hcast, neg_intCast_add_finsum_add_natCast_eq_one_div_six_iff hs hχ hc hf]
  exact and_congr_left' ⟨by omega, by omega⟩

end OrderedField

/-! ### Boundary and witness signature checks -/

section WitnessSignatures

variable {K : Type*} [DivisionRing K] [CharZero K]

/-- The genus-zero branch data `(2, 3, 7)` attains the cuspless bound `1 / 42`, showing that the
constant in `TauCeti.one_div_forty_two_le_hyperbolic_deficit` is sharp. -/
theorem hyperbolic_deficit_two_three_seven :
    2 * ((0 : ℕ) : K) - 2 +
        (({2, 3, 7} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum = 1 / 42 := by
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_zero, Nat.cast_ofNat]
  norm_num

/-- The cuspless signature `(0; 2, 3, 8; 0)` attains the second-smallest orbifold deficit
`1 / 24`. -/
theorem orbifold_deficit_zero_two_three_eight_zero :
    2 * ((0 : ℕ) : K) - 2 +
        (({2, 3, 8} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + (0 : ℕ) = 1 / 24 := by
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_zero, Nat.cast_ofNat]
  norm_num

/-- The cuspless four-point signature `(0; 2, 2, 2, 3; 0)` also has deficit `1 / 6`, showing that
`1 ≤ c` is essential in `TauCeti.orbifold_deficit_eq_one_div_six_iff`. -/
theorem orbifold_deficit_zero_two_two_two_three_zero :
    2 * ((0 : ℕ) : K) - 2 +
        (({2, 2, 2, 3} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + (0 : ℕ) = 1 / 6 := by
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_zero, Nat.cast_ofNat]
  norm_num

/-- The Euclidean pillowcase signature `(0; 2, 2, 2, 2; 0)` has deficit `0`, showing that
positivity of the deficit is essential in `TauCeti.one_div_forty_two_le_orbifold_deficit`. -/
theorem orbifold_deficit_zero_four_twos_zero :
    2 * ((0 : ℕ) : K) - 2 +
        (({2, 2, 2, 2} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + (0 : ℕ) = 0 := by
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_zero, Nat.cast_ofNat]
  norm_num

/-- The modular signature `(0; 2, 3; 1)` attains the cusped minimum `1 / 6`. -/
theorem orbifold_deficit_zero_two_three_one :
    2 * ((0 : ℕ) : K) - 2 +
        (({2, 3} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + (1 : ℕ) = 1 / 6 := by
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  norm_num

/-- The cusped Euclidean signature `(0; 2, 2; 1)` has deficit `0`, showing that positivity of the
deficit is essential in `TauCeti.one_div_six_le_orbifold_deficit`. -/
theorem orbifold_deficit_zero_two_two_one :
    2 * ((0 : ℕ) : K) - 2 +
        (({2, 2} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + (1 : ℕ) = 0 := by
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  norm_num

end WitnessSignatures

end TauCeti
