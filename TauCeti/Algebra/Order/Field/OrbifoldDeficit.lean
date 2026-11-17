/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Multiset.Filter
public import TauCeti.Algebra.BigOperators.Finprod
public import TauCeti.Algebra.Order.Field.HurwitzTriangle
public import TauCeti.Data.Set.Multiset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Sharp lower bounds and equality cases for hyperbolic orbifold signature deficits

An orbifold signature `(g; m₁, …, m_r; c)` consists of a genus `g : ℕ`, a multiset `e` of elliptic
orders, and a cusp count `c : ℕ`. Its **orbifold deficit** (the negative orbifold Euler
characteristic) in a division ring `K` is

`2g - 2 + ∑ᵢ (1 - 1 / mᵢ) + c`,

or more generally `-(χ : K) + ∑ᵢ (1 - 1 / mᵢ) + c` for an integer Euler characteristic `χ ≤ 2`
(with `χ = 2 - 2g` in the orientable surface case). Since
`-(χ : K) + ∑ᵢ (1 - 1 / mᵢ) + c = -((χ - c : ℤ) : K) + ∑ᵢ (1 - 1 / mᵢ)`, every cusped or general
orbifold deficit reduces directly to the cuspless Euler-characteristic deficit
`-(χ' : K) + ∑ᵢ (1 - 1 / mᵢ)` with `χ' = χ - c ≤ 1` (when `1 ≤ c`) or `χ' ≤ 2` (for arbitrary
`c : ℕ`). For a cofinite Fuchsian group `Γ` of signature `(g; m₁, …, m_r; c)`, the Gauss–Bonnet
area formula expresses the hyperbolic covolume of `Γ` as `2π` times this deficit, while positivity
of covolume forces the deficit to be strictly positive; for a finite tame group of automorphisms of
a function field of genus `g ≥ 2`, Riemann–Hurwitz identifies the cuspless (`c = 0`) deficit with
`(2g - 2) / |G|`, yielding Hurwitz's `84(g - 1)` bound (`TauCeti.card_le_eighty_four_mul_sub_one`).

This file proves the two sharp positive lower bounds on orbifold deficits and their gaps to the
second-smallest values in an arbitrary linearly ordered field `K`, together with their exact
equality characterizations and Hurwitz's `84(g - 1)` bound in any characteristic-zero division
ring `K`:

1. **Cusped / `χ ≤ 1` minimum `1/6`**: whenever `χ ≤ 1` (in particular, whenever `χ ≤ 2` and
   `1 ≤ c`) and the deficit is positive, it is at least `1/6`, attained uniquely (among multisets
   `e` with `1 ∉ e`) at `χ = 1, e = {2, 3}` (respectively `χ = 2`, `g = 0`, `c = 1`, `e = {2, 3}`,
   the signature of `PSL(2, ℤ)`). Every other positive deficit with `χ ≤ 1` and `1 ∉ e` is at least
   `1/4`, attained at `(0; 2, 4; 1)`. The hypothesis `1 ≤ c` is essential for uniqueness: without
   cusps, `(0; 2, 2, 2, 3; 0)` also has deficit `1/6`.
2. **Unconditional / `χ ≤ 2` minimum `1/42` (Siegel / Hurwitz)**: whenever `χ ≤ 2` and the deficit
   is positive, it is at least `1/42`, attained uniquely (among multisets `e` with `1 ∉ e`) at
   `χ = 2` (`g = 0`), `c = 0` and `e = {2, 3, 7}`. Every other positive deficit with `χ ≤ 2` and
   `1 ∉ e` is at least `1/24`, attained at `(0; 2, 3, 8; 0)`.

Because `1 - 1 / (1 : K) = 0` and `1 - 1 / (0 : K) = 1`
(`Multiset.sum_one_sub_one_div_eq_sum_filter_add_count_zero`), the lower bounds `1/42` and `1/6`
(and hence `TauCeti.card_le_eighty_four_mul_sub_one`) hold for all multisets `e : Multiset ℕ` and
all order maps `f : α → ℕ` without any lower-bound or finiteness assumptions. The multiset
uniqueness and second-smallest deficit theorems require only `1 ∉ e`. Combining the multiset bounds
and characterizations with `Set.exists_finsum_mem_comp_eq_multiset_sum_map`,
`Set.Finite.finsum_mem_comp_eq_multiset_sum_map`, and `Set.Finite.map_toFinset_val_eq_iff` yields
the unconditional `finsum` lower bounds and, under `hs : s.Finite` and `∀ x ∈ s, f x ≠ 1`, the
`finsum` equality characterizations over an orbit set `s : Set α` with stabilizer-order function
`f : α → ℕ`, characterizing the minimal signatures directly via the fibre cardinalities
`Nat.card {x // x ∈ s ∧ f x = m}`.

## Main results

* `Multiset.sum_one_sub_one_div_nonneg`, `Multiset.sum_one_sub_one_div_le_card`,
  `Multiset.sum_one_sub_one_div_eq_sum_filter_add_count_zero`,
  `TauCeti.half_le_one_sub_one_div`, `TauCeti.card_div_two_le_sum_one_sub_one_div`, and
  `TauCeti.sum_one_sub_one_div_eq_card_div_two`: bounds and identities for elliptic defect sums.
* `TauCeti.one_div_six_le_neg_intCast_add_sum_one_sub_one_div_of_le_one`,
  `TauCeti.one_div_four_le_neg_intCast_add_sum_one_sub_one_div_of_le_one_of_ne`,
  `TauCeti.neg_intCast_add_sum_one_sub_one_div_eq_one_div_six_iff_of_le_one`,
  `TauCeti.one_div_forty_two_le_neg_intCast_add_sum_one_sub_one_div`,
  `TauCeti.one_div_twenty_four_le_neg_intCast_add_sum_one_sub_one_div_of_ne`, and
  `TauCeti.neg_intCast_add_sum_one_sub_one_div_eq_one_div_forty_two_iff`: core cuspless
  Euler-characteristic bounds, second-smallest gaps, and equality characterizations for `χ ≤ 1` and
  `χ ≤ 2`.
* `TauCeti.one_div_forty_two_le_orbifold_deficit`,
  `TauCeti.one_div_twenty_four_le_orbifold_deficit_of_ne`, and
  `TauCeti.orbifold_deficit_eq_one_div_forty_two_iff`: Siegel's `1/42` lower bound, the `1/24` gap,
  and the `(0; 2, 3, 7; 0)` equality characterization, with the cuspless bound
  `TauCeti.one_div_forty_two_le_hyperbolic_deficit` and Hurwitz's `84(g - 1)` bound
  `TauCeti.card_le_eighty_four_mul_sub_one`.
* `TauCeti.one_div_six_le_orbifold_deficit`,
  `TauCeti.one_div_four_le_orbifold_deficit_of_ne`, and
  `TauCeti.orbifold_deficit_eq_one_div_six_iff`: the `1/6` lower bound, `1/4` gap, and
  `(0; 2, 3; 1)` equality characterization for cusped signatures (`1 ≤ c`).
* `TauCeti.one_div_forty_two_le_orbifold_deficit_finsum`,
  `TauCeti.orbifold_deficit_finsum_eq_one_div_forty_two_iff`,
  `TauCeti.one_div_six_le_orbifold_deficit_finsum`, and
  `TauCeti.orbifold_deficit_finsum_eq_one_div_six_iff`: `finsum` and fibre-count forms (with
  Euler-characteristic versions
  `TauCeti.one_div_forty_two_le_neg_intCast_add_finsum_mem_one_sub_inv_add_natCast`,
  `TauCeti.neg_intCast_add_finsum_mem_one_sub_inv_add_natCast_eq_one_div_forty_two_iff`,
  `TauCeti.one_div_six_le_neg_intCast_add_finsum_mem_one_sub_inv_add_natCast`, and
  `TauCeti.neg_intCast_add_finsum_mem_one_sub_inv_add_natCast_eq_one_div_six_iff`).

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

/-- Separating out `0` and `1` from `(e.map fun n ↦ 1 - 1 / n).sum`: each `1` contributes `0`, while
each `0` contributes `1 - 1 / 0 = 1`. -/
theorem sum_one_sub_one_div_eq_sum_filter_add_count_zero [DivisionRing K] (e : Multiset ℕ) :
    (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum =
      ((e.filter (2 ≤ ·)).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + e.count 0 := by
  conv_lhs => rw [← Multiset.filter_add_not (2 ≤ ·) e]
  rw [Multiset.map_add, Multiset.sum_add]
  congr 1
  rw [Multiset.sum_map_eq_nsmul_single 0]
  · simp [Multiset.count_filter_of_pos]
  · intro n hn hmem
    have : n = 1 := by
      have := (Multiset.mem_filter.mp hmem).2
      omega
    subst this
    simp

end Multiset

namespace TauCeti

private theorem neg_intCast_add_sum_one_sub_one_div_filter_two_le {K : Type*} [DivisionRing K]
    (χ : ℤ) (e : Multiset ℕ) :
    -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum =
      -((χ - e.count 0 : ℤ) : K) +
        ((e.filter (2 ≤ ·)).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  rw [e.sum_one_sub_one_div_eq_sum_filter_add_count_zero]
  push_cast
  abel

private theorem neg_intCast_add_sum_one_sub_one_div_add_natCast_eq {K : Type*} [DivisionRing K]
    (χ : ℤ) (e : Multiset ℕ) (c : ℕ) :
    -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c =
      -((χ - c : ℤ) : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  push_cast
  abel

private theorem neg_intCast_two_sub_two_mul {K : Type*} [DivisionRing K] (g : ℕ) :
    -((2 - 2 * (g : ℤ) : ℤ) : K) = 2 * (g : K) - 2 := by
  push_cast
  abel

private theorem finsum_mem_one_sub_inv_eq_sum_map {K α : Type*} [DivisionRing K] {s : Set α}
    (hs : s.Finite) (f : α → ℕ) :
    ∑ᶠ x ∈ s, (1 - (f x : K)⁻¹) =
      ((hs.toFinset.val.map f).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  simpa only [one_div] using
    hs.finsum_mem_comp_eq_multiset_sum_map f fun n : ℕ ↦ 1 - (n : K)⁻¹

private theorem one_notMem_map_toFinset_val {α : Type*} {s : Set α} (hs : s.Finite) {f : α → ℕ}
    (hf : ∀ x ∈ s, f x ≠ 1) : 1 ∉ hs.toFinset.val.map f := by
  simpa using hf

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

end CharZero

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### Elementary defect estimates -/

/-- The contribution `1 - 1 / n` of any natural number `n ≠ 1` is at least `1 / 2`. -/
theorem half_le_one_sub_one_div {n : ℕ} (hn : n ≠ 1) : (1 : K) / 2 ≤ 1 - 1 / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · norm_num
  · have hn2 : (2 : K) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    linarith [one_div_le_one_div_of_le (by norm_num : (0 : K) < 2) hn2]

/-- Half the number of branch points is at most their total contribution when `1 ∉ e`. -/
theorem card_div_two_le_sum_one_sub_one_div {e : Multiset ℕ} (he : 1 ∉ e) :
    (e.card : K) / 2 ≤ (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  have hcard : (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).card = e.card := Multiset.card_map _ _
  have hlow : ∀ x ∈ e.map fun n : ℕ ↦ 1 - 1 / (n : K), (1 : K) / 2 ≤ x := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Multiset.mem_map.mp hx
    exact half_le_one_sub_one_div fun h ↦ he (h ▸ hn)
  have := Multiset.card_nsmul_le_sum hlow
  rw [hcard, nsmul_eq_mul] at this
  linarith

/-! ### Core cuspless Euler-characteristic bounds (`χ ≤ 1` and `χ ≤ 2`) -/

/-- For `χ ≤ 1` and `1 ∉ e`, every positive deficit `-(χ : K) + ∑_{n ∈ e} (1 - 1 / n)` other than
`(χ, e) = (1, {2, 3})` is at least `1 / 4`, attained at `(1, {2, 4})`. -/
theorem one_div_four_le_neg_intCast_add_sum_one_sub_one_div_of_le_one_of_ne
    {χ : ℤ} {e : Multiset ℕ} (hχ : χ ≤ 1) (he : 1 ∉ e)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum)
    (hne : ¬ (χ = 1 ∧ e = {2, 3})) :
    (1 : K) / 4 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  have hlow : (e.card : K) / 2 ≤ (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum :=
    card_div_two_le_sum_one_sub_one_div he
  have hhigh : (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum ≤ e.card := e.sum_one_sub_one_div_le_card
  rcases (by omega : χ ≤ -1 ∨ χ = 0 ∨ χ = 1) with hneg | rfl | rfl
  · have hχ' : (χ : K) ≤ -1 := by exact_mod_cast hneg
    linarith [e.sum_one_sub_one_div_nonneg (K := K)]
  · have hne0 : e ≠ 0 := by
      rintro rfl
      simp at hpos
    have h1 : (1 : K) ≤ e.card := by exact_mod_cast Multiset.card_pos.mpr hne0
    simp only [Int.cast_zero, neg_zero, zero_add]
    linarith
  · have hne23 : e ≠ {2, 3} := fun h ↦ hne ⟨rfl, h⟩
    simp only [Int.cast_one] at hpos ⊢
    have hcard2 : 2 ≤ e.card := by
      have h1 : (1 : K) < e.card := by linarith
      have : (1 : ℕ) < e.card := by exact_mod_cast h1
      omega
    rcases eq_or_lt_of_le hcard2 with hc2 | hc3
    · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hc2.symm
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton] at hpos ⊢
      have hhyper : (1 : K) / a + 1 / b < 1 := by linarith
      linarith [one_div_four_le_hyperbolic_pair_deficit_of_ne hhyper hne23]
    · have hc3' : (3 : K) ≤ e.card := by exact_mod_cast hc3
      linarith

/-- For `χ ≤ 1` and any multiset `e : Multiset ℕ`, a positive deficit
`-(χ : K) + ∑_{n ∈ e} (1 - 1 / n)` is at least `1 / 6`. -/
theorem one_div_six_le_neg_intCast_add_sum_one_sub_one_div_of_le_one
    {χ : ℤ} {e : Multiset ℕ} (hχ : χ ≤ 1)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum) :
    (1 : K) / 6 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  rw [neg_intCast_add_sum_one_sub_one_div_filter_two_le] at hpos ⊢
  by_cases h : (χ - e.count 0 : ℤ) = 1 ∧ e.filter (2 ≤ ·) = {2, 3}
  · rcases h with ⟨hχ1, hf23⟩
    rw [hχ1, hf23]
    simp; norm_num
  · exact (by norm_num : (1 : K) / 6 ≤ 1 / 4).trans
      (one_div_four_le_neg_intCast_add_sum_one_sub_one_div_of_le_one_of_ne
        (by omega) (by simp) hpos h)

/-- With at least four entries in `e` (`1 ∉ e`) and sum strictly above `2`, the genus-zero deficit
`-2 + ∑ (1 - 1 / n)` is at least `1 / 6` (attained at `{2, 2, 2, 3}`). -/
private theorem one_div_six_le_neg_two_add_sum_of_four_le_card {e : Multiset ℕ}
    (he : 1 ∉ e) (hc4 : 4 ≤ e.card)
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
    have hdef : (2 : K) / 3 ≤ 1 - 1 / n := by
      have hn1 : n ≠ 1 := fun h ↦ he (h ▸ Multiset.mem_cons_self n t)
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · norm_num
      · have hn3 : (3 : K) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
        linarith [one_div_le_one_div_of_le (by norm_num : (0 : K) < 3) hn3]
    have ht : 1 ∉ t := fun h ↦ he (Multiset.mem_cons_of_mem h)
    have ht3 : (t.card : K) = 3 := by
      have : t.card = 3 := by simpa using hc4'.symm
      exact_mod_cast this
    simp only [Multiset.map_cons, Multiset.sum_cons]
    linarith [card_div_two_le_sum_one_sub_one_div (K := K) ht, ht3, hdef]

/-- For `χ ≤ 2` and `1 ∉ e`, every positive deficit `-(χ : K) + ∑_{n ∈ e} (1 - 1 / n)` other than
`(χ, e) = (2, {2, 3, 7})` is at least `1 / 24`, attained at `(2, {2, 3, 8})`. -/
theorem one_div_twenty_four_le_neg_intCast_add_sum_one_sub_one_div_of_ne
    {χ : ℤ} {e : Multiset ℕ} (hχ : χ ≤ 2) (he : 1 ∉ e)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum)
    (hne : ¬ (χ = 2 ∧ e = {2, 3, 7})) :
    (1 : K) / 24 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  rcases hχ.lt_or_eq with hlt | rfl
  · exact (by norm_num : (1 : K) / 24 ≤ 1 / 6).trans
      (one_div_six_le_neg_intCast_add_sum_one_sub_one_div_of_le_one (by omega) hpos)
  · have hne7 : e ≠ {2, 3, 7} := fun h ↦ hne ⟨rfl, h⟩
    have hhigh : (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum ≤ e.card := e.sum_one_sub_one_div_le_card
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

/-- For any integer `χ ≤ 2` and multiset `e : Multiset ℕ`, a positive deficit
`-(χ : K) + ∑_{n ∈ e} (1 - 1 / n)` is at least `1 / 42`. -/
theorem one_div_forty_two_le_neg_intCast_add_sum_one_sub_one_div
    {χ : ℤ} {e : Multiset ℕ} (hχ : χ ≤ 2)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum) :
    (1 : K) / 42 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  rw [neg_intCast_add_sum_one_sub_one_div_filter_two_le] at hpos ⊢
  by_cases h : (χ - e.count 0 : ℤ) = 2 ∧ e.filter (2 ≤ ·) = {2, 3, 7}
  · rcases h with ⟨hχ2, hf7⟩
    rw [hχ2, hf7]
    simp; norm_num
  · exact (by norm_num : (1 : K) / 42 ≤ 1 / 24).trans
      (one_div_twenty_four_le_neg_intCast_add_sum_one_sub_one_div_of_ne
        (by omega) (by simp) hpos h)

/-! ### Cusped orbifold deficits (`1 ≤ c`): `1 / 6` bound and `1 / 4` gap -/

/-- For `χ ≤ 2`, `1 ≤ c`, and `1 ∉ e`, every positive orbifold deficit
`-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) + c` other than `(χ, c, e) = (2, 1, {2, 3})` is at least `1 / 4`,
attained at `(2, 1, {2, 4})` (genus `0`, one cusp, and elliptic orders `2, 4`). -/
theorem one_div_four_le_neg_intCast_add_sum_one_sub_one_div_add_natCast_of_ne
    {χ : ℤ} {c : ℕ} {e : Multiset ℕ}
    (hχ : χ ≤ 2) (hc : 1 ≤ c) (he : 1 ∉ e)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c)
    (hne : ¬ (χ = 2 ∧ c = 1 ∧ e = {2, 3})) :
    (1 : K) / 4 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  rw [neg_intCast_add_sum_one_sub_one_div_add_natCast_eq] at hpos ⊢
  exact one_div_four_le_neg_intCast_add_sum_one_sub_one_div_of_le_one_of_ne
    (by omega) he hpos fun ⟨_, h23⟩ ↦ hne ⟨by omega, by omega, h23⟩

/-- For `χ ≤ 2`, `1 ≤ c`, and any multiset `e : Multiset ℕ`, a positive orbifold deficit
`-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) + c` is at least `1 / 6`. -/
theorem one_div_six_le_neg_intCast_add_sum_one_sub_one_div_add_natCast
    {χ : ℤ} {c : ℕ} {e : Multiset ℕ} (hχ : χ ≤ 2) (hc : 1 ≤ c)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c) :
    (1 : K) / 6 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  rw [neg_intCast_add_sum_one_sub_one_div_add_natCast_eq] at hpos ⊢
  exact one_div_six_le_neg_intCast_add_sum_one_sub_one_div_of_le_one (by omega) hpos

/-- **Second-smallest cusped orbifold deficit**: for `1 ≤ c` and `1 ∉ e`, every positive deficit
`2g - 2 + ∑_{n ∈ e} (1 - 1 / n) + c` other than `(g, c, e) = (0, 1, {2, 3})` is at least `1 / 4`,
attained at `(0, 1, {2, 4})`. -/
theorem one_div_four_le_orbifold_deficit_of_ne {g c : ℕ} {e : Multiset ℕ}
    (hc : 1 ≤ c) (he : 1 ∉ e)
    (hpos : 0 < 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c)
    (hne : ¬ (g = 0 ∧ c = 1 ∧ e = {2, 3})) :
    (1 : K) / 4 ≤ 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  rw [← neg_intCast_two_sub_two_mul] at hpos ⊢
  exact one_div_four_le_neg_intCast_add_sum_one_sub_one_div_add_natCast_of_ne
    (by omega) hc he hpos fun ⟨_, hc1, he23⟩ ↦ hne ⟨by omega, hc1, he23⟩

/-- **Sharp lower bound for cusped orbifold deficits**: for `1 ≤ c` and any multiset `e`, a
positive deficit `2g - 2 + ∑_{n ∈ e} (1 - 1 / n) + c` is at least `1 / 6`. -/
theorem one_div_six_le_orbifold_deficit {g c : ℕ} {e : Multiset ℕ}
    (hc : 1 ≤ c)
    (hpos : 0 < 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c) :
    (1 : K) / 6 ≤ 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  rw [← neg_intCast_two_sub_two_mul] at hpos ⊢
  exact one_div_six_le_neg_intCast_add_sum_one_sub_one_div_add_natCast (by omega) hc hpos

/-! ### General orbifold deficits (`c : ℕ`): Siegel's `1 / 42` bound and `1 / 24` gap -/

/-- For `χ ≤ 2`, arbitrary `c : ℕ`, and `1 ∉ e`, every positive orbifold deficit
`-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) + c` other than `(χ, c, e) = (2, 0, {2, 3, 7})` is at least
`1 / 24`, attained at `(2, 0, {2, 3, 8})`. -/
theorem one_div_twenty_four_le_neg_intCast_add_sum_one_sub_one_div_add_natCast_of_ne
    {χ : ℤ} {c : ℕ} {e : Multiset ℕ}
    (hχ : χ ≤ 2) (he : 1 ∉ e)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c)
    (hne : ¬ (χ = 2 ∧ c = 0 ∧ e = {2, 3, 7})) :
    (1 : K) / 24 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  rw [neg_intCast_add_sum_one_sub_one_div_add_natCast_eq] at hpos ⊢
  exact one_div_twenty_four_le_neg_intCast_add_sum_one_sub_one_div_of_ne
    (by omega) he hpos fun ⟨_, h7⟩ ↦ hne ⟨by omega, by omega, h7⟩

/-- **Siegel's numerical `1 / 42` bound with cusps (Euler-characteristic form).** For `χ ≤ 2`,
arbitrary `c : ℕ`, and any multiset `e : Multiset ℕ`, a positive orbifold deficit
`-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) + c` is at least `1 / 42`. -/
theorem one_div_forty_two_le_neg_intCast_add_sum_one_sub_one_div_add_natCast
    {χ : ℤ} {c : ℕ} {e : Multiset ℕ} (hχ : χ ≤ 2)
    (hpos : 0 < -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c) :
    (1 : K) / 42 ≤ -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  rw [neg_intCast_add_sum_one_sub_one_div_add_natCast_eq] at hpos ⊢
  exact one_div_forty_two_le_neg_intCast_add_sum_one_sub_one_div (by omega) hpos

/-- **Second-smallest orbifold deficit**: for any `g c : ℕ` and `1 ∉ e`, every positive deficit
`2g - 2 + ∑_{n ∈ e} (1 - 1 / n) + c` other than `(g, c, e) = (0, 0, {2, 3, 7})` is at least
`1 / 24`, attained at `(0, 0, {2, 3, 8})`. -/
theorem one_div_twenty_four_le_orbifold_deficit_of_ne {g c : ℕ} {e : Multiset ℕ}
    (he : 1 ∉ e)
    (hpos : 0 < 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c)
    (hne : ¬ (g = 0 ∧ c = 0 ∧ e = {2, 3, 7})) :
    (1 : K) / 24 ≤ 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  rw [← neg_intCast_two_sub_two_mul] at hpos ⊢
  exact one_div_twenty_four_le_neg_intCast_add_sum_one_sub_one_div_add_natCast_of_ne
    (by omega) he hpos fun ⟨_, hc0, he7⟩ ↦ hne ⟨by omega, hc0, he7⟩

/-- **Siegel's numerical `1 / 42` bound for orbifold deficits**: for any genus `g`, cusp count `c`,
and multiset `e`, a positive deficit `2g - 2 + ∑_{n ∈ e} (1 - 1 / n) + c` is at least `1 / 42`. -/
theorem one_div_forty_two_le_orbifold_deficit {g c : ℕ} {e : Multiset ℕ}
    (hpos : 0 < 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c) :
    (1 : K) / 42 ≤ 2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c := by
  rw [← neg_intCast_two_sub_two_mul] at hpos ⊢
  exact one_div_forty_two_le_neg_intCast_add_sum_one_sub_one_div_add_natCast (by omega) hpos

/-- **The sharp numerical bound for hyperbolic branch data**: for any genus `γ : ℕ` and multiset
`e : Multiset ℕ`, a positive cuspless deficit `2γ - 2 + ∑_{n ∈ e} (1 - 1 / n)` is at least
`1 / 42`. -/
theorem one_div_forty_two_le_hyperbolic_deficit {γ : ℕ} {e : Multiset ℕ}
    (hpos : 0 < 2 * (γ : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum) :
    (1 : K) / 42 ≤ 2 * (γ : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum := by
  rw [← neg_intCast_two_sub_two_mul] at hpos ⊢
  exact one_div_forty_two_le_neg_intCast_add_sum_one_sub_one_div (by omega) hpos

/-! ### `finsum` lower bounds for elliptic orbit sets -/

/-- **Siegel's `1 / 42` bound in `finsum` form (Euler-characteristic version).** For any `χ ≤ 2`,
cusp count `c : ℕ`, set `s : Set α`, and map `f : α → ℕ`, if
`0 < -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c`, then that deficit is at least `1 / 42`. Neither
finiteness of `s` nor a lower bound on `f` is needed. -/
theorem one_div_forty_two_le_neg_intCast_add_finsum_mem_one_sub_inv_add_natCast
    {α : Type*} {s : Set α} {f : α → ℕ} {χ : ℤ} {c : ℕ} (hχ : χ ≤ 2)
    (hpos : 0 < -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c) :
    (1 : K) / 42 ≤ -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c := by
  obtain ⟨e, he⟩ := s.exists_finsum_mem_comp_eq_multiset_sum_map f fun n : ℕ ↦ 1 - 1 / (n : K)
  simp_rw [← one_div, he] at hpos ⊢
  exact one_div_forty_two_le_neg_intCast_add_sum_one_sub_one_div_add_natCast hχ hpos

/-- **Siegel's `1 / 42` bound in `finsum` form (genus version).** For any `g c : ℕ`, set `s : Set α`
and `f : α → ℕ`, if `0 < 2g - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c`, then
`1 / 42 ≤ 2g - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c`. -/
theorem one_div_forty_two_le_orbifold_deficit_finsum {α : Type*} {s : Set α}
    {f : α → ℕ} {g c : ℕ}
    (hpos : 0 < 2 * (g : K) - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c) :
    (1 : K) / 42 ≤ 2 * (g : K) - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c := by
  rw [← neg_intCast_two_sub_two_mul] at hpos ⊢
  exact one_div_forty_two_le_neg_intCast_add_finsum_mem_one_sub_inv_add_natCast (by omega) hpos

/-- **Cusped `1 / 6` bound in `finsum` form (Euler-characteristic version).** For `χ ≤ 2`, `1 ≤ c`,
any set `s : Set α`, and any `f : α → ℕ`, a positive deficit
`-(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c` is at least `1 / 6`. -/
theorem one_div_six_le_neg_intCast_add_finsum_mem_one_sub_inv_add_natCast
    {α : Type*} {s : Set α} {f : α → ℕ} {χ : ℤ} {c : ℕ} (hχ : χ ≤ 2) (hc : 1 ≤ c)
    (hpos : 0 < -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c) :
    (1 : K) / 6 ≤ -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c := by
  obtain ⟨e, he⟩ := s.exists_finsum_mem_comp_eq_multiset_sum_map f fun n : ℕ ↦ 1 - 1 / (n : K)
  simp_rw [← one_div, he] at hpos ⊢
  exact one_div_six_le_neg_intCast_add_sum_one_sub_one_div_add_natCast hχ hc hpos

/-- **Cusped `1 / 6` bound in `finsum` form (genus version).** For `1 ≤ c`, any set `s : Set α`,
and any `f : α → ℕ`, if `0 < 2g - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c`, then
`1 / 6 ≤ 2g - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c`. -/
theorem one_div_six_le_orbifold_deficit_finsum {α : Type*} {s : Set α}
    {f : α → ℕ} {g c : ℕ} (hc : 1 ≤ c)
    (hpos : 0 < 2 * (g : K) - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c) :
    (1 : K) / 6 ≤ 2 * (g : K) - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c := by
  rw [← neg_intCast_two_sub_two_mul] at hpos ⊢
  exact one_div_six_le_neg_intCast_add_finsum_mem_one_sub_inv_add_natCast (by omega) hc hpos

end OrderedField

/-! ### Equality characterizations, Hurwitz's `84(g - 1)` bound, and witness checks -/

section CharZeroEqualities

variable {K : Type*} [DivisionRing K] [CharZero K]

/-- For `χ ≤ 1` and `1 ∉ e`, `-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) = 1 / 6` holds in any
characteristic-zero division ring if and only if `χ = 1` and `e = {2, 3}`. -/
theorem neg_intCast_add_sum_one_sub_one_div_eq_one_div_six_iff_of_le_one
    {χ : ℤ} {e : Multiset ℕ} (hχ : χ ≤ 1) (he : 1 ∉ e) :
    -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum = 1 / 6 ↔ χ = 1 ∧ e = {2, 3} := by
  refine ⟨fun heq ↦ ?_, ?_⟩
  · have heqQ : -(χ : ℚ) + (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum = 1 / 6 := by
      rw [← Rat.cast_inj (α := K)]
      simpa using heq
    by_contra hne
    linarith [one_div_four_le_neg_intCast_add_sum_one_sub_one_div_of_le_one_of_ne
      (K := ℚ) hχ he (by linarith) hne]
  · rintro ⟨rfl, rfl⟩
    simp; norm_num

/-- For `χ ≤ 2` and `1 ∉ e`, `-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) = 1 / 42` holds in any
characteristic-zero division ring if and only if `χ = 2` and `e = {2, 3, 7}`. -/
theorem neg_intCast_add_sum_one_sub_one_div_eq_one_div_forty_two_iff
    {χ : ℤ} {e : Multiset ℕ} (hχ : χ ≤ 2) (he : 1 ∉ e) :
    -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum = 1 / 42 ↔ χ = 2 ∧ e = {2, 3, 7} := by
  refine ⟨fun heq ↦ ?_, ?_⟩
  · have heqQ : -(χ : ℚ) + (e.map fun n : ℕ ↦ 1 - 1 / (n : ℚ)).sum = 1 / 42 := by
      rw [← Rat.cast_inj (α := K)]
      simpa using heq
    by_contra hne
    linarith [one_div_twenty_four_le_neg_intCast_add_sum_one_sub_one_div_of_ne
      (K := ℚ) hχ he (by linarith) hne]
  · rintro ⟨rfl, rfl⟩
    simp; norm_num

/-- For `χ ≤ 2`, `1 ≤ c`, and `1 ∉ e`, `-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) + c = 1 / 6` holds in any
characteristic-zero division ring if and only if `χ = 2`, `c = 1`, and `e = {2, 3}`. -/
theorem neg_intCast_add_sum_one_sub_one_div_add_natCast_eq_one_div_six_iff
    {χ : ℤ} {c : ℕ} {e : Multiset ℕ} (hχ : χ ≤ 2) (hc : 1 ≤ c) (he : 1 ∉ e) :
    -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c = 1 / 6 ↔
      χ = 2 ∧ c = 1 ∧ e = {2, 3} := by
  rw [neg_intCast_add_sum_one_sub_one_div_add_natCast_eq,
    neg_intCast_add_sum_one_sub_one_div_eq_one_div_six_iff_of_le_one (by omega) he]
  exact ⟨fun ⟨_, h23⟩ ↦ ⟨by omega, by omega, h23⟩, fun ⟨_, _, h23⟩ ↦ ⟨by omega, h23⟩⟩

/-- **Equality case for cusped orbifold deficits**: for `1 ≤ c` and `1 ∉ e`, the deficit
`2g - 2 + ∑_{n ∈ e} (1 - 1 / n) + c` equals `1 / 6` in any characteristic-zero division ring if and
only if `g = 0`, `c = 1`, and `e = {2, 3}`. -/
theorem orbifold_deficit_eq_one_div_six_iff {g c : ℕ} {e : Multiset ℕ}
    (hc : 1 ≤ c) (he : 1 ∉ e) :
    2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c = 1 / 6 ↔
      g = 0 ∧ c = 1 ∧ e = {2, 3} := by
  rw [← neg_intCast_two_sub_two_mul,
    neg_intCast_add_sum_one_sub_one_div_add_natCast_eq_one_div_six_iff (by omega) hc he]
  exact and_congr_left' ⟨by omega, by omega⟩

/-- For `χ ≤ 2`, arbitrary `c : ℕ`, and `1 ∉ e`,
`-(χ : K) + ∑_{n ∈ e} (1 - 1 / n) + c = 1 / 42` holds in any characteristic-zero division ring if
and only if `χ = 2`, `c = 0`, and `e = {2, 3, 7}`. -/
theorem neg_intCast_add_sum_one_sub_one_div_add_natCast_eq_one_div_forty_two_iff
    {χ : ℤ} {c : ℕ} {e : Multiset ℕ} (hχ : χ ≤ 2) (he : 1 ∉ e) :
    -(χ : K) + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c = 1 / 42 ↔
      χ = 2 ∧ c = 0 ∧ e = {2, 3, 7} := by
  rw [neg_intCast_add_sum_one_sub_one_div_add_natCast_eq,
    neg_intCast_add_sum_one_sub_one_div_eq_one_div_forty_two_iff (by omega) he]
  exact ⟨fun ⟨_, h7⟩ ↦ ⟨by omega, by omega, h7⟩, fun ⟨_, _, h7⟩ ↦ ⟨by omega, h7⟩⟩

/-- **Equality case of Siegel's `1 / 42` bound**: for any genus `g`, cusp count `c`, and `1 ∉ e`,
`2g - 2 + ∑_{n ∈ e} (1 - 1 / n) + c = 1 / 42` holds in any characteristic-zero division ring if and
only if `g = 0`, `c = 0`, and `e = {2, 3, 7}`. -/
theorem orbifold_deficit_eq_one_div_forty_two_iff {g c : ℕ} {e : Multiset ℕ}
    (he : 1 ∉ e) :
    2 * (g : K) - 2 + (e.map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + c = 1 / 42 ↔
      g = 0 ∧ c = 0 ∧ e = {2, 3, 7} := by
  rw [← neg_intCast_two_sub_two_mul,
    neg_intCast_add_sum_one_sub_one_div_add_natCast_eq_one_div_forty_two_iff (by omega) he]
  exact and_congr_left' ⟨by omega, by omega⟩

/-- **The numerical half of the Hurwitz bound**: if `n * (2γ - 2 + ∑ᵢ (1 - 1 / eᵢ)) = 2g - 2` in a
characteristic-zero division ring `K` with `g ≥ 2`, then `n ≤ 84 (g - 1)`. -/
theorem card_le_eighty_four_mul_sub_one {n g γ : ℕ} {e : Multiset ℕ} (hg : 2 ≤ g)
    (hkey : (n : K) * (2 * (γ : K) - 2 + (e.map fun m : ℕ ↦ 1 - 1 / (m : K)).sum) =
      2 * (g : K) - 2) :
    n ≤ 84 * (g - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  have hkeyQ : (n : ℚ) * (2 * (γ : ℚ) - 2 + (e.map fun m : ℕ ↦ 1 - 1 / (m : ℚ)).sum) =
      2 * (g : ℚ) - 2 := by
    rw [← Rat.cast_inj (α := K)]
    simpa [one_div] using hkey
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hgQ : (2 : ℚ) ≤ g := by exact_mod_cast hg
  have hDpos : 0 < 2 * (γ : ℚ) - 2 + (e.map fun m : ℕ ↦ 1 - 1 / (m : ℚ)).sum := by
    by_contra hcon
    have hle := mul_nonpos_of_nonneg_of_nonpos hnQ.le (not_lt.mp hcon)
    rw [hkeyQ] at hle
    linarith
  have hmul := mul_le_mul_of_nonneg_left (one_div_forty_two_le_hyperbolic_deficit hDpos) hnQ.le
  rw [hkeyQ] at hmul
  have hnat : (n : ℚ) ≤ ((84 * (g - 1) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ g)]
    linarith
  exact_mod_cast hnat

/-- **Equality case of Siegel's `1 / 42` bound in `finsum` form (Euler-characteristic version).**
For a finite set `s : Set α`, `f : α → ℕ` with `∀ x ∈ s, f x ≠ 1`, and `χ ≤ 2`,
`-(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 42` holds in any characteristic-zero division
ring if and only if `χ = 2`, `c = 0`, and each fibre `{x // x ∈ s ∧ f x = m}` has cardinality
`Multiset.count m {2, 3, 7}`. Finiteness of `s` is necessary for the converse because `Nat.card`
vanishes on infinite fibres. -/
theorem neg_intCast_add_finsum_mem_one_sub_inv_add_natCast_eq_one_div_forty_two_iff
    {α : Type*} {s : Set α} (hs : s.Finite) {f : α → ℕ} {χ : ℤ} {c : ℕ}
    (hχ : χ ≤ 2) (hf : ∀ x ∈ s, f x ≠ 1) :
    -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 42 ↔
      χ = 2 ∧ c = 0 ∧ ∀ m : ℕ, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3, 7} := by
  rw [finsum_mem_one_sub_inv_eq_sum_map hs f,
    neg_intCast_add_sum_one_sub_one_div_add_natCast_eq_one_div_forty_two_iff hχ
      (one_notMem_map_toFinset_val hs hf),
    hs.map_toFinset_val_eq_iff]
  simp_rw [Set.ncard_ofPred]

/-- **Equality case of Siegel's `1 / 42` bound in `finsum` form (genus version).** For a finite set
`s : Set α` and `f : α → ℕ` with `∀ x ∈ s, f x ≠ 1`,
`2g - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 42` holds in any characteristic-zero division
ring if and only if `g = 0`, `c = 0`, and
`∀ m, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3, 7}`. -/
theorem orbifold_deficit_finsum_eq_one_div_forty_two_iff {α : Type*} {s : Set α}
    (hs : s.Finite) {f : α → ℕ} {g c : ℕ} (hf : ∀ x ∈ s, f x ≠ 1) :
    2 * (g : K) - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 42 ↔
      g = 0 ∧ c = 0 ∧ ∀ m : ℕ, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3, 7} := by
  rw [← neg_intCast_two_sub_two_mul,
    neg_intCast_add_finsum_mem_one_sub_inv_add_natCast_eq_one_div_forty_two_iff hs (by omega) hf]
  exact and_congr_left' ⟨by omega, by omega⟩

/-- **Equality case of the cusped `1 / 6` bound in `finsum` form (Euler-characteristic version).**
For a finite set `s : Set α`, `f : α → ℕ` with `∀ x ∈ s, f x ≠ 1`, `χ ≤ 2`, and `1 ≤ c`,
`-(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 6` holds in any characteristic-zero division
ring if and only if `χ = 2`, `c = 1`, and
`∀ m, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3}`. -/
theorem neg_intCast_add_finsum_mem_one_sub_inv_add_natCast_eq_one_div_six_iff
    {α : Type*} {s : Set α} (hs : s.Finite) {f : α → ℕ} {χ : ℤ} {c : ℕ}
    (hχ : χ ≤ 2) (hc : 1 ≤ c) (hf : ∀ x ∈ s, f x ≠ 1) :
    -(χ : K) + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 6 ↔
      χ = 2 ∧ c = 1 ∧ ∀ m : ℕ, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3} := by
  rw [finsum_mem_one_sub_inv_eq_sum_map hs f,
    neg_intCast_add_sum_one_sub_one_div_add_natCast_eq_one_div_six_iff hχ hc
      (one_notMem_map_toFinset_val hs hf),
    hs.map_toFinset_val_eq_iff]
  simp_rw [Set.ncard_ofPred]

/-- **Equality case of the cusped `1 / 6` bound in `finsum` form (genus version).** For a finite
set `s : Set α`, `f : α → ℕ` with `∀ x ∈ s, f x ≠ 1`, and `1 ≤ c`,
`2g - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 6` holds in any characteristic-zero division
ring if and only if `g = 0`, `c = 1`, and
`∀ m, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3}`. -/
theorem orbifold_deficit_finsum_eq_one_div_six_iff {α : Type*} {s : Set α}
    (hs : s.Finite) {f : α → ℕ} {g c : ℕ} (hc : 1 ≤ c) (hf : ∀ x ∈ s, f x ≠ 1) :
    2 * (g : K) - 2 + (∑ᶠ x ∈ s, (1 - (f x : K)⁻¹)) + c = 1 / 6 ↔
      g = 0 ∧ c = 1 ∧ ∀ m : ℕ, Nat.card {x // x ∈ s ∧ f x = m} = Multiset.count m {2, 3} := by
  rw [← neg_intCast_two_sub_two_mul,
    neg_intCast_add_finsum_mem_one_sub_inv_add_natCast_eq_one_div_six_iff hs (by omega) hc hf]
  exact and_congr_left' ⟨by omega, by omega⟩

/-- The genus-zero branch data `(2, 3, 7)` attains the cuspless bound `1 / 42`, showing that the
constant in `TauCeti.one_div_forty_two_le_hyperbolic_deficit` is sharp. -/
theorem hyperbolic_deficit_two_three_seven :
    2 * ((0 : ℕ) : K) - 2 +
        (({2, 3, 7} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum = 1 / 42 := by
  simp; norm_num

-- Boundary and witness signature checks: `(0; 2, 3, 8; 0)`, `(0; 2, 2, 2, 3; 0)`,
-- `(0; 2, 2, 2, 2; 0)`, `(0; 2, 3; 1)`, and `(0; 2, 2; 1)`.
example :
    2 * ((0 : ℕ) : K) - 2 +
        (({2, 3, 8} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + (0 : ℕ) = 1 / 24 := by
  simp; norm_num

example :
    2 * ((0 : ℕ) : K) - 2 +
        (({2, 2, 2, 3} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + (0 : ℕ) = 1 / 6 := by
  simp; norm_num

example :
    2 * ((0 : ℕ) : K) - 2 +
        (({2, 2, 2, 2} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + (0 : ℕ) = 0 := by
  simp; norm_num

example :
    2 * ((0 : ℕ) : K) - 2 +
        (({2, 3} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + (1 : ℕ) = 1 / 6 := by
  simp; norm_num

example :
    2 * ((0 : ℕ) : K) - 2 +
        (({2, 2} : Multiset ℕ).map fun n : ℕ ↦ 1 - 1 / (n : K)).sum + (1 : ℕ) = 0 := by
  simp; norm_num

end CharZeroEqualities

end TauCeti
