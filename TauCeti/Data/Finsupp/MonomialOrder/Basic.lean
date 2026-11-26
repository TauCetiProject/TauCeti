/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Basic facts about monomial orders

* `MonomialOrder.toSyn_lt_toSyn_add`: a proper multiple of an exponent is larger in every monomial
  order.
* `MonomialOrder.toSyn_lt_toSyn_mapDomain_swap`: exchanging the exponents of two variables so that
  the larger variable carries the larger exponent gives a larger exponent.
* `MonomialOrder.toSyn_sum_single_lt_of_card_eq`: among the subsets of a finite set `s` of
  variables with a given number of elements, the subset closed upwards in `s` has the largest
  squarefree exponent `∑ i ∈ t, single i 1`.

The last two statements are the exchange argument computing the leading exponents of elementary
symmetric polynomials and of polynomials invariant under transpositions of variables.
-/

public section

open Finsupp

namespace MonomialOrder

variable {σ : Type*}

/-- A proper multiple of an exponent is larger in every monomial order. -/
theorem toSyn_lt_toSyn_add (m : MonomialOrder σ) (k : σ →₀ ℕ) {s : σ →₀ ℕ} (hs : s ≠ 0) :
    m.toSyn k < m.toSyn (k + s) :=
  m.toSyn_strictMono (lt_add_of_pos_right k (pos_iff_ne_zero.mpr hs))

/-- Exchanging the exponents of two variables `X i > X j` increases an exponent `e` with
`e i < e j`: the larger variable then carries the larger exponent. -/
theorem toSyn_lt_toSyn_mapDomain_swap [DecidableEq σ] (m : MonomialOrder σ) {i j : σ}
    {e : σ →₀ ℕ} (hij : m.toSyn (single j 1) < m.toSyn (single i 1)) (he : e i < e j) :
    m.toSyn e < m.toSyn (e.mapDomain (Equiv.swap i j)) := by
  have hne : i ≠ j := by
    rintro rfl
    exact hij.ne rfl
  set k := e j - e i
  have he' : e = (e - single j k) + single j k := by
    ext x
    by_cases hx : x = j
    · subst hx
      simp only [coe_add, coe_tsub, Pi.add_apply, Pi.sub_apply, single_eq_same]
      omega
    · simp [Ne.symm hx]
  have hswap : e.mapDomain (Equiv.swap i j) = (e - single j k) + single i k := by
    ext x
    rw [mapDomain_equiv_apply, Equiv.symm_swap]
    by_cases hxi : x = i
    · subst hxi
      simp only [Equiv.swap_apply_left, coe_add, coe_tsub, Pi.add_apply, Pi.sub_apply,
        single_eq_same, single_eq_of_ne hne]
      omega
    by_cases hxj : x = j
    · subst hxj
      simp only [Equiv.swap_apply_right, coe_add, coe_tsub, Pi.add_apply, Pi.sub_apply,
        single_eq_same, single_eq_of_ne (Ne.symm hne)]
      omega
    · simp [Equiv.swap_apply_of_ne_of_ne hxi hxj, Ne.symm hxi, Ne.symm hxj]
  rw [hswap]
  conv_lhs => rw [he']
  rw [map_add, map_add, ← smul_single_one j k, ← smul_single_one i k, map_nsmul, map_nsmul]
  exact add_lt_add_right (nsmul_lt_nsmul_right (Nat.sub_ne_zero_of_lt he) hij) _

/-- Among the subsets `u` of a finite set `s` of variables with as many elements as `t ⊆ s`, the
subset `t` has the largest squarefree exponent `∑ i ∈ t, single i 1` if it is closed upwards in
`s`: every variable of `s` larger than a variable of `t` belongs to `t`. -/
theorem toSyn_sum_single_lt_of_card_eq (m : MonomialOrder σ) {s t u : Finset σ} (ht : t ⊆ s)
    (hup : ∀ i ∈ t, ∀ j ∈ s, m.toSyn (single i 1) < m.toSyn (single j 1) → j ∈ t)
    (hu : u ⊆ s) (hcard : u.card = t.card) (hut : u ≠ t) :
    m.toSyn (∑ i ∈ u, single i 1) < m.toSyn (∑ i ∈ t, single i 1) := by
  classical
  induction hn : (u \ t).card using Nat.strong_induction_on generalizing u with
  | _ n ih =>
  obtain ⟨j, hju, hjt⟩ : ∃ j ∈ u, j ∉ t := by
    by_contra! h
    exact hut (Finset.eq_of_subset_of_card_le h hcard.ge)
  obtain ⟨i, hit, hiu⟩ : ∃ i ∈ t, i ∉ u := by
    by_contra! h
    exact hut (Finset.eq_of_subset_of_card_le h hcard.le).symm
  have hji : m.toSyn (single j 1) < m.toSyn (single i 1) := by
    rcases lt_trichotomy (m.toSyn (single j 1)) (m.toSyn (single i 1)) with h | h | h
    · exact h
    · rw [single_left_inj one_ne_zero |>.1 (m.toSyn.injective h)] at hjt
      exact absurd hit hjt
    · exact absurd (hup i hit j (hu hju) h) hjt
  have hiu' : i ∉ u.erase j := fun h ↦ hiu (Finset.mem_of_mem_erase h)
  have hlt : m.toSyn (∑ x ∈ u, single x 1) < m.toSyn (∑ x ∈ insert i (u.erase j), single x 1) := by
    rw [← Finset.add_sum_erase u _ hju, Finset.sum_insert hiu', map_add, map_add]
    exact add_lt_add_left hji _
  by_cases hu't : insert i (u.erase j) = t
  · rwa [hu't] at hlt
  refine hlt.trans (ih _ ?_ ?_ ?_ hu't rfl)
  · have : insert i (u.erase j) \ t = (u \ t).erase j := by
      ext x
      by_cases hx : x = i
      · subst hx
        simp [hit]
      · simp only [Finset.mem_sdiff, Finset.mem_insert, hx, false_or, Finset.mem_erase]
        tauto
    rw [this, Finset.card_erase_of_mem (Finset.mem_sdiff.2 ⟨hju, hjt⟩), ← hn]
    exact Nat.sub_lt (Finset.card_pos.2 ⟨j, Finset.mem_sdiff.2 ⟨hju, hjt⟩⟩) one_pos
  · exact Finset.insert_subset (ht hit) ((Finset.erase_subset _ _).trans hu)
  · rw [Finset.card_insert_of_notMem hiu', Finset.card_erase_of_mem hju, ← hcard]
    have := Finset.card_pos.2 ⟨j, hju⟩
    omega

end MonomialOrder
