/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Data.Nat.Choose.Vandermonde
import TauCeti.Algebra.Order.Antidiag.Pi

/-!
# Vandermonde's identity for finitely many groups

Choosing `n` objects from a disjoint union of groups of sizes `K i`, for `i ∈ s`, amounts to
choosing `k i` objects from each group, for some function `k` whose values sum to `n`.  Counting
both ways gives the multivariate Vandermonde identity

```text
  ∑ k ∈ s.piAntidiag n, ∏ i ∈ s, choose (K i) (k i) = choose (∑ i ∈ s, K i) n.
```

Restricting to the choices with a prescribed number `m` of objects from one group `i` leaves
`choose (K i) m` choices there, times the Vandermonde count for the remaining groups. These
identities normalize the multivariate hypergeometric distribution and compute its coordinate
marginals. Prescribing a count in every fibre of a map of groups gives a product of binomial
coefficients, which describes merging categories of a sample.

## Main results

* `Finset.sum_piAntidiag_prod_choose`: the multivariate Vandermonde identity, generalizing
  Mathlib's `Nat.add_choose_eq`.
* `Finset.sum_filter_piAntidiag_prod_choose`: the same count with one coordinate prescribed.
* `Finset.sum_filter_piAntidiag_fiberwise_prod_choose`: the count with every fibre total
  prescribed.
-/

public section

namespace Finset

variable {ι : Type*} [DecidableEq ι]

/-- **Vandermonde's identity** for finitely many groups: the ways of choosing `n` objects from
groups of sizes `K i`, `i ∈ s`, sorted by how many come from each group. -/
theorem sum_piAntidiag_prod_choose (s : Finset ι) (K : ι → ℕ) (n : ℕ) :
    ∑ k ∈ s.piAntidiag n, ∏ i ∈ s, (K i).choose (k i) = (∑ i ∈ s, K i).choose n := by
  induction s using Finset.cons_induction generalizing n with
  | empty => cases n <;> simp
  | cons a s has ih =>
    rw [piAntidiag_cons, sum_disjiUnion, sum_cons, Nat.add_choose_eq]
    refine sum_congr rfl fun p _ ↦ ?_
    rw [sum_map, ← ih, mul_sum]
    refine sum_congr rfl fun g hg ↦ ?_
    have hga := eq_zero_of_notMem_of_mem_piAntidiag has hg
    rw [prod_cons]
    congr 1
    · simp [hga]
    · refine prod_congr rfl fun i hi ↦ ?_
      have hia : i ≠ a := ne_of_mem_of_not_mem hi has
      simp [hia]

/-- The ways of choosing `n` objects from groups of sizes `K j`, `j ∈ s`, with exactly `m`
objects from the group `i ∈ s`: there are `choose (K i) m` choices in that group, times the
Vandermonde count for the other groups. -/
theorem sum_filter_piAntidiag_prod_choose {s : Finset ι} {i : ι} (hi : i ∈ s) (K : ι → ℕ)
    (n m : ℕ) :
    ∑ k ∈ s.piAntidiag n with k i = m, ∏ j ∈ s, (K j).choose (k j) =
      if m ≤ n then (K i).choose m * (∑ j ∈ s.erase i, K j).choose (n - m) else 0 := by
  have hi' : i ∉ s.erase i := notMem_erase i s
  have hs : (s.erase i).cons i hi' = s := by simp [hi]
  conv_lhs => rw [sum_filter, ← hs, piAntidiag_cons, sum_disjiUnion]
  simp only [sum_map, addRightEmbedding_apply, Pi.add_apply, ↓reduceIte]
  -- Only the summand with `i`-coordinate `m` survives; it factors by Vandermonde's identity.
  have hterm : ∀ p ∈ antidiagonal n, ∀ g ∈ (s.erase i).piAntidiag p.2,
      (if g i + p.1 = m then ∏ j ∈ (s.erase i).cons i hi',
          (K j).choose (g j + if j = i then p.1 else 0) else 0) =
        if p.1 = m then (K i).choose m * ∏ j ∈ s.erase i, (K j).choose (g j) else 0 := by
    intro p _ g hg
    have hgi := eq_zero_of_notMem_of_mem_piAntidiag hi' hg
    rw [hgi, zero_add]
    split_ifs with hp
    · rw [prod_cons]
      congr 1
      · simp [hgi, hp]
      · refine prod_congr rfl fun j hj ↦ ?_
        simp [(mem_erase.mp hj).1]
    · rfl
  rw [sum_congr rfl fun p hp ↦ sum_congr rfl (hterm p hp)]
  split_ifs with hmn
  · rw [sum_eq_single (m, n - m)]
    · simp [← mul_sum, sum_piAntidiag_prod_choose]
    · rintro ⟨a, b⟩ hab hne
      have ha : a ≠ m := fun ham ↦ hne (by
        rw [mem_antidiagonal] at hab
        ext <;> simp <;> omega)
      simp [ha]
    · intro h
      exact absurd (by simp [mem_antidiagonal, Nat.add_sub_of_le hmn]) h
  · refine sum_eq_zero fun p hp ↦ ?_
    have ha : p.1 ≠ m := by
      rw [mem_antidiagonal] at hp
      omega
    simp [ha]

end Finset

namespace Finset

/-- Vandermonde's identity with the number of selected objects prescribed in every fibre of
a map of finite index types. The count factors over the fibres, provided their prescribed
counts have total `n`. -/
theorem sum_filter_piAntidiag_fiberwise_prod_choose {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (f : ι → κ) (K : ι → ℕ) (l : κ → ℕ) (n : ℕ) :
    ∑ k ∈ (univ.piAntidiag n).filter
        (fun k ↦ ∀ j, ∑ i : {i // f i = j}, k i = l j), ∏ i, (K i).choose (k i) =
      if ∑ j, l j = n then ∏ j, (∑ i : {i // f i = j}, K i).choose (l j) else 0 := by
  classical
  let e := Equiv.piCongrFiberwise (f := f) (γ₁ := fun _ ↦ ℕ)
    (fun j ↦ Equiv.refl ({i // f i = j} → ℕ))
  let t (j : κ) := (univ : Finset {i // f i = j}).piAntidiag (l j)
  by_cases hl : ∑ j, l j = n
  · rw [ite_eq_left hl]
    have hmem (k : ι → ℕ) :
        e k ∈ Fintype.piFinset t ↔
          k ∈ (univ.piAntidiag n).filter
            (fun k ↦ ∀ j, ∑ i : {i // f i = j}, k i = l j) := by
      simp only [Fintype.mem_piFinset, t, mem_piAntidiag, mem_univ, implies_true,
        and_true, Equiv.piCongrFiberwise_apply, Equiv.refl_apply, e, mem_filter]
      constructor
      · intro hk
        refine ⟨?_, hk⟩
        rw [← Fintype.sum_fiberwise f k]
        simpa only [hk] using hl
      · exact fun hk ↦ hk.2
    calc
      _ = ∑ v ∈ Fintype.piFinset t, ∏ j, ∏ i : {i // f i = j}, (K i).choose (v j i) := by
        refine sum_bij (fun k _ ↦ e k) (fun k hk ↦ (hmem k).2 hk)
          (fun _ _ _ _ h ↦ e.injective h) ?_ ?_
        · intro v hv
          exact ⟨e.symm v, (hmem _).1 ((e.apply_symm_apply v).symm ▸ hv), e.apply_symm_apply v⟩
        · intro k _
          exact (Fintype.prod_fiberwise f (fun i ↦ (K i).choose (k i))).symm
      _ = ∏ j, ∑ v ∈ t j, ∏ i : {i // f i = j}, (K i).choose (v i) :=
        (prod_univ_sum t (fun j v ↦ ∏ i : {i // f i = j}, (K i).choose (v i))).symm
      _ = _ := by simp only [t, sum_piAntidiag_prod_choose]
  · rw [ite_eq_right hl]
    apply sum_eq_zero
    intro k hk
    obtain ⟨hk, hf⟩ := mem_filter.mp hk
    have hsum := (mem_piAntidiag.mp hk).1
    rw [← Fintype.sum_fiberwise f k] at hsum
    exact (hl (by simpa only [hf] using hsum)).elim

end Finset
