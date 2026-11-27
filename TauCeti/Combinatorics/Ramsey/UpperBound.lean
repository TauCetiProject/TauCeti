/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Ramsey.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.FinCases

/-!
# Upper bounds for Ramsey numbers

For a demand `f : K → ℕ` satisfying `∀ k, 2 ≤ f k`, write `f - eₖ` for the demand obtained by
replacing `f k` by `f k - 1`. The Greenwood–Gleason recurrence bounds `ramseyNumber f` using the
numbers for all these lowered demands. It follows by applying the neighbourhood form of the
recurrence in `TauCeti.Combinatorics.Ramsey.Basic` at the Ramsey numbers themselves.

For two colours, the recurrence says
`R(s + 2, t + 2) ≤ R(s + 1, t + 2) + R(s + 2, t + 1)` and induction gives the explicit binomial
bound `R(s + 1, t + 1) ≤ (s + t).choose s`. More generally, if a candidate order is odd and one
lowered bound is even, a counterexample would make every degree in that colour graph odd,
contradicting `SimpleGraph.even_card_odd_degree_vertices`. For two colours this gives a strict
improvement when both smaller Ramsey numbers are even.

## Main results

* `TauCeti.ramseyNumber_add_card_le`: the multicolour Greenwood–Gleason recurrence.
* `TauCeti.ramseyNumber_fin_two_le_add`: its hypothesis-free two-colour specialization.
* `TauCeti.ramseyNumber_fin_two_le_choose`: the binomial upper bound for two colours.
* `TauCeti.ramseyProp_of_odd_sum_of_even`: the parity refinement for any finite type of colours.
* `TauCeti.ramseyNumber_fin_two_lt_add_of_even_of_even`: the strict two-colour recurrence for even
  lower terms.

## References

* R. E. Greenwood and A. M. Gleason, *Combinatorial relations and chromatic graphs*, Canadian
  Journal of Mathematics 7 (1955), 1–7: Theorems 2 and 6 for the two-colour bounds and the
  multicolour triangle case.
* S. P. Radziszowski, *Small Ramsey numbers*, Electronic Journal of Combinatorics, Dynamic Survey
  DS1, §6.1(a): the general multicolour recurrence, which is implicit in Greenwood–Gleason.
* P. Erdős, *Some remarks on the theory of graphs*, Bulletin of the American Mathematical Society
  53 (1947), 292–294: the contrasting probabilistic lower-bound method.
-/

public section

open Finset SimpleGraph

namespace TauCeti

private theorem update_fin_two_zero_sub_one (a b : ℕ) :
    Function.update ![a + 1, b] 0 (![a + 1, b] 0 - 1) = ![a, b] := by
  simpa using Fin.update_cons_zero (α := fun _ ↦ ℕ) (a + 1) ![b] a

private theorem update_fin_two_one_sub_one (a b : ℕ) :
    Function.update ![a, b + 1] 1 (![a, b + 1] 1 - 1) = ![a, b] := by
  rw [Matrix.cons_val_one, Matrix.cons_val_zero, Nat.add_sub_cancel,
    ← Fin.succ_zero_eq_one, ← Matrix.Fin.cons_vecCons a (b + 1) ![], ← Fin.cons_update]
  congr
  exact Fin.update_cons_zero (α := fun _ ↦ ℕ) (b + 1) ![] b

/-- The multicolour Ramsey-number recurrence of Greenwood and Gleason: if every demand is at
least two, then `ramseyNumber f + Fintype.card K` is at most two plus the sum of the Ramsey
numbers obtained by lowering each demand in turn. -/
theorem ramseyNumber_add_card_le {K : Type*} [Fintype K] [DecidableEq K]
    (f : K → ℕ) (hf : ∀ k, 2 ≤ f k) :
    ramseyNumber f + Fintype.card K ≤ 2 + ∑ k, ramseyNumber (Function.update f k (f k - 1)) := by
  let n : K → ℕ := fun k ↦ ramseyNumber (Function.update f k (f k - 1))
  have hn (k : K) : 0 < n k := ramseyNumber_pos_iff.2 fun j ↦ by
    by_cases hjk : j = k
    · subst j
      simp only [Function.update_self]
      have := hf k
      omega
    · simp only [Function.update_of_ne hjk]
      have := hf j
      omega
  have h : ramseyNumber f ≤ (∑ k, (n k - 1)) + 2 := by
    simpa [Nat.add_assoc] using RamseyProp.ramseyNumber_le
      (ramseyProp_succ_of_sum_lt (n := n) (N := (∑ k, (n k - 1)) + 1)
        (fun k ↦ by dsimp only [n]; exact ramseyProp_ramseyNumber _) (Nat.lt_succ_self _))
  have hsum : (∑ k, n k) = (∑ k, (n k - 1)) + Fintype.card K := by
    calc
      (∑ k, n k) = ∑ k, ((n k - 1) + 1) :=
        sum_congr rfl fun k _ ↦ (Nat.sub_add_cancel (hn k)).symm
      _ = _ := by simp [sum_add_distrib]
  dsimp only [n] at h hsum
  omega

/-- The two-colour recurrence
`R(s + 2, t + 2) ≤ R(s + 1, t + 2) + R(s + 2, t + 1)`. -/
theorem ramseyNumber_fin_two_le_add (s t : ℕ) :
    ramseyNumber ![s + 2, t + 2] ≤
      ramseyNumber ![s + 1, t + 2] + ramseyNumber ![s + 2, t + 1] := by
  have h := ramseyNumber_add_card_le ![s + 2, t + 2] (by
    intro k
    fin_cases k <;> simp)
  simp only [Fintype.card_fin, Fin.sum_univ_two, update_fin_two_zero_sub_one,
    update_fin_two_one_sub_one] at h
  omega

/-- The binomial upper bound `R(s + 1, t + 1) ≤ (s + t).choose s` for two colours. -/
theorem ramseyNumber_fin_two_le_choose (s t : ℕ) :
    ramseyNumber ![s + 1, t + 1] ≤ (s + t).choose s := by
  induction s generalizing t with
  | zero =>
      have h : ramseyNumber ![1, t + 1] ≤ 1 :=
        ramseyNumber_le_one_iff.2 ⟨0, by simp⟩
      simpa using h
  | succ s ihs =>
      induction t with
      | zero =>
          have h : ramseyNumber ![s + 1 + 1, 1] ≤ 1 :=
            ramseyNumber_le_one_iff.2 ⟨1, by simp⟩
          simpa using h
      | succ t iht =>
          calc
            ramseyNumber ![s + 1 + 1, t + 1 + 1] ≤
                ramseyNumber ![s + 1, t + 1 + 1] +
                  ramseyNumber ![s + 1 + 1, t + 1] := ramseyNumber_fin_two_le_add s t
            _ ≤ (s + (t + 1)).choose s + ((s + 1) + t).choose (s + 1) :=
              Nat.add_le_add (ihs (t + 1)) iht
            _ = (s + 1 + (t + 1)).choose (s + 1) := by
              have hsucc : s + 1 + (t + 1) = s + (t + 1) + 1 := by omega
              rw [hsucc, Nat.choose_succ_succ']
              congr 2
              omega

/-- Suppose the lowered Ramsey property holds on `n k` vertices for each colour `k`. If
`1 + ∑ k, (n k - 1)` is odd and `n k₀` is even, then the original Ramsey property holds on
`1 + ∑ k, (n k - 1)` vertices. -/
theorem ramseyProp_of_odd_sum_of_even {K : Type*} [Fintype K] [DecidableEq K] {f n : K → ℕ}
    (h : ∀ k, RamseyProp (Function.update f k (f k - 1)) (n k)) {k₀ : K}
    (hk₀ : Even (n k₀)) (hodd : Odd (1 + ∑ k, (n k - 1))) :
    RamseyProp f (1 + ∑ k, (n k - 1)) := by
  have hk₀' : n k₀ % 2 = 0 := Nat.even_iff.mp hk₀
  by_cases hn0 : n k₀ = 0
  · have hk1 : RamseyProp f 1 := by
      have hk1 := h k₀
      rw [hn0, ramseyProp_zero_iff] at hk1
      obtain ⟨j, hj⟩ := hk1
      rw [ramseyProp_one_iff]
      refine ⟨j, ?_⟩
      by_cases hjk : j = k₀
      · subst j
        simp only [Function.update_self] at hj ⊢
        omega
      · simp only [Function.update_of_ne hjk] at hj ⊢
        omega
    exact hk1.mono (by omega)
  · rw [ramseyProp_iff]
    intro C
    by_contra hC
    have hlt (v : Fin (1 + ∑ k, (n k - 1))) (k : K) : (C.labelGraph k).degree v < n k := by
      rw [← not_le]
      intro hk
      exact hC ((h k).exists_isNClique_of_le_degree (v := v) C hk)
    have hle (v : Fin (1 + ∑ k, (n k - 1))) (k : K) :
        (C.labelGraph k).degree v ≤ n k - 1 := by
      have := hlt v k
      omega
    have hsum (v : Fin (1 + ∑ k, (n k - 1))) :
        ∑ k, (C.labelGraph k).degree v = ∑ k, (n k - 1) := by
      simpa using TopEdgeLabeling.sum_degree_labelGraph C v
    have hdeg (v : Fin (1 + ∑ k, (n k - 1))) :
        (C.labelGraph k₀).degree v = n k₀ - 1 := by
      by_contra hv
      have hltdeg : (C.labelGraph k₀).degree v < n k₀ - 1 := by
        have := hle v k₀
        omega
      have hsumlt := sum_lt_sum (fun k _ ↦ hle v k) ⟨k₀, mem_univ _, hltdeg⟩
      have := hsum v
      omega
    have hdegodd (v : Fin (1 + ∑ k, (n k - 1))) : Odd ((C.labelGraph k₀).degree v) := by
      rw [hdeg, Nat.odd_iff]
      have hnpos : 0 < n k₀ := Nat.pos_of_ne_zero hn0
      omega
    have heven : Even (1 + ∑ k, (n k - 1)) := by
      simpa [hdegodd] using (C.labelGraph k₀).even_card_odd_degree_vertices
    exact (Nat.not_even_iff_odd.2 hodd) heven

/-- If `R(s + 1, t + 2)` and `R(s + 2, t + 1)` are even, then `R(s + 2, t + 2)` is strictly
less than their sum. -/
theorem ramseyNumber_fin_two_lt_add_of_even_of_even (s t : ℕ)
    (hs : Even (ramseyNumber ![s + 1, t + 2]))
    (ht : Even (ramseyNumber ![s + 2, t + 1])) :
    ramseyNumber ![s + 2, t + 2] <
      ramseyNumber ![s + 1, t + 2] + ramseyNumber ![s + 2, t + 1] := by
  let A := ramseyNumber ![s + 1, t + 2]
  let B := ramseyNumber ![s + 2, t + 1]
  have hA : 0 < A := ramseyNumber_pos_iff.2 fun k ↦ by fin_cases k <;> simp
  have hB : 0 < B := ramseyNumber_pos_iff.2 fun k ↦ by fin_cases k <;> simp
  have hs' : A % 2 = 0 := Nat.even_iff.mp hs
  have ht' : B % 2 = 0 := Nat.even_iff.mp ht
  have hprop : RamseyProp ![s + 2, t + 2] (A + B - 1) := by
    have hp : RamseyProp ![s + 2, t + 2] (1 + ∑ k : Fin 2, (![A, B] k - 1)) := by
      refine ramseyProp_of_odd_sum_of_even (n := ![A, B]) (k₀ := 0) ?_
        (by simpa only [Matrix.cons_val_zero, Nat.even_iff] using hs') ?_
      · intro k
        fin_cases k
        · simp only [Fin.zero_eta]
          rw [update_fin_two_zero_sub_one, Matrix.cons_val_zero]
          exact ramseyProp_ramseyNumber _
        · simp only [Fin.mk_one]
          rw [update_fin_two_one_sub_one, Matrix.cons_val_one, Matrix.cons_val_zero]
          exact ramseyProp_ramseyNumber _
      · rw [Nat.odd_iff]
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega
    convert hp using 1
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have hle := hprop.ramseyNumber_le
  dsimp only [A, B] at hle ⊢
  omega

end TauCeti
