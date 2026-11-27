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

For a demand `f : K → ℕ`, write `f - eₖ` for the demand obtained by replacing `f k` by
`f k - 1`. The Greenwood–Gleason recurrence bounds `ramseyNumber f` using the numbers for all
these lowered demands. It follows by applying the neighbourhood form of the recurrence in
`TauCeti.Combinatorics.Ramsey.Basic` at the Ramsey numbers themselves.

For two colours, the recurrence says
`R(s + 2, t + 2) ≤ R(s + 1, t + 2) + R(s + 2, t + 1)` and induction gives the explicit binomial
bound `R(s + 1, t + 1) ≤ (s + t).choose s`. There is a strict improvement when the two smaller
Ramsey numbers are even: otherwise an extremal colouring would have odd vertex cardinality, while
every degree in one of its colour graphs would be odd, contradicting the handshaking lemma.

## Main results

* `TauCeti.ramseyNumber_add_card_le`: the multicolour Greenwood–Gleason recurrence.
* `TauCeti.ramseyNumber_two_le_add`: its hypothesis-free two-colour specialization.
* `TauCeti.ramseyNumber_two_le_choose`: the binomial upper bound for two colours.
* `TauCeti.ramseyNumber_two_lt_of_even`: the strict two-colour recurrence for even lower terms.

## References

* R. E. Greenwood and A. M. Gleason, *Combinatorial relations and chromatic graphs*, Canadian
  Journal of Mathematics 7 (1955), 1–7: the recurrence, binomial estimate, and parity refinement.
* S. P. Radziszowski, *Small Ramsey numbers*, Electronic Journal of Combinatorics, Dynamic Survey
  DS1: the standard two-colour bounds and their numerical specializations.
* P. Erdős, *Some remarks on the theory of graphs*, Bulletin of the American Mathematical Society
  53 (1947), 292–294: the contrasting probabilistic lower-bound method.
-/

public section

open Finset SimpleGraph

namespace TauCeti

private theorem ramseyNumber_pos_of_forall_pos {K : Type*} [Finite K] {f : K → ℕ}
    (hf : ∀ k, 0 < f k) : 0 < ramseyNumber f := by
  refine Nat.pos_of_ne_zero fun h ↦ ?_
  obtain ⟨k, hk⟩ := ramseyNumber_eq_zero_iff.1 h
  exact (hf k).ne' hk

private theorem card_neighborFinset_lt_of_not_exists_isNClique {K V : Type*}
    [Finite K] [DecidableEq K] [Fintype V] [DecidableEq V] (f : K → ℕ)
    (C : TopEdgeLabeling V K)
    (hC : ¬∃ k, ∃ s : Finset V, (C.labelGraph k).IsNClique (f k) s) (v : V) (k : K) :
    #{w | (C.labelGraph k).Adj v w} < ramseyNumber (Function.update f k (f k - 1)) := by
  classical
  rw [← not_le]
  intro hk
  obtain ⟨j, s, hsA, hs⟩ := (ramseyProp_ramseyNumber _).exists_isNClique_subset C hk
  apply hC
  obtain rfl | hjk := eq_or_ne j k
  · obtain hj | hj := eq_or_ne (f j) 0
    · exact ⟨j, ∅, by simp [hj]⟩
    rw [Function.update_self] at hs
    refine ⟨j, insert v s, ?_⟩
    rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj)]
    exact hs.insert fun w hw ↦ by simpa using hsA hw
  · exact ⟨j, s, by rwa [Function.update_of_ne hjk] at hs⟩

/-- The multicolour Ramsey-number recurrence of Greenwood and Gleason: if every demand is at
least two, then `ramseyNumber f + Fintype.card K` is at most two plus the sum of the Ramsey
numbers obtained by lowering each demand in turn. -/
theorem ramseyNumber_add_card_le {K : Type*} [Fintype K] [DecidableEq K]
    (f : K → ℕ) (hf : ∀ k, 2 ≤ f k) :
    ramseyNumber f + Fintype.card K ≤ 2 + ∑ k, ramseyNumber (Function.update f k (f k - 1)) := by
  let n : K → ℕ := fun k ↦ ramseyNumber (Function.update f k (f k - 1))
  have hn (k : K) : 1 ≤ n k := by
    rw [Nat.one_le_iff_ne_zero, ne_eq, ramseyNumber_eq_zero_iff]
    push Not
    intro j
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
theorem ramseyNumber_two_le_add (s t : ℕ) :
    ramseyNumber ![s + 2, t + 2] ≤
      ramseyNumber ![s + 1, t + 2] + ramseyNumber ![s + 2, t + 1] := by
  have h := ramseyNumber_add_card_le ![s + 2, t + 2] (by
    intro k
    fin_cases k <;> simp)
  simp only [Fintype.card_fin, Fin.sum_univ_two] at h
  have h0 : Function.update ![s + 2, t + 2] 0 (![s + 2, t + 2] 0 - 1) =
      ![s + 1, t + 2] := by
    ext i
    fin_cases i <;> simp
  have h1 : Function.update ![s + 2, t + 2] 1 (![s + 2, t + 2] 1 - 1) =
      ![s + 2, t + 1] := by
    ext i
    fin_cases i <;> simp
  rw [h0, h1] at h
  omega

/-- The binomial upper bound `R(s + 1, t + 1) ≤ (s + t).choose s` for two colours. -/
theorem ramseyNumber_two_le_choose (s t : ℕ) :
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
                  ramseyNumber ![s + 1 + 1, t + 1] := ramseyNumber_two_le_add s t
            _ ≤ (s + (t + 1)).choose s + ((s + 1) + t).choose (s + 1) :=
              Nat.add_le_add (ihs (t + 1)) iht
            _ = (s + 1 + (t + 1)).choose (s + 1) := by
              have hsucc : s + 1 + (t + 1) = s + (t + 1) + 1 := by omega
              rw [hsucc, Nat.choose_succ_succ']
              congr 2
              omega

/-- If `R(s + 1, t + 2)` and `R(s + 2, t + 1)` are even, then `R(s + 2, t + 2)` is strictly
less than their sum. -/
theorem ramseyNumber_two_lt_of_even (s t : ℕ)
    (hs : Even (ramseyNumber ![s + 1, t + 2]))
    (ht : Even (ramseyNumber ![s + 2, t + 1])) :
    ramseyNumber ![s + 2, t + 2] <
      ramseyNumber ![s + 1, t + 2] + ramseyNumber ![s + 2, t + 1] := by
  let A := ramseyNumber ![s + 1, t + 2]
  let B := ramseyNumber ![s + 2, t + 1]
  have hA : 0 < A := ramseyNumber_pos_of_forall_pos fun k ↦ by fin_cases k <;> simp
  have hB : 0 < B := ramseyNumber_pos_of_forall_pos fun k ↦ by fin_cases k <;> simp
  have hs' : A % 2 = 0 := Nat.even_iff.mp hs
  have ht' : B % 2 = 0 := Nat.even_iff.mp ht
  have hprop : RamseyProp ![s + 2, t + 2] (A + B - 1) := by
    classical
    rw [ramseyProp_iff]
    intro C
    by_contra hC
    have h0 (v : Fin (A + B - 1)) : #{w | (C.labelGraph 0).Adj v w} < A := by
      convert card_neighborFinset_lt_of_not_exists_isNClique ![s + 2, t + 2] C hC v 0 using 1
      simp only [A]; congr 1
      funext i; fin_cases i <;> simp
    have h1 (v : Fin (A + B - 1)) : #{w | (C.labelGraph 1).Adj v w} < B := by
      convert card_neighborFinset_lt_of_not_exists_isNClique ![s + 2, t + 2] C hC v 1 using 1
      simp only [B]; congr 1
      funext i; fin_cases i <;> simp
    have hsum (v : Fin (A + B - 1)) :
        #{w | (C.labelGraph 0).Adj v w} + #{w | (C.labelGraph 1).Adj v w} =
          A + B - 1 - 1 := by
      have hunion : univ.biUnion (fun k ↦ {w | (C.labelGraph k).Adj v w}) = univ.erase v := by
        ext w
        simp only [mem_biUnion, mem_erase, mem_filter, mem_univ, true_and, and_true,
          TopEdgeLabeling.labelGraph_adj]
        constructor
        · rintro ⟨k, hvw, -⟩; exact hvw.symm
        · intro hvw; exact ⟨C.get v w hvw.symm, hvw.symm, rfl⟩
      calc
        _ = ∑ k, #{w | (C.labelGraph k).Adj v w} :=
          (Fin.sum_univ_two (fun k : Fin 2 ↦ #{w | (C.labelGraph k).Adj v w})).symm
        _ = #(univ.biUnion fun k ↦ {w | (C.labelGraph k).Adj v w}) :=
          (card_biUnion (s := univ) (t := fun k ↦ {w | (C.labelGraph k).Adj v w})
            fun k _ l _ hkl ↦ disjoint_filter.2 fun w _ hk hl ↦ SimpleGraph.disjoint_left.1
              (EdgeLabeling.pairwise_disjoint_labelGraph hkl) _ _ hk hl).symm
        _ = A + B - 1 - 1 := by rw [hunion]; simp
    have hdeg (v : Fin (A + B - 1)) : (C.labelGraph 0).degree v = A - 1 := by
      rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
      have := h0 v
      have := h1 v
      have := hsum v
      omega
    have hodd (v : Fin (A + B - 1)) : Odd ((C.labelGraph 0).degree v) := by
      rw [hdeg, Nat.odd_iff]; omega
    have heven : Even (A + B - 1) := by
      simpa [hodd] using (C.labelGraph 0).even_card_odd_degree_vertices
    exact (Nat.not_even_iff_odd.2 (by rw [Nat.odd_iff]; omega)) heven
  have hle := hprop.ramseyNumber_le
  dsimp only [A, B] at hle ⊢; omega
end TauCeti
