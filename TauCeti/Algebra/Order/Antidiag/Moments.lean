/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Tactic.Linarith

/-!
# Binomial moments of monomials of fixed degree

The exponent vectors of degree `N` in a finite set `s` of variables are counted by
`Finset.finsuppAntidiag s N`. At any coordinate `i ∈ s`, the sum of `choose (f i) k`
over these vectors is `choose (N + card s - 1) (k + card s - 1)`.

The first two binomial moments, stated with denominators cleared, give the mean exponent
`N / card s` and the mean `choose (f i) 2`, namely `N (N - 1) / (card s (card s + 1))`.
These exact finite counts are the inputs to exponential-moment estimates for
multihomogeneous auxiliary polynomials; in particular no limiting distribution is needed
to estimate their tails.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §7.5.14 and Lemma 7.5.15.
-/

public section

namespace Finset

variable {ι : Type*} [DecidableEq ι]

/-- The binomial moment of one coordinate of a uniformly counted composition of `N`.
The support set contains the chosen coordinate, so it is nonempty. -/
theorem sum_piAntidiag_choose {s : Finset ι} {i : ι} (hi : i ∈ s) (N k : ℕ) :
    ∑ f ∈ piAntidiag s N, (f i).choose k =
      (N + s.card - 1).choose (k + s.card - 1) := by
  -- Keep the distinguished variable fixed and adjoin the other variables one at a time.
  have aux : ∀ (t : Finset ι) (i : ι), i ∉ t → ∀ N k : ℕ,
      ∑ f ∈ piAntidiag (insert i t) N, (f i).choose k =
        (N + t.card).choose (k + t.card) := by
    intro t
    induction t using Finset.cons_induction with
    | empty =>
      intro i _ N k
      have heq : piAntidiag {i} N = {Function.update (0 : ι → ℕ) i N} := by
        ext f
        simp only [mem_piAntidiag, sum_singleton, mem_singleton]
        constructor
        · rintro ⟨hf, hs⟩
          ext j
          by_cases hji : j = i
          · subst j; simpa using hf
          · simp only [Function.update_of_ne hji]
            exact not_ne_iff.mp (fun h ↦ hji (hs j h))
        · rintro rfl
          refine ⟨by simp, fun j hj ↦ ?_⟩
          by_contra hji
          simp [Function.update_of_ne hji] at hj
      simp [heq]
    | cons j t hj ih =>
      intro i hi N k
      have hit : i ∉ t := fun h ↦ hi (mem_cons_of_mem h)
      have hij : i ≠ j := fun h ↦ hi (by simp [h])
      have hji : j ∉ insert i t := by simp [hj, hij.symm]
      have heq : insert i (cons j t hj) = cons j (insert i t) hji := by
        ext x
        simp [or_left_comm]
      rw [heq, piAntidiag_cons hji, sum_disjiUnion]
      simp only [sum_map, addRightEmbedding_apply, Pi.add_apply,
        ite_eq_right hij, add_zero]
      simp_rw [ih i hit]
      simp only [card_cons]
      -- Adjoining a variable sums the previous moment over all possible residual degrees.
      induction N with
      | zero =>
        rcases k with _ | k
        · simp
        · rw [Nat.antidiagonal_zero, sum_singleton]
          simp only [zero_add]
          rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
      | succ N ihN =>
        rw [Nat.sum_antidiagonal_succ, ihN]
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (Nat.choose_succ_succ' (N + t.card + 1) (k + t.card)).symm
  have h := aux (s.erase i) i (notMem_erase i s) N k
  rw [insert_erase hi, card_erase_of_mem hi] at h
  simpa [Nat.add_sub_assoc (card_pos.mpr ⟨i, hi⟩)] using h

/-- The sum of the `k`th binomial coefficient of a fixed exponent over all monomials
of degree `N` supported in `s`. This also holds when `k > N`, when both sides vanish. -/
theorem sum_finsuppAntidiag_choose {s : Finset ι} {i : ι} (hi : i ∈ s) (N k : ℕ) :
    ∑ f ∈ finsuppAntidiag s N, (f i).choose k =
      (N + s.card - 1).choose (k + s.card - 1) := by
  -- The finitely supported antidiagonal is the injective image of the function antidiagonal.
  rw [finsuppAntidiag, sum_map]
  exact (sum_attach (piAntidiag s N) (fun f ↦ (f i).choose k)).trans
    (sum_piAntidiag_choose hi N k)

/-- The mean exponent of a degree-`N` monomial in `s` is `N / card s`, with denominators
cleared so that the identity holds in `ℕ`. -/
theorem card_mul_sum_finsuppAntidiag_apply {s : Finset ι} {i : ι} (hi : i ∈ s) (N : ℕ) :
    s.card * (∑ f ∈ finsuppAntidiag s N, f i) = N * (finsuppAntidiag s N).card := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (card_ne_zero.mpr ⟨i, hi⟩)
  have hs := sum_finsuppAntidiag_choose hi N 1
  simp only [Nat.choose_one_right] at hs
  rw [hs, card_finsuppAntidiag_nat_eq_choose, hm]
  simp only [Nat.succ_eq_add_one]
  have htop : N + (m + 1) - 1 = N + m := by omega
  have hbot : 1 + (m + 1) - 1 = m + 1 := by omega
  have hcard : m + 1 + N - 1 = N + m := by omega
  rw [htop, hbot, hcard, Nat.choose_symm_add]
  simpa [mul_comm] using Nat.choose_succ_right_eq (N + m) m

/-- The mean binomial square of an exponent of a degree-`N` monomial in `s` is
`N (N - 1) / (card s (card s + 1))`, with denominators cleared. This is the exact second
binomial moment used in exponential-moment bounds for monomials. -/
theorem card_mul_card_add_one_mul_sum_finsuppAntidiag_choose_two
    {s : Finset ι} {i : ι} (hi : i ∈ s) (N : ℕ) :
    s.card * (s.card + 1) * (∑ f ∈ finsuppAntidiag s N, (f i).choose 2) =
      N * (N - 1) * (finsuppAntidiag s N).card := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (card_ne_zero.mpr ⟨i, hi⟩)
  rw [sum_finsuppAntidiag_choose hi, card_finsuppAntidiag_nat_eq_choose, hm]
  simp only [Nat.succ_eq_add_one]
  have htop : N + (m + 1) - 1 = N + m := by omega
  have hbot : 2 + (m + 1) - 1 = m + 1 + 1 := by omega
  have hcard : m + 1 + N - 1 = N + m := by omega
  rw [htop, hbot, hcard, Nat.choose_symm_add]
  have h₁ := Nat.choose_succ_right_eq (N + m) m
  have h₂ := Nat.choose_succ_right_eq (N + m) (m + 1)
  have hsub : N + m - (m + 1) = N - 1 := by omega
  rw [Nat.add_sub_cancel_right] at h₁
  rw [hsub] at h₂
  nlinarith [congrArg (fun x ↦ x * (N - 1)) h₁, congrArg (fun x ↦ x * (m + 1)) h₂]

end Finset
