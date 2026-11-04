/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import TauCeti.Order.Chain

/-!
# Combinations of chains of counting vectors

Let the vectors `C a`, for `a` in a finite set `A`, of natural numbers be distinct and pairwise
comparable, with each coordinate differing by at most one between any two of them. A combination
of them with real coefficients `v` summing to zero then has `ℓ¹` norm at least half the `ℓ¹` norm
of `v`. This is the counting estimate behind the uniform fatness of edgewise subdivisions.

## Main results

* `TauCeti.sum_abs_le_two_mul_sum_abs_sum_mul`: `∑ a, |v a| ≤ 2 * ∑ i, |∑ a, v a * C a i|`.
-/

public section

open Finset

namespace TauCeti

/-- Let the vectors `C a`, for `a ∈ A`, of natural numbers be distinct and pairwise comparable,
with each coordinate differing by at most one between any two of them. Then a combination of them
with coefficients `v` summing to zero satisfies `∑ a, |v a| ≤ 2 * ∑ i, |∑ a, v a * C a i|`. -/
theorem sum_abs_le_two_mul_sum_abs_sum_mul {α β : Type*} [Fintype β]
    (C : α → β → ℕ) (A : Finset α)
    (hC : ∀ a ∈ A, ∀ b ∈ A, (C a ≤ C b ∧ C b ≤ C a + 1) ∨ (C b ≤ C a ∧ C a ≤ C b + 1))
    (hinj : ∀ a ∈ A, ∀ b ∈ A, C a = C b → a = b) (v : α → ℝ) (hv : ∑ a ∈ A, v a = 0) :
    ∑ a ∈ A, |v a| ≤ 2 * ∑ i, |∑ a ∈ A, v a * C a i| := by
  classical
  -- Remove the largest vector `t`. Where it exceeds the second largest `t'`, all the other
  -- vectors agree with `t'`, so there the combination only sees the coefficient of `t`. Merge
  -- that coefficient into the one of `t'` and induct.
  induction A using Finset.strongInduction generalizing v with
  | H A ih =>
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  -- Every nonempty part of `A` has a vector dominating all the others in it.
  have hmax : ∀ B ⊆ A, B.Nonempty → ∃ t ∈ B, ∀ a ∈ B, C a ≤ C t := by
    intro B hBA hB
    have hchain : IsChain (· ≤ ·) (C '' (B : Set α)) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ -
      exact (hC a (hBA ha) b (hBA hb)).imp And.left And.left
    obtain ⟨_, ⟨t, ht, rfl⟩, hgreat⟩ :=
      hchain.exists_isGreatest (B.finite_toSet.image C) ((coe_nonempty.mpr hB).image C)
    exact ⟨t, ht, fun a ha => hgreat ⟨a, ha, rfl⟩⟩
  obtain ⟨t, htA, ht⟩ := hmax A subset_rfl hne
  rcases (A.erase t).eq_empty_or_nonempty with hA' | hA'
  · -- Then `A = {t}`, and `v t = 0`.
    obtain rfl : A = {t} := (erase_eq_empty_iff A t).mp hA' |>.resolve_left hne.ne_empty
    simp only [sum_singleton] at hv
    simp [hv]
  obtain ⟨t', ht'A', ht'⟩ := hmax (A.erase t) (erase_subset t A) hA'
  have ht'A : t' ∈ A := mem_of_mem_erase ht'A'
  -- Merge the coefficient of `t` into that of `t'`, and apply the induction hypothesis.
  set v' : α → ℝ := fun a => v a + if a = t' then v t else 0 with hv'_def
  have hsum' (f : α → ℝ) : ∑ a ∈ A.erase t, v' a * f a =
      ∑ a ∈ A.erase t, v a * f a + v t * f t' := by
    simp [hv'_def, add_mul, Finset.sum_add_distrib, ht'A']
  have hv' : ∑ a ∈ A.erase t, v' a = 0 := by
    have h := hsum' fun _ => 1
    simp only [mul_one] at h
    rw [h, sum_erase_add A v htA, hv]
  have hIH := ih (A.erase t) (erase_ssubset htA)
    (fun a ha b hb => hC a (mem_of_mem_erase ha) b (mem_of_mem_erase hb))
    (fun a ha b hb => hinj a (mem_of_mem_erase ha) b (mem_of_mem_erase hb)) v' hv'
  -- Coordinatewise, the vector of `t` exceeds that of `t'` by `0` or `1`.
  have htt' (i : β) : C t i = C t' i ∨ C t i = C t' i + 1 := by
    have h₁ : C t' i ≤ C t i := ht t' ht'A i
    rcases hC t htA t' ht'A with h | h
    · have h₂ : C t i ≤ C t' i := h.1 i
      omega
    · have h₂ : C t i ≤ C t' i + 1 := h.2 i
      omega
  have hcoord (i : β) : |∑ a ∈ A, v a * C a i| =
      |∑ a ∈ A.erase t, v' a * C a i| + |v t| * ((C t i : ℝ) - C t' i) := by
    rw [hsum' fun a => (C a i : ℝ), ← add_sum_erase A _ htA]
    rcases htt' i with h | h
    · rw [h, sub_self, mul_zero, add_zero, add_comm]
    · -- Where `t` exceeds `t'`, every other vector agrees with `t'`, so the rest cancels.
      have hagree : ∀ a ∈ A.erase t, C a i = C t' i := by
        intro a ha
        refine le_antisymm (ht' a ha i) ?_
        rcases hC a (mem_of_mem_erase ha) t htA with h' | h'
        · have h₂ : C t i ≤ C a i + 1 := h'.2 i
          omega
        · have h₂ : C t i ≤ C a i := h'.1 i
          omega
      have hrest : ∑ a ∈ A.erase t, v a * C a i + v t * C t' i = 0 := by
        rw [← hsum' fun a => (C a i : ℝ), Finset.sum_congr rfl fun a ha => by rw [hagree a ha],
          ← Finset.sum_mul, hv', zero_mul]
      rw [h, Nat.cast_add, Nat.cast_one, add_sub_cancel_left, mul_one, hrest, abs_zero, zero_add]
      congr 1
      linarith
  -- The vectors of `t` and `t'` differ somewhere.
  obtain ⟨i₀, hi₀⟩ : ∃ i, C t' i < C t i := by
    have hne : C t' ≠ C t := fun h => (ne_of_mem_erase ht'A') (hinj t' ht'A t htA h)
    exact (Pi.lt_def.mp (lt_of_le_of_ne (ht t' ht'A) hne)).2
  have hgap : 1 ≤ ∑ i, ((C t i : ℝ) - C t' i) := by
    calc (1 : ℝ) ≤ (C t i₀ : ℝ) - C t' i₀ := by
          rw [le_sub_iff_add_le', ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
          omega
      _ ≤ ∑ i, ((C t i : ℝ) - C t' i) :=
          single_le_sum (f := fun i => (C t i : ℝ) - C t' i)
            (fun i _ => sub_nonneg.mpr (Nat.cast_le.mpr (ht t' ht'A i))) (mem_univ i₀)
  -- Removing `t` costs `|v t|` once on the left and at least `|v t|` on the right.
  have hleft : ∑ a ∈ A.erase t, |v a| ≤ ∑ a ∈ A.erase t, |v' a| + |v t| := by
    have hpt (a : α) : |v a| ≤ |v' a| + if a = t' then |v t| else 0 := by
      split_ifs with h
      · simpa [hv'_def, h] using abs_sub (v t' + v t) (v t)
      · simp [hv'_def, h]
    calc ∑ a ∈ A.erase t, |v a| ≤ ∑ a ∈ A.erase t, (|v' a| + if a = t' then |v t| else 0) :=
          sum_le_sum fun a _ => hpt a
      _ = ∑ a ∈ A.erase t, |v' a| + |v t| := by simp [Finset.sum_add_distrib, ht'A']
  have hright : ∑ i, |∑ a ∈ A, v a * C a i| =
      ∑ i, |∑ a ∈ A.erase t, v' a * C a i| + |v t| * ∑ i, ((C t i : ℝ) - C t' i) := by
    simp only [hcoord, Finset.sum_add_distrib, Finset.mul_sum]
  rw [← add_sum_erase A _ htA, hright]
  nlinarith [abs_nonneg (v t)]

end TauCeti
