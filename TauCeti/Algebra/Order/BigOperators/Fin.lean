/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Order estimates for sums and products of finite sequences

A nonnegative finite sequence in which every term is at most half of the previous one sums to at
most twice its first term. In Roth's lemma this bounds the sum of the weights `rᵢ` by `2 r₀`.

A nonnegative monotone sequence of length `D * k` bounds the `D`-th power of the product of `k`
of its terms, the `j`-th of which is taken no later than position `D * j`. This converts bounds
for vectors selected from an ordered family, such as a family of successive minima, into a bound
by the product of the whole family.

## Main results

* `Fin.sum_le_two_mul_of_two_mul_succ_le`: if `0 ≤ rᵢ` and `2 rᵢ₊₁ ≤ rᵢ`, then
  `∑ᵢ rᵢ ≤ 2 r₀`.
* `Fin.prod_pow_le_prod_of_monotone`: if `c` is nonnegative and monotone on `Fin (D * k)` and
  `s j ≤ D * j`, then `(∏ⱼ c (s j)) ^ D ≤ ∏ᵢ cᵢ`.
-/

public section

namespace Fin

/-- A nonnegative sequence whose terms at least halve at each step sums to at most twice its
first term. -/
theorem sum_le_two_mul_of_two_mul_succ_le {R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] {n : ℕ} {r : Fin (n + 1) → R} (hr : ∀ i, 0 ≤ r i)
    (h : ∀ i : Fin n, 2 * r i.succ ≤ r i.castSucc) : ∑ i, r i ≤ 2 * r 0 := by
  induction n with
  | zero =>
    rw [sum_univ_one, two_mul]
    exact le_add_of_nonneg_right (hr 0)
  | succ n ih =>
    have hs := ih (r := fun i ↦ r i.succ) (fun i ↦ hr _) fun i ↦ by
      rw [succ_castSucc]
      exact h i.succ
    have h0 := h 0
    rw [castSucc_zero] at h0
    rw [sum_univ_succ, two_mul]
    gcongr
    exact hs.trans h0

/-- Selecting `k` terms of a nonnegative monotone sequence of length `D * k`, the `j`-th at
position at most `D * j`, the product of the selected terms raised to the power `D` is at most the
product of the whole sequence: the `j`-th block of `D` consecutive terms bounds the `D`-th power of
the `j`-th selected term from above. -/
theorem prod_pow_le_prod_of_monotone {R : Type*} [CommMonoidWithZero R] [Preorder R]
    [PosMulMono R] {D k : ℕ} {c : Fin (D * k) → R} (hc0 : ∀ i, 0 ≤ c i)
    (hc : Monotone c) {s : Fin k → Fin (D * k)} (hs : ∀ j, (s j : ℕ) ≤ D * j) :
    (∏ j, c (s j)) ^ D ≤ ∏ i, c i := by
  have := PosMulMono.toMulPosMono (α := R)
  have hempty (hDk : D * k = 0) : ∏ i, c i = 1 := by
    have : IsEmpty (Fin (D * k)) := ⟨fun i ↦ by simpa [hDk] using i.2⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
  -- Monotonicity of products over nonempty finsets, which needs no `ZeroLEOneClass`.
  have key {ι : Type} {u v : ι → R} {t : Finset ι} (ht : t.Nonempty) (h0 : ∀ i ∈ t, 0 ≤ u i)
      (h1 : ∀ i ∈ t, u i ≤ v i) : ∏ i ∈ t, u i ≤ ∏ i ∈ t, v i := by
    induction ht using Finset.Nonempty.cons_induction with
    | singleton a => simpa using h1 a (by simp)
    | cons a s ha hs ih =>
      rw [Finset.prod_cons, Finset.prod_cons]
      exact mul_le_mul (h1 a (by simp)) (ih (fun i hi ↦ h0 i (by simp [hi]))
        fun i hi ↦ h1 i (by simp [hi]))
        (Finset.prod_induction_nonempty _ (0 ≤ ·) (fun _ _ ha hb ↦ mul_nonneg ha hb) hs
          fun i hi ↦ h0 i (by simp [hi])) ((h0 a (by simp)).trans (h1 a (by simp)))
  obtain rfl | hD := D.eq_zero_or_pos
  · rw [pow_zero, hempty (Nat.zero_mul k)]
  obtain rfl | hk := k.eq_zero_or_pos
  · rw [hempty (Nat.mul_zero D), Finset.univ_eq_empty, Finset.prod_empty, one_pow]
  let e : Fin k × Fin D ≃ Fin (D * k) := finProdFinEquiv.trans (finCongr (Nat.mul_comm k D))
  have he (p : Fin k × Fin D) : (e p : ℕ) = p.2 + D * p.1 := by simp [e]
  have hD' : (Finset.univ : Finset (Fin D)).Nonempty := ⟨⟨0, hD⟩, Finset.mem_univ _⟩
  rw [← e.prod_comp, Fintype.prod_prod_type, ← Finset.prod_pow]
  refine key ⟨⟨0, hk⟩, Finset.mem_univ _⟩ (fun j _ ↦ ?_) fun j _ ↦ ?_
  · rw [← Fin.prod_const]
    exact Finset.prod_induction_nonempty _ (0 ≤ ·) (fun _ _ ha hb ↦ mul_nonneg ha hb) hD'
      fun _ _ ↦ hc0 _
  rw [← Fin.prod_const]
  refine key hD' (fun _ _ ↦ hc0 _) fun t _ ↦ hc ?_
  rw [Fin.le_iff_val_le_val, he]
  exact (hs j).trans (Nat.le_add_left _ _)

end Fin
