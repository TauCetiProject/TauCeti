/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Abel

/-!
# Alternating sums

This file gives a telescoping formula for alternating sums of consecutive pairs over integer
intervals in an additive commutative group, and the vanishing of an alternating double sum over
`Fin (n + 2) × Fin (n + 1)` whose terms satisfy the semi-simplicial identity. The latter is the
cancellation behind `∂ ∘ ∂ = 0` for boundaries built as alternating sums of face operators.
-/

public section

namespace TauCeti

/-- An alternating sum of consecutive pairs telescopes to its two end terms. -/
@[simp]
theorem sum_Icc_negOnePow_smul_add {G : Type*} [AddCommGroup G] (f : ℤ → G) (a b : ℤ)
    (hab : a ≤ b) :
    ∑ n ∈ Finset.Icc a b, ((n.negOnePow : ℤ) • f n + (n.negOnePow : ℤ) • f (n + 1)) =
      (a.negOnePow : ℤ) • f a + (b.negOnePow : ℤ) • f (b + 1) := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hb ih =>
    have hins : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp), ih, Int.negOnePow_succ]
    simp only [Units.val_neg, neg_smul]
    abel

/-- An alternating double sum over `Fin (n + 2) × Fin (n + 1)` vanishes when its terms satisfy the
semi-simplicial identity `F (j + 1) i = F i j` for `i ≤ j`: the terms indexed by `(j + 1, i)` and
by `(i, j)` cancel in pairs. This is the pairing in the proof of Mathlib's
`AlgebraicTopology.AlternatingFaceMapComplex.d_squared`, stated for an arbitrary family `F`. -/
theorem sum_sum_neg_one_pow_smul_eq_zero {G : Type*} [AddCommGroup G] {n : ℕ}
    (F : Fin (n + 2) → Fin (n + 1) → G)
    (hF : ∀ i j : Fin (n + 1), i ≤ j → F j.succ i = F i.castSucc j) :
    ∑ k : Fin (n + 2), ∑ l : Fin (n + 1), (-1 : ℤ) ^ ((k : ℕ) + l) • F k l = 0 := by
  have hF' (a b : ℕ) (ha : a < n + 1) (hb : b < n + 1) (hab : a ≤ b) :
      F ⟨b + 1, by omega⟩ ⟨a, ha⟩ = F ⟨a, by omega⟩ ⟨b, hb⟩ :=
    hF ⟨a, ha⟩ ⟨b, hb⟩ hab
  rw [← Finset.sum_product']
  -- the term at `(k, l)` cancels the term at `(l + 1, k)` if `k ≤ l`, and at `(l, k - 1)` if not
  let g : Fin (n + 2) × Fin (n + 1) → Fin (n + 2) × Fin (n + 1) := fun p ↦
    if h : (p.1 : ℕ) ≤ p.2 then
      (⟨p.2 + 1, by have := p.2.isLt; omega⟩, ⟨p.1, by have := p.2.isLt; omega⟩)
    else (⟨p.2, by have := p.2.isLt; omega⟩, ⟨p.1 - 1, by have := p.1.isLt; omega⟩)
  refine Finset.sum_involution (fun p _ ↦ g p) (fun ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ _ ↦ ?_)
    (fun ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ _ _ ↦ ?_) (fun _ _ ↦ Finset.mem_univ _)
    (fun ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ _ ↦ ?_)
  · by_cases h : k ≤ l
    · simp only [g, h, dite_true, hF' k l (by omega) hl h]
      rw [show l + 1 + k = k + l + 1 by omega, pow_succ]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [g, h, dite_false, Nat.add_sub_cancel, hF' l k hl (by omega) (by omega)]
      rw [show k + 1 + l = l + k + 1 by omega, pow_succ]
      simp
  · by_cases h : k ≤ l <;> simp [g, h, Prod.ext_iff] <;> omega
  · by_cases h : k ≤ l
    · simp [g, h, show ¬ l + 1 ≤ k by omega]
    · simp [g, h, show l ≤ k - 1 by omega, show k - 1 + 1 = k by omega]

end TauCeti
