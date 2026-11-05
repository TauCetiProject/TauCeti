/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Alternating sums

This file gives a telescoping formula for alternating sums of consecutive pairs in an additive
commutative group, the evaluation of the alternating triangular double sum
`∑_{j = 0}^n ∑_{r ≤ j} (-1)^(j - r) = n / 2 + 1`, and the cancellation of alternating double sums
whose terms satisfy the simplicial identity, which is the combinatorial core of `d ∘ d = 0` for
alternating face map differentials. It also provides finite Euler sums for explicitly supported
`ℤ`-graded families, including support independence, additivity, and translation of the grading.
-/

public section

namespace TauCeti

variable {G : Type*} [AddCommGroup G]

/-! ### Finite Euler sums -/

/-- The Euler sum of a `ℤ`-indexed family over an explicit finite set of degrees. -/
def finiteEulerSum (f : ℤ → G) (s : Finset ℤ) : G :=
  ∑ n ∈ s, (n.negOnePow : ℤ) • f n

/-- A finite Euler sum is the alternating sum over its chosen finite set of degrees. -/
theorem finiteEulerSum_def (f : ℤ → G) (s : Finset ℤ) :
    finiteEulerSum f s = ∑ n ∈ s, (n.negOnePow : ℤ) • f n := by
  rw [finiteEulerSum]

@[simp]
theorem finiteEulerSum_empty (f : ℤ → G) : finiteEulerSum f ∅ = 0 := by
  simp [finiteEulerSum]

@[simp]
theorem finiteEulerSum_insert (f : ℤ → G) {s : Finset ℤ} {n : ℤ} (hn : n ∉ s) :
    finiteEulerSum f (insert n s) = (n.negOnePow : ℤ) • f n + finiteEulerSum f s := by
  simp [finiteEulerSum, hn]

/-- Pointwise equal families have equal Euler sums over the same finite set. -/
theorem finiteEulerSum_congr {f g : ℤ → G} {s : Finset ℤ} (h : ∀ n ∈ s, f n = g n) :
    finiteEulerSum f s = finiteEulerSum g s := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [h n hn]

@[simp]
theorem finiteEulerSum_zero (s : Finset ℤ) : finiteEulerSum (fun _ ↦ (0 : G)) s = 0 := by
  simp [finiteEulerSum]

/-- Euler sums distribute over pointwise addition. -/
@[simp]
theorem finiteEulerSum_add (f g : ℤ → G) (s : Finset ℤ) :
    finiteEulerSum (fun n ↦ f n + g n) s = finiteEulerSum f s + finiteEulerSum g s := by
  simp only [finiteEulerSum, smul_add, Finset.sum_add_distrib]

/-- Two finite sets supporting the same family compute the same Euler sum. -/
theorem finiteEulerSum_eq_of_eq_zero (f : ℤ → G) {s t : Finset ℤ}
    (hs : ∀ n, n ∉ s → f n = 0) (ht : ∀ n, n ∉ t → f n = 0) :
    finiteEulerSum f s = finiteEulerSum f t := by
  have hsu : finiteEulerSum f s = finiteEulerSum f (s ∪ t) :=
    Finset.sum_subset Finset.subset_union_left fun n _ hn ↦ by
      rw [hs n hn, smul_zero]
  have htu : finiteEulerSum f t = finiteEulerSum f (s ∪ t) :=
    Finset.sum_subset Finset.subset_union_right fun n _ hn ↦ by
      rw [ht n hn, smul_zero]
  rw [hsu, htu]

/-- Translating the grading by `m` multiplies its Euler sum by `(-1)ᵐ`. The set on the right is
the corresponding translate of the finite summation range. -/
theorem finiteEulerSum_reindex_add (f : ℤ → G) (m : ℤ) (s : Finset ℤ) :
    finiteEulerSum (fun n ↦ f (n + m)) s =
      (m.negOnePow : ℤ) •
        finiteEulerSum f (s.map (Equiv.addRight m).toEmbedding) := by
  rw [finiteEulerSum, finiteEulerSum, Finset.sum_map, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp only [Equiv.coe_toEmbedding, Equiv.coe_addRight, Int.negOnePow_add,
    Units.val_mul, smul_smul]
  rw [mul_left_comm, ← Units.val_mul, Int.units_mul_self]
  simp

/-! ### Telescoping and simplicial sums -/

/-- An alternating sum of consecutive pairs telescopes to its two end terms. -/
@[simp]
theorem sum_Icc_negOnePow_smul_add (f : ℤ → G) (a b : ℤ)
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

/-- An alternating double sum `∑ i, (-1)ⁱ • ∑ j, (-1)ʲ • F i j` vanishes when its terms satisfy
the simplicial identity `F (j + 1) i = F i j` for `i ≤ j`: the terms with `i ≤ j` cancel against
those with `j < i`. With `F i j = φ (d_j (d_i x))` this is `d ∘ d = 0` for an alternating sum of
faces `dᵢ`; the argument is that of Mathlib's
`AlgebraicTopology.AlternatingFaceMapComplex.d_squared`. -/
theorem sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero {G : Type*} [AddCommGroup G] {n : ℕ}
    (F : Fin (n + 3) → Fin (n + 2) → G)
    (hF : ∀ i j : Fin (n + 2), i ≤ j → F j.succ i = F i.castSucc j) :
    ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • F i j = 0 := by
  simp only [Finset.smul_sum, smul_smul, ← pow_add, ← Finset.sum_product']
  -- split the index set into the pairs with `i ≤ j` and their complement
  let S : Finset (Fin (n + 3) × Fin (n + 2)) := {ij | (ij.1 : ℕ) ≤ ij.2}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  -- the bijection `(i, j) ↦ (j + 1, i)` from `S` to its complement matches opposite terms
  refine Finset.sum_bij (fun ij hij ↦ (ij.2.succ, ij.1.castLT
      (lt_of_le_of_lt (Finset.mem_filter.1 hij).2 ij.2.is_lt))) ?_ ?_ ?_ ?_
  · intro ij hij
    simp only [S, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    simp only [Prod.mk.injEq, Fin.succ_inj] at h
    ext
    · simpa using congrArg Fin.val h.2
    · exact congrArg Fin.val h.1
  · rintro ⟨i', j'⟩ hij'
    simp only [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(Fin.castSucc j', i'.pred fun h ↦ by simp [h] at hij'), ?_, ?_⟩
    · simp only [S, Finset.mem_filter_univ, Fin.val_castSucc, Fin.val_pred]
      omega
    · simp
  · rintro ⟨i, j⟩ hij
    have hij : (i : ℕ) ≤ j := (Finset.mem_filter.1 hij).2
    dsimp only
    rw [hF _ _ (by simpa [Fin.le_def] using hij), Fin.castSucc_castLT, Fin.val_succ,
      Fin.val_castLT, ← neg_smul]
    congr 1
    ring

/-- In any ring, the alternating triangular double sum `∑_{j = 0}^n ∑_{r ≤ j} (-1)^(j - r)` equals
`n / 2 + 1`: the inner sum is `1` when `j` is even and `0` when `j` is odd. -/
theorem sum_Iic_neg_one_pow_sub {R : Type*} [Ring R] (n : ℕ) :
    ∑ j : Fin (n + 1), ∑ r ∈ Finset.Iic j, (-1 : R) ^ ((j : ℕ) - r) = (n / 2 + 1 : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have hinit : (∑ i : Fin (n + 1), ∑ r ∈ Finset.Iic i.castSucc,
        (-1 : R) ^ ((i.castSucc : ℕ) - r)) = (n / 2 + 1 : ℕ) := by
      simp_rw [Fin.sum_Iic_castSucc, Fin.val_castSucc]
      exact ih
    have hlast : (∑ r ∈ Finset.Iic (Fin.last (n + 1)),
        (-1 : R) ^ ((Fin.last (n + 1) : ℕ) - r)) = if Even (n + 2) then 0 else 1 := by
      rw [← Fin.top_eq_last, Finset.Iic_top, Fin.top_eq_last, Fin.val_last,
        ← Equiv.sum_comp Fin.revPerm]
      refine (Finset.sum_congr rfl fun x _ ↦ ?_).trans (Fin.sum_neg_one_pow R (n + 2))
      simp only [Fin.revPerm_apply, Fin.val_rev]
      congr 1
      omega
    rw [hinit, hlast]
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have heven : Even (k + k + 2) := ⟨k + 1, by omega⟩
      rw [ite_eq_left heven, add_zero, show (k + k + 1) / 2 = (k + k) / 2 by omega]
    · have hodd : ¬Even (2 * k + 1 + 2) := fun ⟨m, hm⟩ ↦ by omega
      rw [ite_eq_right hodd, show (2 * k + 1 + 1) / 2 + 1 = (2 * k + 1) / 2 + 1 + 1 by omega]
      push_cast
      abel

end TauCeti
