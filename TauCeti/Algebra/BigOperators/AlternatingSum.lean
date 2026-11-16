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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Alternating sums

This file gives a telescoping formula for alternating sums of consecutive pairs in an additive
commutative group, the evaluation of the alternating triangular double sum
`∑_{j = 0}^n ∑_{r ≤ j} (-1)^(j - r) = n / 2 + 1`, the cancellation of alternating double sums
whose terms satisfy the simplicial identity (the combinatorial core of `d ∘ d = 0` for
alternating face map differentials), and the telescoping cancellation of alternating double sums
satisfying the presimplicial homotopy relations (the combinatorial core of `H ∘ d + d ∘ H`). It
also provides finite Euler sums for explicitly supported `ℤ`-graded families, including support
independence, additivity, and translation of the grading. Finally, it relates the alternating sums
`xₙ - xₙ₋₁ + ⋯ ± x₀`, which appear in the strong Morse inequalities, to the Euler sums
`x₀ - x₁ + ⋯ ± xₙ` and to each other.
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

/-- Two finite sets compute the same Euler sum of a family that vanishes in every degree lying in
only one of them; for instance, when both sets contain the support of the family. -/
theorem finiteEulerSum_eq_of_eq_zero (f : ℤ → G) {s t : Finset ℤ}
    (hs : ∀ n ∈ t, n ∉ s → f n = 0) (ht : ∀ n ∈ s, n ∉ t → f n = 0) :
    finiteEulerSum f s = finiteEulerSum f t := by
  rw [finiteEulerSum_def, finiteEulerSum_def]
  exact Finset.sum_congr_of_eq_on_inter (fun n hn hnt ↦ by rw [ht n hn hnt, smul_zero])
    (fun n hn hns ↦ by rw [hs n hn hns, smul_zero]) fun _ _ _ ↦ rfl

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

private theorem sum_fin_split {n : ℕ} (j : Fin (n + 1)) (f : Fin (n + 2) → G) :
    ∑ i : Fin (n + 2), f i =
      (∑ i ∈ Finset.Iio j, f i.castSucc) + f j.castSucc + f j.succ +
        (∑ i ∈ Finset.Ioi j, f i.succ) := by
  have hgt : Finset.univ.filter (fun i : Fin (n + 2) ↦ ¬i ≤ j.castSucc) = Finset.Ici j.succ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Fin.le_def,
      Fin.val_castSucc, Fin.val_succ]
    omega
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin (n + 2) ↦ i ≤ j.castSucc),
    Finset.filter_ge_eq_Iic, hgt, Fin.sum_Iic_castSucc, Fin.sum_Ici_succ,
    ← Finset.sum_Iio_add_eq_sum_Iic, ← Finset.add_sum_Ioi_eq_sum_Ici]
  abel

private theorem sum_neg_one_pow_diag_band {n : ℕ} (F : Fin (n + 1) → Fin (n + 2) → G)
    (hdiag : ∀ k : Fin n, F k.castSucc k.succ.castSucc = F k.succ k.succ.castSucc) :
    (∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + j.castSucc) • F j j.castSucc) +
      (∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + j.succ) • F j j.succ) =
      F 0 0 - F (Fin.last n) (Fin.last (n + 1)) := by
  rw [Fin.sum_univ_succ (f := fun j : Fin (n + 1) ↦
      (-1 : ℤ) ^ ((j : ℕ) + j.castSucc) • F j j.castSucc),
    Fin.sum_univ_castSucc (f := fun j : Fin (n + 1) ↦
      (-1 : ℤ) ^ ((j : ℕ) + j.succ) • F j j.succ)]
  have hcancel :
      (∑ k : Fin n, (-1 : ℤ) ^ ((k.succ : ℕ) + k.succ.castSucc) • F k.succ k.succ.castSucc) +
        (∑ k : Fin n,
          (-1 : ℤ) ^ ((k.castSucc : ℕ) + k.castSucc.succ) • F k.castSucc k.castSucc.succ) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    simp only [Fin.succ_castSucc, hdiag k, ← add_smul, Fin.val_succ, Fin.val_castSucc]
    have hexp : k.1 + 1 + (k.1 + 1) = k.1 + (k.1 + 1) + 1 := by omega
    have hcoeff : (-1 : ℤ) ^ (k.1 + (k.1 + 1)) * -1 + (-1 : ℤ) ^ (k.1 + (k.1 + 1)) = 0 := by ring
    rw [hexp, pow_succ, hcoeff, zero_smul]
  have hs0 : (-1 : ℤ) ^ (((0 : Fin (n + 1)) : ℕ) + (0 : Fin (n + 1)).castSucc) •
      F 0 (0 : Fin (n + 1)).castSucc = F 0 0 := by simp
  have hslast : (-1 : ℤ) ^ (((Fin.last n) : ℕ) + (Fin.last n).succ) •
      F (Fin.last n) (Fin.last n).succ =
      -F (Fin.last n) (Fin.last (n + 1)) := by
    simp only [Fin.succ_last, Fin.val_last]
    have hexp : n + (n + 1) = 2 * n + 1 := by omega
    rw [hexp, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_smul]
  rw [hs0, hslast, add_assoc, ← add_assoc (∑ k : Fin n, _), hcancel, zero_add, sub_eq_add_neg]

private theorem sum_neg_one_pow_lower_tri {n : ℕ}
    (F : Fin (n + 1) → Fin (n + 2) → G) (E : Fin n → Fin (n + 1) → G)
    (hlo : ∀ (j : Fin n) (i : Fin (n + 1)), (i : ℕ) ≤ j → F j.succ i.castSucc = E j i) :
    (∑ j : Fin (n + 1), ∑ i ∈ Finset.Iio j,
        (-1 : ℤ) ^ ((j : ℕ) + i.castSucc) • F j i.castSucc) =
      -∑ j : Fin n, ∑ i ∈ Finset.Iic j.castSucc, (-1 : ℤ) ^ ((j : ℕ) + i) • E j i := by
  have hempty : Finset.Iio (0 : Fin (n + 1)) = ∅ := by ext; simp
  rw [Fin.sum_univ_succ, hempty, Finset.sum_empty, zero_add, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr (by ext i; simp [Fin.lt_def, Fin.le_def]) fun i hi ↦ ?_
  simp only [Finset.mem_Iic, Fin.le_def, Fin.val_castSucc] at hi
  simp only [hlo j i hi, Fin.val_succ, Fin.val_castSucc, ← neg_smul]
  congr 1
  rw [add_right_comm, pow_succ, mul_neg_one]

private theorem sum_neg_one_pow_upper_tri {n : ℕ}
    (F : Fin (n + 1) → Fin (n + 2) → G) (E : Fin n → Fin (n + 1) → G)
    (hhi : ∀ (j : Fin n) (i : Fin (n + 1)), (j : ℕ) < i → F j.castSucc i.succ = E j i) :
    (∑ j : Fin (n + 1), ∑ i ∈ Finset.Ioi j,
        (-1 : ℤ) ^ ((j : ℕ) + i.succ) • F j i.succ) =
      -∑ j : Fin n, ∑ i ∈ Finset.Ioi j.castSucc, (-1 : ℤ) ^ ((j : ℕ) + i) • E j i := by
  have hempty : Finset.Ioi (Fin.last n) = ∅ := by
    rw [← Fin.top_eq_last, Finset.Ioi_top]
  rw [Fin.sum_univ_castSucc, hempty, Finset.sum_empty, add_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp only [Finset.mem_Ioi, Fin.lt_def, Fin.val_castSucc] at hi
  simp only [hhi j i hi, Fin.val_castSucc, Fin.val_succ, ← neg_smul]
  congr 1
  rw [← add_assoc, pow_succ, mul_neg_one]

/-- Telescoping cancellation of two alternating double sums satisfying the presimplicial homotopy
relations: when adjacent diagonal terms agree (`F k.castSucc k.succ.castSucc = F k.succ
k.succ.castSucc`) and the strictly lower and upper triangles match `E`, the sum
`(∑ j, (-1)ʲ • ∑ i, (-1)ⁱ • F j i) + (∑ i, (-1)ⁱ • ∑ j, (-1)ʲ • E j i)` telescopes to
`F 0 0 - F (Fin.last n) (Fin.last (n + 1))`. With `F j i = h_j (δ_i ψ)` and
`E j i = δ_i (h_j ψ)` this is the combinatorial core of `H ∘ b + b ∘ H = h₀ ∘ δ₀ - hₙ ∘ δₙ₊₁`. -/
theorem sum_neg_one_pow_smul_sum_neg_one_pow_smul_add_eq_sub {G : Type*} [AddCommGroup G] {n : ℕ}
    (F : Fin (n + 1) → Fin (n + 2) → G) (E : Fin n → Fin (n + 1) → G)
    (hdiag : ∀ k : Fin n, F k.castSucc k.succ.castSucc = F k.succ k.succ.castSucc)
    (hlo : ∀ (j : Fin n) (i : Fin (n + 1)), (i : ℕ) ≤ j → F j.succ i.castSucc = E j i)
    (hhi : ∀ (j : Fin n) (i : Fin (n + 1)), (j : ℕ) < i → F j.castSucc i.succ = E j i) :
    (∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) •
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F j i) +
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        ∑ j : Fin n, (-1 : ℤ) ^ (j : ℕ) • E j i) =
      F 0 0 - F (Fin.last n) (Fin.last (n + 1)) := by
  have hS1 : (∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) •
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F j i) =
      ∑ j : Fin (n + 1), ∑ i : Fin (n + 2), (-1 : ℤ) ^ ((j : ℕ) + i) • F j i :=
    Finset.sum_congr rfl fun j _ ↦ by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_smul, ← pow_add]
  have hS2 : (∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
      ∑ j : Fin n, (-1 : ℤ) ^ (j : ℕ) • E j i) =
      ∑ j : Fin n, ∑ i : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + i) • E j i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [smul_smul, ← pow_add, add_comm]
  have hsplit : (∑ j : Fin (n + 1), ∑ i : Fin (n + 2), (-1 : ℤ) ^ ((j : ℕ) + i) • F j i) =
      (∑ j : Fin (n + 1), ∑ i ∈ Finset.Iio j,
        (-1 : ℤ) ^ ((j : ℕ) + i.castSucc) • F j i.castSucc) +
      (∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + j.castSucc) • F j j.castSucc) +
      (∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + j.succ) • F j j.succ) +
      (∑ j : Fin (n + 1), ∑ i ∈ Finset.Ioi j,
        (-1 : ℤ) ^ ((j : ℕ) + i.succ) • F j i.succ) := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ sum_fin_split j fun i ↦ (-1 : ℤ) ^ ((j : ℕ) + i) • F j i
  have htri :
      (∑ j : Fin n, ∑ i ∈ Finset.Iic j.castSucc, (-1 : ℤ) ^ ((j : ℕ) + i) • E j i) +
      (∑ j : Fin n, ∑ i ∈ Finset.Ioi j.castSucc, (-1 : ℤ) ^ ((j : ℕ) + i) • E j i) =
      ∑ j : Fin n, ∑ i : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + i) • E j i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Finset.filter_ge_eq_Iic, ← Finset.filter_lt_eq_Ioi]
    have hfilt : Finset.univ.filter (fun i : Fin (n + 1) ↦ j.castSucc < i) =
        Finset.univ.filter (fun i : Fin (n + 1) ↦ ¬i ≤ j.castSucc) := by ext; simp
    rw [hfilt, Finset.sum_filter_add_sum_filter_not]
  rw [hS1, hS2, hsplit, sum_neg_one_pow_lower_tri F E hlo, sum_neg_one_pow_upper_tri F E hhi,
    ← htri, ← sum_neg_one_pow_diag_band F hdiag]
  abel

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

/-! ### Alternating sums ending in degree `n` -/

/-- The alternating sum `xₙ - xₙ₋₁ + ⋯ ± x₀` is `(-1)ⁿ (x₀ - x₁ + ⋯ ± xₙ)`. -/
theorem sum_range_neg_one_pow_sub_smul (x : ℕ → G) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) • x i =
      (-1 : ℤ) ^ n • ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i • x i := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [smul_smul]
  congr 1
  have h : (-1 : ℤ) ^ n = (-1) ^ (n - i) * (-1) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel (Finset.mem_range_succ_iff.1 hi)]
  have hsq : ((-1 : ℤ) ^ i) ^ 2 = 1 := by rw [pow_right_comm, neg_one_sq, one_pow]
  linear_combination (-(-1 : ℤ) ^ i) * h - (-1 : ℤ) ^ (n - i) * hsq

/-- The alternating sums `sₙ = xₙ - xₙ₋₁ + ⋯ ± x₀` satisfy `sₙ₊₁ = xₙ₊₁ - sₙ`. -/
theorem sum_range_succ_neg_one_pow_sub_smul (x : ℕ → G) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 2), (-1 : ℤ) ^ (n + 1 - i) • x i =
      x (n + 1) - ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) • x i := by
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_smul, sub_eq_add_neg, add_comm,
    ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Nat.sub_add_comm (Finset.mem_range_succ_iff.1 hi), pow_succ, mul_neg_one, neg_smul]

/-- The alternating sum `xₙ - xₙ₋₁ + ⋯ ± x₀` in a ring is `(-1)ⁿ (x₀ - x₁ + ⋯ ± xₙ)`. -/
theorem sum_range_neg_one_pow_sub_mul {R : Type*} [Ring R] (x : ℕ → R) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : R) ^ (n - i) * x i =
      (-1 : R) ^ n * ∑ i ∈ Finset.range (n + 1), (-1 : R) ^ i * x i := by
  simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using
    sum_range_neg_one_pow_sub_smul x n

/-- The alternating sums `sₙ = xₙ - xₙ₋₁ + ⋯ ± x₀` in a ring satisfy `sₙ₊₁ = xₙ₊₁ - sₙ`. -/
theorem sum_range_succ_neg_one_pow_sub_mul {R : Type*} [Ring R] (x : ℕ → R) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 2), (-1 : R) ^ (n + 1 - i) * x i =
      x (n + 1) - ∑ i ∈ Finset.range (n + 1), (-1 : R) ^ (n - i) * x i := by
  simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using
    sum_range_succ_neg_one_pow_sub_smul x n

end TauCeti
