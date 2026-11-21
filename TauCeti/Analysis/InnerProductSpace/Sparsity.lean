/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.InformationTheory.Hamming

/-!
# Sparse vectors: restricted `ℓ¹` norms and best sparse approximation

The number of nonzero coordinates of `x : EuclideanSpace ℝ ι` is Mathlib's
`hammingNorm (WithLp.ofLp x)`, and `x` is `s`-sparse when this is at most `s`. Its
subadditivity is `TauCeti.hammingNorm_add_le`.

This file defines the restricted `ℓ¹` norm `∑_{j ∈ S} |xⱼ|` of `x` on a finite set `S` of
coordinates and the `ℓ¹` error `σₛ(x)₁ = inf {‖x - y‖₁ | y is s-sparse}` of the best `s`-sparse
approximation of `x` (Foucart–Rauhut, Def 2.2).

## Main definitions

* `EuclideanSpace.restrictedL1Norm x S`: the restricted `ℓ¹` norm `∑_{j ∈ S} |xⱼ|`; on
  `Finset.univ` it is the `ℓ¹` norm `‖x‖₁`.
* `EuclideanSpace.bestSparseL1Error x s`: the best `s`-sparse `ℓ¹` error `σₛ(x)₁`.

## Main results

* `EuclideanSpace.le_bestSparseL1Error_iff`: the lower bounds of `σₛ(x)₁` are the common lower
  bounds of the restricted norms of `x` on the complements of sets of at most `s` coordinates;
  by `EuclideanSpace.exists_restrictedL1Norm_compl_eq_bestSparseL1Error` one of these restricted
  norms equals `σₛ(x)₁`.
* `EuclideanSpace.bestSparseL1Error_eq_restrictedL1Norm_compl`: if `S` is a set of `s` largest
  coordinates of `|x|`, then `σₛ(x)₁` is the restricted norm of `x` on `Sᶜ`.
* `EuclideanSpace.exists_bestSparseL1Error_eq`: the infimum defining `σₛ(x)₁` is attained.
* `EuclideanSpace.bestSparseL1Error_eq_zero_iff`: `σₛ(x)₁ = 0` iff `x` is `s`-sparse.
* `EuclideanSpace.antitone_bestSparseL1Error`, `EuclideanSpace.bestSparseL1Error_le`,
  `EuclideanSpace.bestSparseL1Error_zero`: `σₛ(x)₁` is antitone in `s`, at most `‖x‖₁`, and
  equal to `‖x‖₁` for `s = 0`.

## References

* S. Foucart and H. Rauhut, *A Mathematical Introduction to Compressive Sensing*, Birkhäuser,
  2013, Def 2.2 (p. 42).

The definitions are adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Nonparametric/Basic.lean`; the proofs are new.
-/

public section

noncomputable section

open Finset

namespace EuclideanSpace

variable {ι : Type*}

/-- The Hamming weight of `x` is the number of its nonzero coordinates. -/
theorem hammingNorm_ofLp_eq_card_filter [Fintype ι] (x : EuclideanSpace ℝ ι) :
    hammingNorm (WithLp.ofLp x) = #{j | x j ≠ 0} :=
  (rfl)

/-! ### The restricted `ℓ¹` norm -/

/-- The restricted `ℓ¹` norm `∑_{j ∈ S} |xⱼ|` of `x` on a finite set `S` of coordinates. On
`Finset.univ` it is the `ℓ¹` norm `‖x‖₁`. -/
def restrictedL1Norm (x : EuclideanSpace ℝ ι) (S : Finset ι) : ℝ :=
  ∑ j ∈ S, |x j|

/-- The restricted `ℓ¹` norm is the sum of the absolute coordinates in `S`. -/
theorem restrictedL1Norm_def (x : EuclideanSpace ℝ ι) (S : Finset ι) :
    x.restrictedL1Norm S = ∑ j ∈ S, |x j| :=
  (rfl)

@[simp]
theorem restrictedL1Norm_empty (x : EuclideanSpace ℝ ι) : x.restrictedL1Norm ∅ = 0 := by
  simp [restrictedL1Norm_def]

/-- The restricted `ℓ¹` norm is nonnegative. -/
theorem restrictedL1Norm_nonneg (x : EuclideanSpace ℝ ι) (S : Finset ι) :
    0 ≤ x.restrictedL1Norm S :=
  sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The restricted `ℓ¹` norm is monotone in the set of coordinates. -/
theorem restrictedL1Norm_mono (x : EuclideanSpace ℝ ι) {S T : Finset ι} (h : S ⊆ T) :
    x.restrictedL1Norm S ≤ x.restrictedL1Norm T :=
  sum_le_sum_of_subset_of_nonneg h fun _ _ _ ↦ abs_nonneg _

/-- If every coordinate of `|x|` in `S` dominates every coordinate outside `S`, then the
restricted norm of `x` on any set `T` with at most as many elements as `S` is at most its
restricted norm on `S`. -/
theorem restrictedL1Norm_le_of_card_le (x : EuclideanSpace ℝ ι)
    {S T : Finset ι} (hTS : #T ≤ #S) (hS : ∀ i ∈ S, ∀ j ∉ S, |x j| ≤ |x i|) :
    x.restrictedL1Norm T ≤ x.restrictedL1Norm S := by
  classical
  have hcard : #(T \ S) ≤ #(S \ T) := card_sdiff_le_card_sdiff_iff.mpr hTS
  -- Each coordinate in `T \ S` is dominated by each coordinate in `S \ T`.
  have hsum : (#(S \ T) : ℝ) * x.restrictedL1Norm (T \ S) ≤
      #(T \ S) * x.restrictedL1Norm (S \ T) := by
    have := sum_le_sum fun i (hi : i ∈ S \ T) ↦ sum_le_sum fun j (hj : j ∈ T \ S) ↦
      hS i (mem_sdiff.1 hi).1 j (mem_sdiff.1 hj).2
    simpa [restrictedL1Norm_def, sum_const, nsmul_eq_mul, mul_sum, mul_comm] using this
  have hle : x.restrictedL1Norm (T \ S) ≤ x.restrictedL1Norm (S \ T) := by
    rcases Nat.eq_zero_or_pos #(S \ T) with h0 | hpos
    · have hTS0 : T \ S = ∅ := card_eq_zero.1 (by omega)
      rw [hTS0]
      simpa using x.restrictedL1Norm_nonneg (S \ T)
    · have hB := x.restrictedL1Norm_nonneg (S \ T)
      have hcard' : (#(T \ S) : ℝ) ≤ #(S \ T) := by exact_mod_cast hcard
      have hpos' : (0 : ℝ) < #(S \ T) := by exact_mod_cast hpos
      nlinarith
  have hT := sum_inter_add_sum_sdiff T S fun j ↦ |x j|
  have hS' := sum_inter_add_sum_sdiff S T fun j ↦ |x j|
  rw [inter_comm] at hS'
  simp only [restrictedL1Norm_def] at hle ⊢
  linarith

variable [Fintype ι]

/-- The restricted `ℓ¹` norms on a set and on its complement add up to the `ℓ¹` norm. -/
theorem restrictedL1Norm_add_restrictedL1Norm_compl [DecidableEq ι] (x : EuclideanSpace ℝ ι)
    (S : Finset ι) : x.restrictedL1Norm S + x.restrictedL1Norm Sᶜ = x.restrictedL1Norm univ :=
  sum_add_sum_compl S _

/-! ### The best `s`-sparse `ℓ¹` error -/

/-- The `ℓ¹` error `σₛ(x)₁ = inf {‖x - y‖₁ | y is s-sparse}` of the best `s`-sparse approximation
of `x`. -/
def bestSparseL1Error (x : EuclideanSpace ℝ ι) (s : ℕ) : ℝ :=
  ⨅ y : {y : EuclideanSpace ℝ ι // hammingNorm (WithLp.ofLp y) ≤ s},
    (x - y.val).restrictedL1Norm univ

/-- `σₛ(x)₁` is the infimum of the `ℓ¹` distances from `x` to `s`-sparse vectors. -/
theorem bestSparseL1Error_def (x : EuclideanSpace ℝ ι) (s : ℕ) :
    x.bestSparseL1Error s = ⨅ y : {y : EuclideanSpace ℝ ι // hammingNorm (WithLp.ofLp y) ≤ s},
      (x - y.val).restrictedL1Norm univ :=
  (rfl)

/-- There is a vector with at most `#T` nonzero coordinates whose `ℓ¹` distance to `x` is the
restricted norm of `x` on `Tᶜ`. One such vector is the truncation of `x` to `T`, which replaces
the coordinates of `x` outside `T` by zero. -/
theorem exists_hammingNorm_le_card_and_restrictedL1Norm_sub_eq_restrictedL1Norm_compl
    [DecidableEq ι] (x : EuclideanSpace ℝ ι) (T : Finset ι) :
    ∃ y : EuclideanSpace ℝ ι, hammingNorm (WithLp.ofLp y) ≤ #T ∧
      (x - y).restrictedL1Norm univ = x.restrictedL1Norm Tᶜ := by
  set y : EuclideanSpace ℝ ι := WithLp.toLp 2 fun j ↦ if j ∈ T then x j else 0
  have hy (j : ι) : y j = if j ∈ T then x j else 0 := by rw [PiLp.toLp_apply]
  refine ⟨y, ?_, ?_⟩
  · rw [hammingNorm_ofLp_eq_card_filter]
    refine card_le_card fun j hj ↦ ?_
    by_contra hjT
    simp [hy, hjT] at hj
  · rw [restrictedL1Norm_def, restrictedL1Norm_def, ← sum_add_sum_compl T]
    simp only [PiLp.sub_apply, hy]
    rw [sum_eq_zero fun j hj ↦ by simp [hj], zero_add]
    exact sum_congr rfl fun j hj ↦ by simp [mem_compl.1 hj]

/-- A vector vanishing outside `T` has `ℓ¹` distance to `x` at least the restricted norm of `x`
on `Tᶜ`. -/
theorem restrictedL1Norm_compl_le_restrictedL1Norm_sub [DecidableEq ι]
    (x : EuclideanSpace ℝ ι) {y : EuclideanSpace ℝ ι} {T : Finset ι} (hy : ∀ j ∉ T, y j = 0) :
    x.restrictedL1Norm Tᶜ ≤ (x - y).restrictedL1Norm univ := by
  calc x.restrictedL1Norm Tᶜ = (x - y).restrictedL1Norm Tᶜ :=
        sum_congr rfl fun j hj ↦ by simp [hy j (mem_compl.1 hj)]
    _ ≤ (x - y).restrictedL1Norm univ := (x - y).restrictedL1Norm_mono (subset_univ _)

/-- A real `c` is a lower bound of `σₛ(x)₁` iff it is a lower bound of the restricted norms of `x`
on the complements of all sets of at most `s` coordinates. The bound is attained:
see `EuclideanSpace.exists_restrictedL1Norm_compl_eq_bestSparseL1Error`. -/
theorem le_bestSparseL1Error_iff [DecidableEq ι] (x : EuclideanSpace ℝ ι) {s : ℕ} {c : ℝ} :
    c ≤ x.bestSparseL1Error s ↔ ∀ T : Finset ι, #T ≤ s → c ≤ x.restrictedL1Norm Tᶜ := by
  rw [bestSparseL1Error_def]
  constructor
  · intro hc T hT
    obtain ⟨y, hy, hxy⟩ :=
      x.exists_hammingNorm_le_card_and_restrictedL1Norm_sub_eq_restrictedL1Norm_compl T
    refine hc.trans (le_of_le_of_eq ?_ hxy)
    refine ciInf_le (f := fun y : {y : EuclideanSpace ℝ ι // hammingNorm (WithLp.ofLp y) ≤ s} ↦
      (x - y.val).restrictedL1Norm univ) ⟨0, ?_⟩ ⟨y, hy.trans hT⟩
    rintro _ ⟨z, rfl⟩
    exact restrictedL1Norm_nonneg _ _
  · intro hc
    have : Nonempty {y : EuclideanSpace ℝ ι // hammingNorm (WithLp.ofLp y) ≤ s} :=
      ⟨⟨0, by simp⟩⟩
    refine le_ciInf fun y ↦ (hc (univ.filter fun j ↦ y.val j ≠ 0)
      (hammingNorm_ofLp_eq_card_filter y.val ▸ y.property)).trans ?_
    exact x.restrictedL1Norm_compl_le_restrictedL1Norm_sub fun j hj ↦ by simpa using hj

/-- `σₛ(x)₁` is at most the restricted norm of `x` on the complement of any set of at most `s`
coordinates. -/
theorem bestSparseL1Error_le_restrictedL1Norm_compl [DecidableEq ι] (x : EuclideanSpace ℝ ι)
    {s : ℕ} {T : Finset ι} (hT : #T ≤ s) : x.bestSparseL1Error s ≤ x.restrictedL1Norm Tᶜ :=
  (x.le_bestSparseL1Error_iff.1 le_rfl) T hT

/-- `σₛ(x)₁` is nonnegative. -/
theorem bestSparseL1Error_nonneg (x : EuclideanSpace ℝ ι) (s : ℕ) :
    0 ≤ x.bestSparseL1Error s := by
  classical
  exact x.le_bestSparseL1Error_iff.2 fun T _ ↦ x.restrictedL1Norm_nonneg _

/-- `σₛ(x)₁` is at most the `ℓ¹` norm of `x`. -/
theorem bestSparseL1Error_le (x : EuclideanSpace ℝ ι) (s : ℕ) :
    x.bestSparseL1Error s ≤ x.restrictedL1Norm univ := by
  classical
  simpa using x.bestSparseL1Error_le_restrictedL1Norm_compl (T := ∅) (Nat.zero_le s)

/-- `σₛ(x)₁` is antitone in the sparsity level `s`. -/
theorem antitone_bestSparseL1Error (x : EuclideanSpace ℝ ι) : Antitone x.bestSparseL1Error := by
  classical
  exact fun s s' hss' ↦ x.le_bestSparseL1Error_iff.2 fun T hT ↦
    x.bestSparseL1Error_le_restrictedL1Norm_compl (hT.trans hss')

/-- `σₛ(x)₁` is the restricted norm of `x` on the complement of some set of at most `s`
coordinates. -/
theorem exists_restrictedL1Norm_compl_eq_bestSparseL1Error [DecidableEq ι]
    (x : EuclideanSpace ℝ ι) (s : ℕ) :
    ∃ T : Finset ι, #T ≤ s ∧ x.restrictedL1Norm Tᶜ = x.bestSparseL1Error s := by
  obtain ⟨T, hT, hmin⟩ := exists_min_image (univ.filter fun T : Finset ι ↦ #T ≤ s)
    (fun T ↦ x.restrictedL1Norm Tᶜ) ⟨∅, by simp⟩
  have hTs : #T ≤ s := (mem_filter.1 hT).2
  refine ⟨T, hTs, le_antisymm ?_ (x.bestSparseL1Error_le_restrictedL1Norm_compl hTs)⟩
  exact x.le_bestSparseL1Error_iff.2 fun T' hT' ↦ hmin T' (by simpa using hT')

/-- The infimum defining `σₛ(x)₁` is attained at an `s`-sparse vector. -/
theorem exists_bestSparseL1Error_eq (x : EuclideanSpace ℝ ι) (s : ℕ) :
    ∃ y : EuclideanSpace ℝ ι, hammingNorm (WithLp.ofLp y) ≤ s ∧
      x.bestSparseL1Error s = (x - y).restrictedL1Norm univ := by
  classical
  obtain ⟨T, hTs, hT⟩ := x.exists_restrictedL1Norm_compl_eq_bestSparseL1Error s
  obtain ⟨y, hy, hxy⟩ :=
    x.exists_hammingNorm_le_card_and_restrictedL1Norm_sub_eq_restrictedL1Norm_compl T
  exact ⟨y, hy.trans hTs, hT ▸ hxy.symm⟩

/-- If `S` is a set of `s` largest coordinates of `|x|`, then `σₛ(x)₁` is the restricted norm of
`x` on `Sᶜ`. -/
theorem bestSparseL1Error_eq_restrictedL1Norm_compl [DecidableEq ι] (x : EuclideanSpace ℝ ι)
    {s : ℕ} {S : Finset ι} (hS : #S = s) (hmax : ∀ i ∈ S, ∀ j ∉ S, |x j| ≤ |x i|) :
    x.bestSparseL1Error s = x.restrictedL1Norm Sᶜ := by
  refine le_antisymm (x.bestSparseL1Error_le_restrictedL1Norm_compl hS.le) ?_
  refine x.le_bestSparseL1Error_iff.2 fun T hT ↦ ?_
  have h := x.restrictedL1Norm_le_of_card_le (hT.trans hS.ge) hmax
  have hS' := x.restrictedL1Norm_add_restrictedL1Norm_compl S
  have hT' := x.restrictedL1Norm_add_restrictedL1Norm_compl T
  linarith

/-- `σ₀(x)₁` is the `ℓ¹` norm of `x`. -/
@[simp]
theorem bestSparseL1Error_zero (x : EuclideanSpace ℝ ι) :
    x.bestSparseL1Error 0 = x.restrictedL1Norm univ := by
  classical
  refine le_antisymm (x.bestSparseL1Error_le 0) (x.le_bestSparseL1Error_iff.2 fun T hT ↦ ?_)
  rw [card_eq_zero.1 (Nat.le_zero.1 hT), compl_empty]

/-- `σₛ(x)₁ = 0` iff `x` is `s`-sparse. -/
@[simp]
theorem bestSparseL1Error_eq_zero_iff (x : EuclideanSpace ℝ ι) {s : ℕ} :
    x.bestSparseL1Error s = 0 ↔ hammingNorm (WithLp.ofLp x) ≤ s := by
  classical
  constructor
  · intro h
    obtain ⟨T, hTs, hT⟩ := x.exists_restrictedL1Norm_compl_eq_bestSparseL1Error s
    rw [h, restrictedL1Norm_def, sum_eq_zero_iff_of_nonneg fun _ _ ↦ abs_nonneg _] at hT
    rw [hammingNorm_ofLp_eq_card_filter]
    refine le_trans (card_le_card fun j hj ↦ ?_) hTs
    by_contra hjT
    simp_all
  · intro h
    refine le_antisymm ?_ (x.bestSparseL1Error_nonneg s)
    refine (x.bestSparseL1Error_le_restrictedL1Norm_compl (T := univ.filter fun j ↦ x j ≠ 0)
      (hammingNorm_ofLp_eq_card_filter x ▸ h)).trans_eq (sum_eq_zero fun j hj ↦ ?_)
    simpa using hj

end EuclideanSpace
