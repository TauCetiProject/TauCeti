/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import TauCeti.LinearAlgebra.Matrix.Connected
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Negative semidefiniteness from a positive null vector

Let `A` be a symmetric matrix over a linear ordered field whose off-diagonal entries are
nonnegative, and suppose that `A` kills a vector `m` with strictly positive entries. Then the
quadratic form of `A` is negative semidefinite, and when the positive-entry graph of `A` is
connected it vanishes exactly on the multiples of `m`
([Stacks, Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X)).

The intersection matrix of the special fibre of a regular model of a curve over a discrete
valuation ring has this shape, with `m` the vector of multiplicities of the components. The
statement is the source of the negative definiteness of the intersection form on vectors
supported on a proper subset of the components, which drives the classification of
configurations of components.

The proof is the first proof of the Stacks Project: writing `x = (yᵢ mᵢ)ᵢ`, the relation
`A m = 0` turns the quadratic form into
`2 xᵀ A x = -∑ᵢⱼ aᵢⱼ mᵢ mⱼ (yᵢ - yⱼ)²`, in which every term with `i ≠ j` is nonnegative and
every term with `i = j` vanishes.

## Main results

* `Matrix.two_mul_dotProduct_mulVec_eq_neg_sum`: the identity above, stated without dividing
  the entries of `x`.
* `Matrix.dotProduct_mulVec_nonpos_of_mulVec_eq_zero`: the quadratic form is negative
  semidefinite.
* `Matrix.dotProduct_mulVec_eq_zero_iff_of_mulVec_eq_zero`: under connectedness, its isotropic
  vectors are exactly the multiples of `m`.
-/

public section

namespace Matrix

open Finset

variable {C K : Type*} [Fintype C]

/-- If a symmetric matrix `A` over a field kills a vector `m` with nonzero entries, then its
quadratic form is `2 xᵀ A x = -∑ᵢⱼ aᵢⱼ (mⱼxᵢ - mᵢxⱼ)² / (mᵢmⱼ)`. -/
theorem two_mul_dotProduct_mulVec_eq_neg_sum [Field K] {A : Matrix C C K} (hA : A.IsSymm)
    {m : C → K} (hm : ∀ i, m i ≠ 0) (hAm : A *ᵥ m = 0) (x : C → K) :
    2 * (x ⬝ᵥ A *ᵥ x) =
      -∑ i, ∑ j, A i j * (m j * x i - m i * x j) ^ 2 / (m i * m j) := by
  have hterm (i j : C) : A i j * (m j * x i - m i * x j) ^ 2 / (m i * m j) =
      x i ^ 2 / m i * (A i j * m j) + x j ^ 2 / m j * (A j i * m i) -
        2 * (x i * (A i j * x j)) := by
    rw [hA.apply i j]
    field_simp [hm i, hm j]
    ring
  have hrow (i : C) : ∑ j, A i j * m j = 0 := by
    simpa [mulVec, dotProduct] using congrFun hAm i
  simp_rw [hterm, sum_sub_distrib, sum_add_distrib, ← mul_sum, hrow]
  rw [sum_comm (f := fun i j ↦ x j ^ 2 / m j * (A j i * m i))]
  simp_rw [← mul_sum, hrow]
  simp [mulVec, dotProduct, mul_sum]

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [Fintype C] in
/-- The summands of `Matrix.two_mul_dotProduct_mulVec_eq_neg_sum` are nonnegative when the
off-diagonal entries of `A` are nonnegative and the entries of `m` are positive. -/
private lemma sum_div_nonneg {A : Matrix C C K} (hnonneg : ∀ i j, i ≠ j → 0 ≤ A i j)
    {m : C → K} (hm : ∀ i, 0 < m i) (x : C → K) (i j : C) :
    0 ≤ A i j * (m j * x i - m i * x j) ^ 2 / (m i * m j) := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · have := hm i
    have := hm j
    have := hnonneg i j hij
    positivity

/-- The quadratic form of a symmetric matrix over a linear ordered field with nonnegative
off-diagonal entries is negative semidefinite as soon as the matrix kills a vector with positive
entries ([Stacks, Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X)). -/
theorem dotProduct_mulVec_nonpos_of_mulVec_eq_zero {A : Matrix C C K} (hA : A.IsSymm)
    (hnonneg : ∀ i j, i ≠ j → 0 ≤ A i j) {m : C → K} (hm : ∀ i, 0 < m i)
    (hAm : A *ᵥ m = 0) (x : C → K) :
    x ⬝ᵥ A *ᵥ x ≤ 0 := by
  have h := two_mul_dotProduct_mulVec_eq_neg_sum hA (fun i ↦ (hm i).ne') hAm x
  have hsum : 0 ≤ ∑ i, ∑ j, A i j * (m j * x i - m i * x j) ^ 2 / (m i * m j) :=
    sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ sum_div_nonneg hnonneg hm x i j
  linarith

/-- Let `A` be a symmetric matrix over a linear ordered field with nonnegative off-diagonal
entries and connected positive-entry graph, killing a vector `m` with positive entries. Then its
quadratic form vanishes exactly on the multiples of `m`
([Stacks, Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X)). -/
theorem dotProduct_mulVec_eq_zero_iff_of_mulVec_eq_zero {A : Matrix C C K} (hA : A.IsSymm)
    (hnonneg : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hconnected : ∀ i j, Relation.ReflTransGen (fun i j ↦ i ≠ j ∧ 0 < A i j) i j)
    {m : C → K} (hm : ∀ i, 0 < m i) (hAm : A *ᵥ m = 0) (x : C → K) :
    x ⬝ᵥ A *ᵥ x = 0 ↔ ∃ c : K, x = c • m := by
  constructor
  · intro hx
    rcases isEmpty_or_nonempty C with hC | hC
    · exact ⟨0, Subsingleton.elim _ _⟩
    obtain ⟨i₀⟩ := hC
    have h := two_mul_dotProduct_mulVec_eq_neg_sum hA (fun i ↦ (hm i).ne') hAm x
    rw [hx, mul_zero, zero_eq_neg] at h
    -- Every summand vanishes, so the ratios `xᵢ / mᵢ` agree along each edge of the graph.
    have hzero (i j : C) : A i j * (m j * x i - m i * x j) ^ 2 / (m i * m j) = 0 :=
      (sum_eq_zero_iff_of_nonneg fun i _ ↦ sum_nonneg fun j _ ↦
          sum_div_nonneg hnonneg hm x i j).mp h i (mem_univ i) |>
        (sum_eq_zero_iff_of_nonneg fun j _ ↦ sum_div_nonneg hnonneg hm x i j).mp |>
        fun h ↦ h j (mem_univ j)
    have hedge {i j : C} (hij : i ≠ j ∧ 0 < A i j) : x i / m i = x j / m j := by
      have hi := (hm i).ne'
      have hj := (hm j).ne'
      have hsq : (m j * x i - m i * x j) ^ 2 = 0 := by
        have := hzero i j
        rw [div_eq_zero_iff, mul_eq_zero] at this
        rcases this with (h | h) | h
        · exact absurd h hij.2.ne'
        · exact h
        · exact absurd h (mul_ne_zero hi hj)
      rw [div_eq_div_iff hi hj]
      linear_combination pow_eq_zero_iff (two_ne_zero) |>.mp hsq
    refine ⟨x i₀ / m i₀, funext fun j ↦ ?_⟩
    have hj : x i₀ / m i₀ = x j / m j := by
      induction hconnected i₀ j with
      | refl => rfl
      | tail _ hbc ih => exact ih.trans (hedge hbc)
    rw [Pi.smul_apply, smul_eq_mul, hj, div_mul_cancel₀ _ (hm j).ne']
  · rintro ⟨c, rfl⟩
    rw [mulVec_smul, hAm, smul_zero, dotProduct_zero]

end Matrix
