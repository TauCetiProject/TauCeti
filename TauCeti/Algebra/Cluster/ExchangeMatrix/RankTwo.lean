/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation
public import Mathlib.LinearAlgebra.Matrix.Symmetric

import Mathlib.Algebra.Order.Ring.Abs

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FinCases

/-!
# Cartan companions and rank-two mutation classes

The Cartan companion has diagonal entries two and off-diagonal entries `-|bᵢⱼ|`.
Every positive skew-symmetrizer of an exchange matrix symmetrizes its companion.
Either mutation of a rank-two skew-symmetrizable matrix negates it. Its full mutation class is
`{B, -B}`, even when the product of its off-diagonal entries has absolute value at least four.
The bound at most three throughout this class is equivalent to the bound at the initial matrix.
These statements concern matrix mutation classes, not finiteness of cluster variables.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras II: Finite type classification*,
  Inventiones Mathematicae 154 (2003), §1, Theorem 1.8 and the rank-two discussion.
-/

public section

open Matrix

namespace TauCeti

variable {K : Type*} [DecidableEq K]

/-- The Cartan companion of an integer matrix has diagonal two and negative absolute
values off the diagonal. -/
def cartanCompanion (B : Matrix K K ℤ) : Matrix K K ℤ :=
  of fun i j ↦ if i = j then 2 else -|B i j|

/-- The entries of the Cartan companion. -/
theorem cartanCompanion_apply (B : Matrix K K ℤ) (i j : K) :
    cartanCompanion B i j = if i = j then 2 else -|B i j| := by rfl

/-- Negating a matrix does not change its Cartan companion. -/
@[simp]
theorem cartanCompanion_neg (B : Matrix K K ℤ) : cartanCompanion (-B) = cartanCompanion B := by
  ext i j
  simp [cartanCompanion_apply]

/-- A positive skew-symmetrizer gives symmetric weighted entries in the Cartan companion. -/
theorem mul_cartanCompanion_apply {B : Matrix K K ℤ} {s : K → ℤ}
    (h : B.IsSkewSymmetrizer s) (i j : K) :
    s i * cartanCompanion B i j = s j * cartanCompanion B j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · have habs := congrArg abs (h.mul_apply i j)
    simp only [abs_mul, abs_of_pos (h.pos i), abs_of_pos (h.pos j), abs_neg] at habs
    simpa [cartanCompanion_apply, hij, Ne.symm hij] using congrArg Neg.neg habs

/-- Scaling the rows of the Cartan companion by a positive skew-symmetrizer gives a
symmetric matrix. -/
theorem isSymm_diagonal_mul_cartanCompanion [Fintype K] {B : Matrix K K ℤ} {s : K → ℤ}
    (h : B.IsSkewSymmetrizer s) : (diagonal s * cartanCompanion B).IsSymm := by
  ext i j
  simpa only [transpose_apply, diagonal_mul] using mul_cartanCompanion_apply h j i

section RankTwo

/-- Either rank-two mutation negates a skew-symmetrizable matrix. -/
theorem matrixMutation_rankTwo {B : Matrix (Fin 2) (Fin 2) ℤ} {s : Fin 2 → ℤ}
    (h : B.IsSkewSymmetrizer s) (k : Fin 2) :
    matrixMutation (Function.Embedding.refl _) B k = -B := by
  have hp (i j : Fin 2) : (B i j)⁺ * (B j i)⁺ = 0 := by
    by_cases hi : 0 ≤ B i j
    · have hj : B j i ≤ 0 := not_lt.mp fun hj ↦ not_lt_of_ge hi (h.apply_pos_iff.mp hj)
      simp [posPart_def, max_eq_right hj]
    · simp [posPart_def, max_eq_right (le_of_not_ge hi)]
  have hn (i j : Fin 2) : (B i j)⁻ * (B j i)⁻ = 0 := by
    by_cases hi : 0 ≤ B i j
    · simp [negPart_def, max_eq_right (neg_nonpos.mpr hi)]
    · have hj : 0 ≤ B j i := (h.apply_pos_iff.mpr (lt_of_not_ge hi)).le
      simp [negPart_def, max_eq_right (neg_nonpos.mpr hj)]
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [matrixMutation_apply, h.apply_self, hp, hn]

/-- The companion is unchanged by either rank-two mutation. -/
theorem cartanCompanion_matrixMutation_rankTwo {B : Matrix (Fin 2) (Fin 2) ℤ}
    {s : Fin 2 → ℤ} (h : B.IsSkewSymmetrizer s) (k : Fin 2) :
    cartanCompanion (matrixMutation (Function.Embedding.refl _) B k) = cartanCompanion B := by
  rw [matrixMutation_rankTwo h, cartanCompanion_neg]

/-- Every finite rank-two mutation sequence reaches the initial matrix or its negative. -/
theorem foldl_matrixMutation_rankTwo {B : Matrix (Fin 2) (Fin 2) ℤ} {s : Fin 2 → ℤ}
    (h : B.IsSkewSymmetrizer s) (w : List (Fin 2)) :
    w.foldl (fun A k ↦ matrixMutation (Function.Embedding.refl _) A k) B = B ∨
      w.foldl (fun A k ↦ matrixMutation (Function.Embedding.refl _) A k) B = -B := by
  induction w generalizing B with
  | nil => exact Or.inl rfl
  | cons k w ih =>
    rw [List.foldl_cons, matrixMutation_rankTwo h]
    rcases ih h.neg with hh | hh
    · exact Or.inr hh
    · exact Or.inl (by simpa using hh)

/-- The complete mutation class of a skew-symmetrizable rank-two matrix is the pair containing
it and its negative. -/
theorem range_foldl_matrixMutation_rankTwo {B : Matrix (Fin 2) (Fin 2) ℤ}
    {s : Fin 2 → ℤ} (h : B.IsSkewSymmetrizer s) :
    Set.range (fun w : List (Fin 2) ↦
      w.foldl (fun A k ↦ matrixMutation (Function.Embedding.refl _) A k) B) = {B, -B} := by
  ext A
  constructor
  · rintro ⟨w, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using foldl_matrixMutation_rankTwo h w
  · intro hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact ⟨[], rfl⟩
    · exact ⟨[0], by simpa using matrixMutation_rankTwo h 0⟩

/-- Skew-symmetrizable rank-two matrices have finite mutation classes, independently of their
entry sizes. -/
theorem finite_range_foldl_matrixMutation_rankTwo {B : Matrix (Fin 2) (Fin 2) ℤ}
    {s : Fin 2 → ℤ} (h : B.IsSkewSymmetrizer s) :
    (Set.range (fun w : List (Fin 2) ↦
      w.foldl (fun A k ↦ matrixMutation (Function.Embedding.refl _) A k) B)).Finite := by
  rw [range_foldl_matrixMutation_rankTwo h]
  exact (Set.finite_singleton (-B)).insert B

/-- A uniform bound on off-diagonal entry products in rank two can be checked at the initial
matrix. The bound three is the two-finiteness criterion. -/
theorem forall_foldl_matrixMutation_abs_mul_le_iff {B : Matrix (Fin 2) (Fin 2) ℤ}
    {s : Fin 2 → ℤ} (h : B.IsSkewSymmetrizer s) (bound : ℤ) :
    (∀ w : List (Fin 2), ∀ i j : Fin 2, i ≠ j →
      |(w.foldl (fun A k ↦ matrixMutation (Function.Embedding.refl _) A k) B) i j *
        (w.foldl (fun A k ↦ matrixMutation (Function.Embedding.refl _) A k) B) j i| ≤ bound) ↔
      |B 0 1 * B 1 0| ≤ bound := by
  constructor
  · intro hall
    exact hall [] 0 1 (by decide)
  · intro hB w i j hij
    rcases foldl_matrixMutation_rankTwo h w with hw | hw <;> rw [hw] <;>
      fin_cases i <;> fin_cases j <;> simp_all [mul_comm]

end RankTwo

end TauCeti
