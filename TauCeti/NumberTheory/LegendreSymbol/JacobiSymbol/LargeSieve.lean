/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import TauCeti.Analysis.Matrix.L2OpNorm

/-!
# Reciprocity for the quadratic large sieve

The square of the operator norm of the Jacobi-symbol matrix is
`Finset.jacobiSymL2OpNormSq`. For odd index sets, reversing the symbol by quadratic
reciprocity uses the original coefficients on rows congruent to `1` modulo `4`.
On rows congruent to `3` modulo `4` it twists the coefficients by `(-1)^(n / 2)`,
negating precisely those in columns congruent to `3` modulo `4`. The fixed-coefficient estimate
`TauCeti.exists_sum_norm_sq_jacobiSym_le_two_mul_swap` and the norm comparison
`Finset.jacobiSymL2OpNormSq_le_two_mul_swap` are the two parts of Heath-Brown's Lemma 1.
The latter uses `Matrix.forall_sum_norm_sq_mulVec_le_iff_vecMul` for large-sieve duality.

## References

* D. R. Heath-Brown, *A mean value estimate for real character sums*,
  Acta Arithmetica 72 (1995), Lemma 1 and §3.
-/

public section

open scoped BigOperators Matrix.Norms.L2Operator

namespace Finset

/-- The squared `ℓ²` operator norm of the matrix with entry `jacobiSym n m` at row
`m ∈ S` and column `n ∈ T`. For odd squarefree dyadic ranges this is Heath-Brown's
`B(M,N)`. -/
noncomputable def jacobiSymL2OpNormSq (S T : Finset ℕ) : ℝ :=
  ‖Matrix.of (fun (m : S) (n : T) ↦ (jacobiSym (n : ℕ) m : ℂ))‖ ^ 2

/-- Express the Jacobi-symbol sum-of-squares constant as a squared matrix operator norm. -/
theorem jacobiSymL2OpNormSq_def (S T : Finset ℕ) :
    jacobiSymL2OpNormSq S T =
      ‖Matrix.of (fun (m : S) (n : T) ↦ (jacobiSym (n : ℕ) m : ℂ))‖ ^ 2 := (rfl)

/-- The squared Jacobi operator norm is nonnegative for all finite index sets. -/
@[simp, grind .]
theorem jacobiSymL2OpNormSq_nonneg (S T : Finset ℕ) : 0 ≤ jacobiSymL2OpNormSq S T := by
  rw [jacobiSymL2OpNormSq_def]
  positivity

/-- Restricting the row and column sets can only decrease the squared Jacobi operator norm.
In particular, this transfers bounds from full dyadic blocks to truncated blocks. -/
theorem jacobiSymL2OpNormSq_mono {S T S' T' : Finset ℕ} (hS : S ⊆ S') (hT : T ⊆ T') :
    S.jacobiSymL2OpNormSq T ≤ S'.jacobiSymL2OpNormSq T' := by
  rw [jacobiSymL2OpNormSq_def, jacobiSymL2OpNormSq_def]
  have hS' : (S : Set ℕ) ⊆ S' := coe_subset.mpr hS
  have hT' : (T : Set ℕ) ⊆ T' := coe_subset.mpr hT
  set A := Matrix.of (fun (m : S') (n : T') ↦ (jacobiSym (n : ℕ) m : ℂ)) with hA
  have hsub : A.submatrix (Set.inclusion hS') (Set.inclusion hT') =
      Matrix.of (fun (m : S) (n : T) ↦ (jacobiSym (n : ℕ) m : ℂ)) := by
    ext m n
    rw [hA]
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
  rw [← hsub]
  gcongr
  exact A.l2_opNorm_submatrix_le (Set.inclusion_injective hS') (Set.inclusion_injective hT')

-- The square-sum criteria stay out of the simp set because their right sides quantify over
-- all coefficient sequences.
/-- A nonnegative bound for the squared Jacobi operator norm is equivalent to the uniform
second-moment bound for arbitrary complex coefficients on the column set. -/
theorem jacobiSymL2OpNormSq_le_iff {S T : Finset ℕ} {C : ℝ} (hC : 0 ≤ C) :
    jacobiSymL2OpNormSq S T ≤ C ↔
      ∀ a : ℕ → ℂ, ∑ m ∈ S, ‖∑ n ∈ T, a n * (jacobiSym n m : ℂ)‖ ^ 2 ≤
        C * ∑ n ∈ T, ‖a n‖ ^ 2 := by
  have hrestr : Function.Surjective (fun a : ℕ → ℂ ↦ a ∘ (Subtype.val : T → ℕ)) :=
    Subtype.val_injective.surjective_comp_right
  rw [jacobiSymL2OpNormSq_def, Matrix.l2_opNorm_sq_le_iff hC, hrestr.forall]
  simp only [Matrix.mulVec_apply, dotProduct, Matrix.row_apply, Matrix.of_apply,
    Function.comp_apply, ← Finset.sum_coe_sort S, ← Finset.sum_coe_sort T, mul_comm (G := ℂ)]

/-- A nonnegative bound for the squared Jacobi operator norm also controls the dual
second moment, with the roles of the row and column sets exchanged. -/
theorem jacobiSymL2OpNormSq_le_iff_dual {S T : Finset ℕ} {C : ℝ} (hC : 0 ≤ C) :
    jacobiSymL2OpNormSq S T ≤ C ↔
      ∀ b : ℕ → ℂ, ∑ n ∈ T, ‖∑ m ∈ S, b m * (jacobiSym n m : ℂ)‖ ^ 2 ≤
        C * ∑ m ∈ S, ‖b m‖ ^ 2 := by
  have hrestr : Function.Surjective (fun b : ℕ → ℂ ↦ b ∘ (Subtype.val : S → ℕ)) :=
    Subtype.val_injective.surjective_comp_right
  rw [jacobiSymL2OpNormSq_def, Matrix.l2_opNorm_sq_le_iff hC,
    Matrix.forall_sum_norm_sq_mulVec_le_iff_vecMul _ hC, hrestr.forall]
  simp only [Matrix.vecMul_apply, dotProduct, Matrix.col_apply, Matrix.of_apply,
    Function.comp_apply, ← Finset.sum_coe_sort S, ← Finset.sum_coe_sort T]

/-- A matrix with no Jacobi-symbol columns has zero operator norm. -/
@[simp] theorem jacobiSymL2OpNormSq_empty_right (S : Finset ℕ) : S.jacobiSymL2OpNormSq ∅ = 0 := by
  rw [jacobiSymL2OpNormSq_def, Subsingleton.elim (Matrix.of _) 0]
  simp

/-- A matrix with no Jacobi-symbol rows has zero operator norm. -/
@[simp] theorem jacobiSymL2OpNormSq_empty_left (T : Finset ℕ) :
    (∅ : Finset ℕ).jacobiSymL2OpNormSq T = 0 := by
  rw [jacobiSymL2OpNormSq_def, Subsingleton.elim (Matrix.of _) 0]
  simp

end Finset

namespace TauCeti

/-- For a fixed odd denominator and odd summation indices, the squared norm of a Jacobi sum
is bounded by the two reversed sums with the original and sign-twisted coefficients.
This is the row-wise estimate in the proof of Heath-Brown's Lemma 1. -/
theorem norm_sum_mul_jacobiSym_sq_le_add_swap {T : Finset ℕ} {m : ℕ}
    (hm : Odd m) (hT : ∀ n ∈ T, Odd n) (a : ℕ → ℂ) :
    ‖∑ n ∈ T, a n * (jacobiSym n m : ℂ)‖ ^ 2 ≤
      ‖∑ n ∈ T, a n * (jacobiSym m n : ℂ)‖ ^ 2 +
        ‖∑ n ∈ T, a n * (-1 : ℂ) ^ (n / 2) * (jacobiSym m n : ℂ)‖ ^ 2 := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm) with hm₁ | hm₃
  · have he : (∑ n ∈ T, a n * (jacobiSym n m : ℂ)) = ∑ n ∈ T, a n * (jacobiSym m n : ℂ) :=
      Finset.sum_congr rfl fun n hn ↦
        congrArg (fun x : ℤ ↦ a n * (x : ℂ))
          (jacobiSym.quadratic_reciprocity_one_mod_four' (hT n hn) hm₁)
    rw [he]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · have he : (∑ n ∈ T, a n * (jacobiSym n m : ℂ)) =
        ∑ n ∈ T, a n * (-1 : ℂ) ^ (n / 2) * (jacobiSym m n : ℂ) := by
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      have hsign : jacobiSym n m = (-1 : ℤ) ^ (n / 2) * jacobiSym m n := by
        rw [jacobiSym.quadratic_reciprocity (hT n hn) hm, Nat.mul_comm, pow_mul,
          ZMod.neg_one_pow_div_two_of_three_mod_four hm₃]
      rw [hsign]
      push_cast
      rw [mul_assoc]
    rw [he]
    exact le_add_of_nonneg_left (sq_nonneg _)

/-- For odd index sets, reversing the Jacobi symbol costs at most a factor of two in the
second moment, after a choice of coefficients of the same magnitudes.
This is the fixed-coefficient part of Heath-Brown's Lemma 1. -/
theorem exists_sum_norm_sq_jacobiSym_le_two_mul_swap {S T : Finset ℕ}
    (hS : ∀ m ∈ S, Odd m) (hT : ∀ n ∈ T, Odd n) (a : ℕ → ℂ) :
    ∃ b : ℕ → ℂ, (∀ n, ‖b n‖ = ‖a n‖) ∧
      ∑ m ∈ S, ‖∑ n ∈ T, a n * (jacobiSym n m : ℂ)‖ ^ 2 ≤
        2 * ∑ m ∈ S, ‖∑ n ∈ T, b n * (jacobiSym m n : ℂ)‖ ^ 2 := by
  let b : ℕ → ℂ := fun n ↦ a n * (-1 : ℂ) ^ (n / 2)
  have hab (n : ℕ) : ‖b n‖ = ‖a n‖ := by
    simp only [b, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
  let F (c : ℕ → ℂ) (m : ℕ) := ∑ n ∈ T, c n * (jacobiSym m n : ℂ)
  have hsum := Finset.sum_le_sum fun m hm ↦ norm_sum_mul_jacobiSym_sq_le_add_swap (hS m hm) hT a
  rw [Finset.sum_add_distrib] at hsum
  rcases le_total (∑ m ∈ S, ‖F a m‖ ^ 2) (∑ m ∈ S, ‖F b m‖ ^ 2) with h | h
  · exact ⟨b, hab, by linarith⟩
  · exact ⟨a, fun _ ↦ rfl, by linarith⟩

end TauCeti

namespace Finset

/-- For finite sets of odd integers, the Jacobi-symbol norm squared is at most twice
the norm squared with the sets interchanged. This is Heath-Brown's Lemma 1 on
arbitrary finite sets, including the odd squarefree dyadic ranges. -/
theorem jacobiSymL2OpNormSq_le_two_mul_swap {S T : Finset ℕ}
    (hS : ∀ m ∈ S, Odd m) (hT : ∀ n ∈ T, Odd n) :
    jacobiSymL2OpNormSq S T ≤ 2 * jacobiSymL2OpNormSq T S := by
  have hnonneg := jacobiSymL2OpNormSq_nonneg T S
  have hdual := (jacobiSymL2OpNormSq_le_iff_dual (S := T) (T := S) hnonneg).mp le_rfl
  refine (jacobiSymL2OpNormSq_le_iff (by positivity)).mpr fun a ↦ ?_
  obtain ⟨b, hab, h⟩ := TauCeti.exists_sum_norm_sq_jacobiSym_le_two_mul_swap hS hT a
  have hb := hdual b
  simp only [hab] at hb
  exact h.trans (by rw [mul_assoc]; gcongr)

end Finset
