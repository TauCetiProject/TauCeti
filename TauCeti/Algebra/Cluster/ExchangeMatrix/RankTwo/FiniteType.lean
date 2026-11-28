/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.RankTwo.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic

/-!
# Finite-type Cartan companions in rank at most two

The Cartan companion of a skew-symmetrizable exchange matrix on at most two indices
is of finite type exactly when the absolute off-diagonal entry products are at most three.
This is the rank-at-most-two case of the matrix criterion in Fomin and Zelevinsky's
finite-type classification: some companion in the mutation class is of finite type
exactly when every matrix in that class satisfies the bound.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras II: Finite type classification*,
  Inventiones Mathematicae 154 (2003), §1, Theorem 1.8.
-/

public section

namespace Matrix.IsSkewSymmetrizer

open TauCeti

variable {K : Type*} [DecidableEq K] [Finite K]

/-- For a skew-symmetrizable matrix on at most two indices, the Cartan companion is of finite
type exactly when every off-diagonal entry product has absolute value at most three. -/
theorem isFiniteType_cartanCompanion_iff_of_card_le_two
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (hK : Nat.card K ≤ 2) :
    IsFiniteType B.cartanCompanion ↔ ∀ i j, i ≠ j → |B i j * B j i| ≤ 3 := by
  constructor
  · intro hB i j hij
    have hprod := hB.apply_mul_apply_mem_of_ne hij
    simp only [cartanCompanion_apply_mul_apply_of_ne _ hij,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hprod
    omega
  · intro hbound
    let A := B.cartanCompanion
    let d (i : K) : ℚ := s i
    have hd (i : K) : 0 < d i := by
      dsimp only [d]
      exact_mod_cast h.pos i
    have hsym (i j : K) : d i * (A i j : ℚ) = d j * (A j i : ℚ) := by
      dsimp only [d, A]
      exact_mod_cast h.mul_cartanCompanion_apply i j
    have hsmall (i j : K) (hij : i ≠ j) : (A i j : ℚ) * (A j i : ℚ) ≤ 3 := by
      have hp : A i j * A j i ≤ 3 := by
        simpa only [A, cartanCompanion_apply_mul_apply_of_ne _ hij] using hbound i j hij
      exact_mod_cast hp
    let M := Matrix.of fun i j ↦ d i * (A i j : ℚ)
    have hM : M.IsSymm := Matrix.IsSymm.ext fun i j ↦ by
      simpa only [M, Matrix.of_apply] using hsym j i
    have hdiag (i : K) : M i i = 2 * d i := by simp [M, A, mul_comm]
    have hdM (i : K) : 0 < M i i := by
      rw [hdiag]
      exact mul_pos (by norm_num) (hd i)
    refine isFiniteType_of B.cartanCompanion_apply_self
      (fun _ _ hij ↦ B.cartanCompanion_nonpos_of_ne hij)
      (hM.posDef_of_card_le_two hK hdM ?_)
    intro i j hij
    have hdet : M i i * M j j - M i j * M j i =
        d i * d j * (4 - (A i j : ℚ) * (A j i : ℚ)) := by
      rw [hdiag i, hdiag j]
      simp only [M, Matrix.of_apply]
      ring
    rw [hdet]
    exact mul_pos (mul_pos (hd i) (hd j)) (by linarith [hsmall i j hij])

/-- On at most two indices, the mutation class has a finite-type Cartan companion exactly
when every off-diagonal product in the class has absolute value at most three. -/
theorem exists_isFiniteType_cartanCompanion_matrixMutationWord_iff_of_card_le_two
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (hK : Nat.card K ≤ 2) :
    (∃ w, IsFiniteType (matrixMutationWord (Function.Embedding.refl K) B w).cartanCompanion) ↔
      ∀ w : List K, ∀ i j, i ≠ j →
        |matrixMutationWord (Function.Embedding.refl K) B w i j *
          matrixMutationWord (Function.Embedding.refl K) B w j i| ≤ 3 := by
  simp only [cartanCompanion_matrixMutationWord_of_card_le_two hK,
    exists_const, forall_abs_matrixMutationWord_mul_le_iff_of_card_le_two hK]
  exact h.isFiniteType_cartanCompanion_iff_of_card_le_two hK

end Matrix.IsSkewSymmetrizer
