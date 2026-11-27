/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import TauCeti.Algebra.Ring.SquareZero
import TauCeti.AlgebraicGeometry.AbelianScheme.KugaSato.Projector
import TauCeti.AlgebraicGeometry.AbelianScheme.KugaSato.Selector

/-!
# Examples of relative-degree and corrected coefficient projectors

The relative-degree selector of an elliptic scheme uses the nodes `1, 2, 4` at `N = 2`.
For the nilpotent Jordan block `J` of size two, the correction of `J` is zero and the
correction of `1 + J` is the identity. The fifth power of `1 + J` is still nonidempotent.
-/

namespace TauCeti.Examples.KugaSato

open Polynomial TauCeti.KugaSato

/-- The degree-zero and degree-two denominators at `N = 2` have opposite signs. -/
example : (2 - (2 : ℚ) ^ 0, 2 - (2 : ℚ) ^ 2) = (1, -2) := by norm_num

/-- The elliptic degree-one polynomial takes values zero, one and zero on the three nodes. -/
example : ((relativeDegreeOnePolynomial ℚ 1 2).eval 1,
    (relativeDegreeOnePolynomial ℚ 1 2).eval 2,
    (relativeDegreeOnePolynomial ℚ 1 2).eval 4) = (0, 1, 0) := by
  have h₀ := eval_relativeDegreeOnePolynomial ℚ (g := 1) (j := 0) (N := 2) (by decide) (by decide)
  have h₁ := eval_relativeDegreeOnePolynomial ℚ (g := 1) (j := 1) (N := 2) (by decide) (by decide)
  have h₂ := eval_relativeDegreeOnePolynomial ℚ (g := 1) (j := 2) (N := 2) (by decide) (by decide)
  norm_num at h₀ h₁ h₂
  simp [h₀, h₁, h₂]

/-- For the empty power and identity Young operator, the coefficient projector is the identity. -/
example {V : Type*} [AddCommGroup V] [Module ℚ V] (T : Fin 0 → Module.End ℚ V)
    (hT : Pairwise (fun i j ↦ Commute (T i) (T j))) :
    coefficientProjector 5 1 (relativeDegreeSelector 1 2 T hT) = 1 := by
  simp [coefficientProjector_def, Module.End.one_eq_id]

/-- A filtration of length one needs no correction: the correction is the identity polynomial. -/
example : idempotentCorrection (R := ℚ) 1 = X := by
  simpa only [aeval_X_left_apply] using (aeval_idempotentCorrection (R := ℚ) (X : ℚ[X]) 1).trans
    (by rw [pow_one, pow_one, sub_sub_self])

/-- The correction distinguishes eigenvalues zero and one even with nontrivial generalized
eigenvectors. The unipotent block's fifth power still fails idempotence. -/
example :
    let J : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
    aeval J (idempotentCorrection (R := ℚ) 5) = 0 ∧
      aeval (1 + J) (idempotentCorrection (R := ℚ) 5) = 1 ∧
      ¬ IsIdempotentElem ((1 + J) ^ 5) := by
  intro J
  have hJ : J ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [J, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hpow (n : ℕ) : (1 + J) ^ n = 1 + (n : ℚ) • J := by
    simpa only [Nat.cast_smul_eq_nsmul] using TauCeti.one_add_pow_of_sq_eq_zero hJ n
  refine ⟨by simp [pow_eq_zero_of_le (by decide : 2 ≤ 5) hJ], ?_, ?_⟩
  · have h : (1 - (1 + J) ^ 5) ^ 2 = 0 := by
      rw [hpow, sub_add_cancel_left, neg_sq, smul_pow, hJ, smul_zero]
    simp [pow_eq_zero_of_le (by decide : 2 ≤ 5) h]
  · intro h
    have heq : (1 + J) ^ 10 = (1 + J) ^ 5 := by
      have hten : (10 : ℕ) = 5 + 5 := rfl
      rw [hten, pow_add]
      exact h.eq
    rw [hpow, hpow] at heq
    have hentry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ ↦ A 0 1) heq
    norm_num [J] at hentry

end TauCeti.Examples.KugaSato
