/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.AdjointSquare.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-! # Surjectivity of the two adjoint-square contractions

Off-diagonal matrix units factor through the third index. The two remaining
diagonal coordinates use differences of diagonal units, since the trace is zero.
-/

public section
namespace TauCeti.AdjointSquare
open Matrix
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing
variable {K : Type*} [Field K]
local notation "𝔰" => LieAlgebra.SpecialLinear.sl (Fin 3)

open LieAlgebra.SpecialLinear (single val_single)

private def pair (i j k l : Fin 3) (h : i ≠ j) (h' : k ≠ l) : 𝔰 K ⊗[K] 𝔰 K :=
  single i j h 1 ⊗ₜ[K] single k l h' 1

private theorem diagonal_sum_zero (X : 𝔰 K) :
    X.val 0 0 + X.val 1 1 + X.val 2 2 = 0 := by
  have h : Matrix.trace X.val = 0 := X.property
  simpa only [Matrix.trace, Matrix.diag, Fin.sum_univ_succ, Fin.val_zero,
      Fin.val_succ, Fin.succ_zero_eq_one, show (1 : Fin 2).succ = 2 by decide,
      Finset.univ_eq_empty, Finset.sum_empty,
      add_zero, add_assoc] using h

/-- The alternating contraction maps onto the trace-zero carrier. -/
theorem alternating_surjective_of_tmul
    (f : (𝔰 K ⊗[K] 𝔰 K) →ₗ[K] 𝔰 K)
    (hf : ∀ X Y, (f (X ⊗ₜ[K] Y)).val = X.val * Y.val - Y.val * X.val) :
    Function.Surjective f := by
  intro X
  have htrace := diagonal_sum_zero X
  refine ⟨X.val 0 1 • pair 0 2 2 1 (by decide) (by decide) +
      X.val 0 2 • pair 0 1 1 2 (by decide) (by decide) +
      X.val 1 0 • pair 1 2 2 0 (by decide) (by decide) +
      X.val 1 2 • pair 1 0 0 2 (by decide) (by decide) +
      X.val 2 0 • pair 2 1 1 0 (by decide) (by decide) +
      X.val 2 1 • pair 2 0 0 1 (by decide) (by decide) +
      X.val 0 0 • pair 0 2 2 0 (by decide) (by decide) +
      X.val 1 1 • pair 1 2 2 1 (by decide) (by decide), ?_⟩
  apply Subtype.ext
  change (𝔰 K).toSubmodule.subtype _ = X.val
  simp only [map_add, map_smul, pair, Submodule.subtype_apply, hf, val_single]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.trace,
      Matrix.diag, Fin.sum_univ_succ, Matrix.single, Matrix.one_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul];
    first | (solve | ring) | linear_combination -htrace

/-- The symmetric contraction maps onto the trace-zero carrier. -/
theorem symmetric_surjective_of_tmul
    (f : (𝔰 K ⊗[K] 𝔰 K) →ₗ[K] 𝔰 K)
    (hf : ∀ X Y, (f (X ⊗ₜ[K] Y)).val = symmetricProductMatrix X.val Y.val) :
    Function.Surjective f := by
  intro X
  have htrace := diagonal_sum_zero X
  refine ⟨X.val 0 1 • pair 0 2 2 1 (by decide) (by decide) +
      X.val 0 2 • pair 0 1 1 2 (by decide) (by decide) +
      X.val 1 0 • pair 1 2 2 0 (by decide) (by decide) +
      X.val 1 2 • pair 1 0 0 2 (by decide) (by decide) +
      X.val 2 0 • pair 2 1 1 0 (by decide) (by decide) +
      X.val 2 1 • pair 2 0 0 1 (by decide) (by decide) +
      X.val 0 0 • (pair 0 1 1 0 (by decide) (by decide) - pair 2 1 1 2 (by decide) (by decide)) +
      X.val 1 1 • (pair 1 0 0 1 (by decide) (by decide) -
        pair 2 0 0 2 (by decide) (by decide)), ?_⟩
  apply Subtype.ext
  change (𝔰 K).toSubmodule.subtype _ = X.val
  simp only [map_add, map_sub, map_smul, pair, Submodule.subtype_apply, hf, val_single]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetricProductMatrix, Matrix.mul_apply, Matrix.trace,
      Matrix.diag, Fin.sum_univ_succ, Matrix.single, Matrix.one_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul];
    first | (solve | ring) | linear_combination -htrace

end TauCeti.AdjointSquare
