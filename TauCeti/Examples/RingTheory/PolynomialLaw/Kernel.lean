/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.PolynomialLaw.Kernel
import TauCeti.RingTheory.PolynomialLaw.Determinant.Triangular
import Mathlib.Algebra.Field.Rat

/-!
# Examples: the kernel of a polynomial law

* The identity law is faithful: `b ⊗ x + m = m` for all `S`, `b`, `m` forces `x = 0`.
* The zero law has kernel everything, so it is not faithful on a nonzero module.
* The law of the first projection `ℚ × ℚ → ℚ` has kernel the second factor, and the law it
  induces on the quotient is faithful.
* On upper-triangular `2 × 2` matrices the determinant is not faithful: the strictly
  upper-triangular matrix `!![0, 1; 0, 0]` lies in its kernel.
-/

open PolynomialLaw

-- The identity law on `ℚ²` is faithful.
example : (PolynomialLaw.id : (ℚ × ℚ) →ₚₗ[ℚ] (ℚ × ℚ)).IsFaithful :=
  isFaithful_id

-- The zero law has kernel everything ...
example : (0 : (ℚ × ℚ) →ₚₗ[ℚ] ℚ).ker = ⊤ :=
  ker_zero

-- ... so it is not faithful on a nonzero module.
example : ¬ (0 : ℚ →ₚₗ[ℚ] ℚ).IsFaithful := by
  rw [isFaithful_iff, ker_zero]
  exact top_ne_bot

-- The law of the first projection `ℚ × ℚ → ℚ` has kernel the second factor `0 × ℚ`.
example : (LinearMap.fst ℚ ℚ ℚ).toPolynomialLaw.ker = LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) :=
  LinearMap.ker_toPolynomialLaw _

example : ((0 : ℚ), (1 : ℚ)) ∈ (LinearMap.fst ℚ ℚ ℚ).toPolynomialLaw.ker := by
  simp

-- The first projection factors through `(ℚ × ℚ) ⧸ Ker`, and the induced law is faithful.
example : (LinearMap.fst ℚ ℚ ℚ).toPolynomialLaw =
    ((LinearMap.fst ℚ ℚ ℚ).toPolynomialLaw.liftQ _ le_rfl).comp
      (LinearMap.fst ℚ ℚ ℚ).toPolynomialLaw.ker.mkQ.toPolynomialLaw :=
  (liftQ_comp_mkQ le_rfl).symm

example : ((LinearMap.fst ℚ ℚ ℚ).toPolynomialLaw.liftQ _ le_rfl).IsFaithful :=
  isFaithful_liftQ_ker

-- On upper-triangular `2 × 2` matrices over `ℚ` the determinant is not faithful: the strictly
-- upper-triangular matrices lie in its kernel.
example : ¬ (TauCeti.Determinant.algHomDet
    (Matrix.blockTriangularSubalgebra ℚ ℚ (id : Fin 2 → Fin 2)).val).toLaw.IsFaithful := by
  have hN : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) ∈
      Matrix.blockTriangularSubalgebra ℚ ℚ (id : Fin 2 → Fin 2) := by
    rw [Matrix.mem_blockTriangularSubalgebra]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  rw [isFaithful_iff, ← ne_eq, Submodule.ne_bot_iff]
  refine ⟨⟨_, hN⟩, TauCeti.Determinant.mem_ker_algHomDet_of_isUpperTriangular _
    (fun x ↦ (Matrix.mem_blockTriangularSubalgebra ..).1 x.property) fun i ↦ ?_, fun h ↦ ?_⟩
  · fin_cases i <;> simp
  · simpa using congrArg (fun M : Matrix.blockTriangularSubalgebra ℚ ℚ (id : Fin 2 → Fin 2) ↦
      (M : Matrix (Fin 2) (Fin 2) ℚ) 0 1) h
