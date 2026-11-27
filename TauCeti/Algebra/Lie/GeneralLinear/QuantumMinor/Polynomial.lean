/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Alternating

/-!
# A central indeterminate in quantum minors

Adding a commuting element to every diagonal entry of a matrix-unit family preserves the
matrix-unit relations. In particular the family `E + X I` over the polynomial ring (with
possibly noncommutative coefficients) still satisfies the relations. Its quantum minors
specialize at a scalar `t` to the original minors with spectral parameter `u + t`.

This is the central-indeterminate substitution used in the quantum Jacobi identity; see
L. Alpöge, `Formalism.FourierDecayAlt.Qr.QJacobi`.
-/

public section

namespace Matrix

open Polynomial

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A]

/-- The polynomial family obtained by adding the central indeterminate to the diagonal
satisfies the matrix-unit relations. -/
theorem HasMatrixUnitLieRelations.map_C_add_diagonal_X {E : Matrix ι ι A}
    (hE : E.HasMatrixUnitLieRelations) :
    (E.map C + diagonal (fun _ ↦ X)).HasMatrixUnitLieRelations :=
  (hE.map C).add_diagonal X fun i j ↦ (commute_X (C (E i j))).symm

/-- Evaluating the shifted polynomial minor at a scalar adds that scalar to the spectral
parameter. In particular evaluation at zero recovers the original quantum minor. -/
@[simp] theorem eval_quantumMinor_map_C_add_diagonal_X (E : Matrix ι ι A) (u t : K)
    {n : ℕ} (a b : Fin n → ι) :
    eval (algebraMap K A t) ((E.map C + diagonal (fun _ ↦ X)).quantumMinor u a b) =
      E.quantumMinor (u + t) a b := by
  let f : Polynomial A →ₐ[K] A :=
    eval₂AlgHom (AlgHom.id K A) (algebraMap K A t) fun x ↦ by
      rw [AlgHom.id_apply]
      exact Commute.symm (Algebra.commutes t x)
  have hEval (p : Polynomial A) : f p = p.eval (algebraMap K A t) := by
    dsimp only [f]
    rw [eval₂AlgHom_apply, AlgHom.id_toRingHom, eval₂_id]
  have hf : (E.map C + diagonal (fun _ ↦ X)).map f =
      E + diagonal (fun _ ↦ algebraMap K A t) := by
    ext i j
    by_cases h : i = j <;> simp [h, hEval]
  rw [← hEval, f.map_quantumMinor, hf, quantumMinor_add_diagonal_algebraMap]

end Matrix
