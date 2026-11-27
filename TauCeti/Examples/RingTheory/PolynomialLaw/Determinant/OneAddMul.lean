/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.PolynomialLaw.Determinant.OneAddMul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Examples: `D(1 + r r') = D(1 + r' r)`

* For the determinant `det ∘ ρ` of a matrix representation, the identity is Mathlib's
  `Matrix.det_one_add_mul_comm` at `ρ r` and `ρ r'`.
* For the determinant of the identity representation of `M₂(ℤ)` and the matrix units
  `r = E₁₂`, `r' = E₂₁`, the products `r r' = E₁₁` and `r' r = E₂₂` differ, while both
  `1 + r r'` and `1 + r' r` have determinant `2`.
-/

open TauCeti Determinant Matrix

-- For `det ∘ ρ` the identity is `Matrix.det_one_add_mul_comm`.
example {A R n : Type*} [CommRing A] [Ring R] [Algebra A R] [Fintype n] [DecidableEq n]
    (ρ : R →ₐ[A] Matrix n n A) (r r' : R) :
    (1 + ρ r * ρ r').det = (1 + ρ r' * ρ r).det := by
  simpa using (algHomDet ρ).map_one_add_mul_comm r r'

-- The matrix units `E₁₂` and `E₂₁` of `M₂(ℤ)` do not commute ...
example : !![(0 : ℤ), 1; 0, 0] * !![0, 0; 1, 0] ≠ !![0, 0; 1, 0] * !![(0 : ℤ), 1; 0, 0] := by
  intro h
  simpa using congrFun (congrFun h 0) 0

-- ... but `det (1 + r r') = det (1 + r' r) = 2` for the identity representation.
example : algHomDet (AlgHom.id ℤ (Matrix (Fin 2) (Fin 2) ℤ))
      (1 + !![0, 1; 0, 0] * !![0, 0; 1, 0]) = 2 ∧
    algHomDet (AlgHom.id ℤ (Matrix (Fin 2) (Fin 2) ℤ))
      (1 + !![0, 0; 1, 0] * !![0, 1; 0, 0]) = 2 := by
  refine ⟨?_, by rw [← map_one_add_mul_comm, algHomDet_apply]; simp [det_fin_two, one_fin_two]⟩
  rw [algHomDet_apply]
  simp [det_fin_two, one_fin_two]
