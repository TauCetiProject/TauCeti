/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.LatticeNorm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Examples of determinant-lattice norms

This file computes `Submodule.detNorm` on small lattices in `ℚ³` and `ℚ²`, where the ambient
algebra is a split étale `ℚ`-algebra rather than a number field.

* `detNorm_two_int_int`: relative to the standard basis of `ℚ³`, the lattice `2ℤ × ℤ × ℤ` has
  norm `2ℤ`.
* `detNorm_smul_two_int_int`: multiplying that lattice by the unit `(3, 1, 1)` of `ℚ³` gives norm
  `6ℤ`.
* `detNorm_int_int_oneOne_twoZero`: relative to the basis `((1, 1), (2, 0))` of `ℚ²`, the lattice
  `ℤ²` has norm `(1/2)ℤ`. The lattice `ℤ²` is stable under the order `ℤ + 2ℤ²` with this basis, but
  is not an invertible ideal of it.
-/

public section

open Module Submodule Set
open scoped Pointwise

namespace TauCeti.DetNormExamples

/-- The generators `(2, 0, 0)`, `(0, 1, 0)`, `(0, 0, 1)` of the lattice `2ℤ × ℤ × ℤ` in `ℚ³`. -/
def twoIntIntGen : Fin 3 → Fin 3 → ℚ := ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]]

/-- Relative to the standard basis of `ℚ³`, the lattice `2ℤ × ℤ × ℤ` has norm `2ℤ`. -/
theorem detNorm_two_int_int :
    (span ℤ (range twoIntIntGen)).detNorm (Pi.basisFun ℚ (Fin 3)) = ℤ ∙ (2 : ℚ) := by
  rw [detNorm_span_range, Pi.basisFun_det_apply]
  norm_num [twoIntIntGen, Matrix.det_fin_three]

/-- The algebra norm of `(3, 1, 1)` in `ℚ³` is `3`. -/
theorem norm_three_one_one : Algebra.norm ℚ (![3, 1, 1] : Fin 3 → ℚ) = 3 := by
  rw [Algebra.norm_eq_matrix_det (Pi.basisFun ℚ (Fin 3))]
  have : Algebra.leftMulMatrix (Pi.basisFun ℚ (Fin 3)) (![3, 1, 1] : Fin 3 → ℚ) =
      Matrix.diagonal ![3, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [this, Matrix.det_diagonal, Fin.prod_univ_three]
  norm_num

/-- Multiplying `2ℤ × ℤ × ℤ` by the unit `(3, 1, 1)` of `ℚ³` gives a lattice of norm `6ℤ`. -/
theorem detNorm_smul_two_int_int :
    ((![3, 1, 1] : Fin 3 → ℚ) • span ℤ (range twoIntIntGen)).detNorm (Pi.basisFun ℚ (Fin 3)) =
      ℤ ∙ (6 : ℚ) := by
  rw [detNorm_smul, detNorm_two_int_int, norm_three_one_one, smul_span, smul_set_singleton]
  norm_num

/-- The vectors `(1, 1)` and `(2, 0)` form a basis of `ℚ²`. -/
theorem isBasis_oneOne_twoZero :
    LinearIndependent ℚ ![![(1 : ℚ), 1], ![2, 0]] ∧
      span ℚ (range ![![(1 : ℚ), 1], ![2, 0]]) = ⊤ := by
  refine (Pi.basisFun ℚ (Fin 2)).is_basis_iff_det.2 ?_
  rw [Pi.basisFun_det_apply]
  norm_num [Matrix.det_fin_two]

/-- The basis `((1, 1), (2, 0))` of `ℚ²`. -/
noncomputable def oneOneTwoZero : Basis (Fin 2) ℚ (Fin 2 → ℚ) :=
  Basis.mk isBasis_oneOne_twoZero.1 isBasis_oneOne_twoZero.2.ge

/-- Relative to the basis `((1, 1), (2, 0))` of `ℚ²`, the lattice `ℤ²` has norm `(1/2)ℤ`. -/
theorem detNorm_int_int_oneOne_twoZero :
    (span ℤ (range (Pi.basisFun ℚ (Fin 2)))).detNorm oneOneTwoZero = ℤ ∙ (1 / 2 : ℚ) := by
  rw [detNorm_eq_inv_smul_detNorm _ (Pi.basisFun ℚ (Fin 2)), detNorm_span_range_self,
    one_eq_span, smul_span, smul_set_singleton, oneOneTwoZero, Basis.coe_mk,
    Pi.basisFun_det_apply]
  -- The determinant is `-2`, so the generator `(-2)⁻¹` differs from `1 / 2` by the unit `-1`.
  refine span_singleton_eq_span_singleton.2 ⟨-1, ?_⟩
  norm_num [Matrix.det_fin_two]

end TauCeti.DetNormExamples
