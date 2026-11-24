/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.RootSubgroup

/-!
# Examples of root subgroups of `SO_l^J`

For `l = 3`, the root map of the short root `ε₁` of the split form `q₃ = x₁x₃ + x₂²` is
`x_{ε₁}(a) = I + 2a E₁₂ - a E₂₃ - a² E₁₃`. Over a ring in which `2` is invertible, conjugating by
`δ = diag(2, 1, 1)` gives the matrix with rows `(1, a, -a²/2)`, `(0, 1, -a)`, `(0, 0, 1)`, which
has determinant one and preserves `J₃`, so it lies in `SO_3^J`. Its entry `-a²/2` is why the
comparison of the two models needs `2` inverted.

The root matrices of `TauCeti.AntidiagonalSpecialOrthogonal.rootMatrix` for `l = 4` and the pair
`(0, 1)`, the root `ε₁ - ε₂`, are `I + a(E₀₁ - E₂₃)`, and they lie in `SO_4^J`.
-/

public section

open Matrix

namespace TauCeti.AntidiagonalSpecialOrthogonal

variable {A : Type*} [CommRing A]

/-- `δ⁻¹ x_{ε₁}(a) δ` for `l = 3`, with `δ = diag(2, 1, 1)`, is the matrix with rows
`(1, a, -a²/2)`, `(0, 1, -a)`, `(0, 0, 1)`. -/
example [Invertible (2 : A)] (a : A) :
    diagonal ![⅟2, 1, 1] * !![1, 2 * a, -a ^ 2; 0, 1, -a; 0, 0, 1] * diagonal ![2, 1, 1] =
      !![1, a, -(a ^ 2 * ⅟2); 0, 1, -a; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, diagonal_apply, mul_assoc]
  ring

/-- The matrix `δ⁻¹ x_{ε₁}(a) δ` lies in `SO_3^J`: it has determinant one and preserves `J₃`. -/
example [Invertible (2 : A)] (a : A) :
    let g : Matrix (Fin 3) (Fin 3) A := !![1, a, -(a ^ 2 * ⅟2); 0, 1, -a; 0, 0, 1]
    g.det = 1 ∧ g * formMatrix A 3 * gᵀ = formMatrix A 3 := by
  have hJ : formMatrix A 3 = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [formMatrix_apply]
  refine ⟨by simp [det_fin_three], ?_⟩
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination (-a ^ 2) * mul_invOf_self (2 : A)

/-- The root index `(0, 1)` of `SO_4^J`, of the root `ε₁ - ε₂`. -/
def rootSubgroupIndexFour : RootSubgroupIndex 4 :=
  ⟨0, 1, by decide, by decide, by decide, by decide⟩

/-- For `l = 4`, the root matrix of `(0, 1)` is `I + a(E₀₁ - E₂₃)`. -/
example (a : A) :
    rootMatrix rootSubgroupIndexFour a = 1 + a • (single 0 1 1 - single 2 3 1) := by
  rw [rootMatrix_def, rootNilpotent_def]
  congr

/-- The root matrix of `(0, 1)` lies in `SO_4^J`. -/
example (a : A) :
    rootHom rootSubgroupIndexFour A (Multiplicative.ofAdd a) ∈ pointsSubgroup 4 A :=
  rootHom_mem_pointsSubgroup _ _

end TauCeti.AntidiagonalSpecialOrthogonal
