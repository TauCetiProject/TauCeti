/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.ShortRootSubgroup

/-!
# Examples of short root subgroups of `SO_l^J`

For `l = 3`, the middle index `1` and `i = 0`, the short root matrix
`TauCeti.AntidiagonalSpecialOrthogonal.shortRootMatrix` with `h = ½` is the matrix with rows
`(1, a, -a²/2)`, `(0, 1, -a)`, `(0, 0, 1)`: the conjugate `δ⁻¹ x_{ε₁}(a) δ` of the root map of the
split form `q₃ = x₁x₃ + x₂²` by `δ = diag(2, 1, 1)`.
-/

public section

open Matrix

namespace TauCeti.AntidiagonalSpecialOrthogonal

variable {A : Type*} [CommRing A]

/-- The short root index `(0, 1)` of `SO_3^J`, of the short root `ε₁`. -/
def shortRootIndexThree : ShortRootIndex 3 :=
  ⟨0, 1, by decide, by decide⟩

/-- For `l = 3`, the short root matrix with `h = ½` has rows `(1, a, -a²/2)`, `(0, 1, -a)`,
`(0, 0, 1)`. -/
example [Invertible (2 : A)] (a : A) :
    shortRootMatrix shortRootIndexThree ⅟2 a = !![1, a, -(⅟2 * a * a); 0, 1, -a; 0, 0, 1] := by
  rw [shortRootMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shortRootIndexThree]

end TauCeti.AntidiagonalSpecialOrthogonal
