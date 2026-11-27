/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.Tactic.Module

/-!
# Automorphisms of a rank-two module with a given matrix

For a basis `e` of a module `M` indexed by `Fin 2`, Mathlib's
`Matrix.SpecialLinearGroup.toLin_equiv e` sends a matrix `γ` of determinant one to the automorphism
of `M` with matrix `γ` in `e`. This file records its action in coordinates: the vector with
coordinates `(x, y)` goes to the vector with coordinates `γ (x, y)`.

## Main results

* `Matrix.SpecialLinearGroup.toLin_equiv_apply_fin_two`: the coordinates of the image of
  `x • e 0 + y • e 1`.
-/

public section

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The automorphism of `M` with matrix `γ` in a basis `e` indexed by `Fin 2` sends the vector with
coordinates `(x, y)` to the vector with coordinates `γ (x, y)`. -/
theorem toLin_equiv_apply_fin_two (e : Module.Basis (Fin 2) R M) (γ : SL(2, R)) (x y : R) :
    ((toLin_equiv e γ : M ≃ₗ[R] M) : M → M) (x • e 0 + y • e 1) =
      (γ 0 0 * x + γ 0 1 * y) • e 0 + (γ 1 0 * x + γ 1 1 * y) • e 1 := by
  have h (i : Fin 2) : ((toLin_equiv e γ : M ≃ₗ[R] M) : M → M) (e i) =
      γ 0 i • e 0 + γ 1 i • e 1 := by
    rw [← LinearEquiv.coe_coe, toLin_equiv.toLinearMap_eq, Matrix.toLin_self, Fin.sum_univ_two]
  rw [map_add, map_smul, map_smul, h, h]
  module

end Matrix.SpecialLinearGroup
