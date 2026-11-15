/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Morita.Matrix

/-!
# Additivity and free-module evaluation for `ModuleCat.toMatrixModCat`

Mathlib's `ModuleCat.toMatrixModCat R ι` sends a left `R`-module `M` to the left
`Matrix ι ι R`-module `ι → M` with `Matrix.Module.matrixModule` scalar action. This file supplies
its `Functor.Additive` instance and identifies its value on the finite free `R`-module `ι → R` with
the regular left `Matrix ι ι R`-module `Matrix ι ι R` via `Matrix.of`
(`TauCeti.matrixOfColumnModuleLinearEquiv`).
-/

public section

open CategoryTheory
open scoped Matrix.Module

universe u v w

instance (R : Type u) (ι : Type v) [Ring R] [Fintype ι] [DecidableEq ι] :
    (ModuleCat.toMatrixModCat.{u, v, w} R ι).Additive where
  map_add {_ _ _ _} := ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ funext fun _ ↦ rfl

@[simp] theorem ModuleCat.toMatrixModCat_obj_smul_apply {R : Type u} [Ring R] {ι : Type v}
    [Fintype ι] [DecidableEq ι] (M : ModuleCat.{w} R) (A : Matrix ι ι R)
    (v : (ModuleCat.toMatrixModCat R ι).obj M) (i : ι) :
    (A • v) i = ∑ j : ι, A i j • v j := (rfl)

namespace TauCeti

variable (R : Type u) [Ring R] (ι : Type v) [Fintype ι] [DecidableEq ι]

/-- Under `ModuleCat.toMatrixModCat`, the column module built from the finite free `R`-module
`ι → R` is isomorphic as a left `Matrix ι ι R`-module to the regular module `Matrix ι ι R`. -/
def matrixOfColumnModuleLinearEquiv :
    ((ModuleCat.toMatrixModCat R ι).obj (ModuleCat.of R (ι → R))) ≃ₗ[Matrix ι ι R]
      Matrix ι ι R where
  toFun v := Matrix.of fun i k ↦ v i k
  invFun M i k := M i k
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by ext; simp [Matrix.mul_apply]

@[simp] theorem matrixOfColumnModuleLinearEquiv_apply
    (v : (ModuleCat.toMatrixModCat R ι).obj (ModuleCat.of R (ι → R))) (i k : ι) :
    matrixOfColumnModuleLinearEquiv R ι v i k = v i k := (rfl)

@[simp] theorem matrixOfColumnModuleLinearEquiv_symm_apply (M : Matrix ι ι R) (i k : ι) :
    (matrixOfColumnModuleLinearEquiv R ι).symm M i k = M i k := (rfl)

end TauCeti
