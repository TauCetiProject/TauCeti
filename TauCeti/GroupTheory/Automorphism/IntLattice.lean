/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Equiv.IntLinear
public import TauCeti.GroupTheory.Automorphism.Outer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis

/-!
# The outer automorphism group of a free abelian group of finite rank

For a finite index type `ι`, the free abelian group `ℤ^ι`, written multiplicatively as
`Multiplicative (ι → ℤ)`, is commutative, so it has no nontrivial inner automorphisms and its outer
automorphism group is its automorphism group (`TauCeti.OuterAut.mulEquivOfIsMulCommutative`). Its
automorphisms are its `ℤ`-linear automorphisms
(`TauCeti.mulAutMultiplicativeEquivIntLinearEquiv`), that is, the invertible `ι × ι` integer
matrices, through the standard basis (`Module.Basis.toGL`). For `ι = Fin 2` this is
`OuterAut ℤ² ≅ GL₂(ℤ)`, the target of the Dehn–Nielsen–Baer theorem for the torus.

## Main definitions

* `TauCeti.outerAutIntPiEquiv`: `OuterAut (Multiplicative (ι → ℤ)) ≃* GL ι ℤ`.

## Main results

* `TauCeti.outerAutIntPiEquiv_mk_apply`: the `j`-th column of the matrix of the outer class of `φ`
  is the image under `φ` of the `j`-th standard basis vector.
* `TauCeti.outerAutIntPiEquiv_symm_apply`: the outer class attached to an invertible matrix `A` is
  the class of the automorphism `v ↦ A *ᵥ v`.
-/

public section

namespace TauCeti

open Multiplicative

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- **`OuterAut ℤ^ι ≅ GL_ι(ℤ)`**: the outer automorphisms of the abelian group `ℤ^ι` are its
automorphisms, the invertible `ι × ι` integer matrices. -/
noncomputable def outerAutIntPiEquiv :
    OuterAut (Multiplicative (ι → ℤ)) ≃* Matrix.GeneralLinearGroup ι ℤ :=
  OuterAut.mulEquivOfIsMulCommutative.trans <|
    (mulAutMultiplicativeEquivIntLinearEquiv _).trans (Pi.basisFun ℤ ι).toGL

variable {ι}

/-- The matrix of the outer class of `φ` has as its `j`-th column the image under `φ` of the
`j`-th standard basis vector. -/
@[simp]
theorem outerAutIntPiEquiv_mk_apply (φ : MulAut (Multiplicative (ι → ℤ))) (i j : ι) :
    (outerAutIntPiEquiv ι (φ : OuterAut _) : Matrix ι ι ℤ) i j =
      (φ (ofAdd (Pi.single j 1))).toAdd i := by
  simp [outerAutIntPiEquiv]

/-- The outer class attached to an invertible integer matrix `A` is the class of the automorphism
`v ↦ A *ᵥ v` of `ℤ^ι`. -/
theorem outerAutIntPiEquiv_symm_apply (A : Matrix.GeneralLinearGroup ι ℤ) :
    (outerAutIntPiEquiv ι).symm A =
      ((mulAutMultiplicativeEquivIntLinearEquiv _).symm
        (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv : OuterAut _) := by
  rw [MulEquiv.symm_apply_eq]
  ext i j
  simp

end TauCeti
