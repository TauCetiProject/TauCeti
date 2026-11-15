/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Intertwiners and coefficient matrices

A linear map between finite free native comodules is colinear precisely when its scalar
matrix intertwines the coefficient matrices. This permits matrix arguments about
corepresentations to produce native comodule morphisms, without replacing coactions by
matrix-only objects. The source and target bases may have different index types.
-/

public section

open Module TauCeti TauCeti.Comodule
open scoped TensorProduct

namespace Module.Basis

variable {R A M N ι κ : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Coalgebra R A] [AddCommMonoid M] [Module R M] [Comodule R A M]
  [AddCommMonoid N] [Module R N] [Comodule R A N] [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- Colinearity is equivalent to the coefficient-matrix intertwining equation. The scalar
matrix of the linear map is extended to the coefficient algebra. -/
theorem map_coact_iff_coefficientMatrix (b : Basis ι R M) (c : Basis κ R N)
    (f : M →ₗ[R] N) :
    TensorProduct.map f LinearMap.id ∘ₗ coact (R := R) (C := A) =
        coact (R := R) (C := A) ∘ₗ f ↔
      coefficientMatrix (C := A) c * (LinearMap.toMatrix b c f).map (algebraMap R A) =
        (LinearMap.toMatrix b c f).map (algebraMap R A) * coefficientMatrix (C := A) b := by
  classical
  have hleft (i : κ) (j : ι) :
      TensorProduct.equivFinsuppOfBasisLeft c
          (TensorProduct.map f LinearMap.id (coact (R := R) (C := A) (b j))) i =
        ((LinearMap.toMatrix b c f).map (algebraMap R A) *
          coefficientMatrix (C := A) b) i j := by
    rw [coact_basis_eq_sum_coefficientMatrix b]
    simp [Matrix.mul_apply, LinearMap.toMatrix_apply, Algebra.smul_def]
  have hright (i : κ) (j : ι) :
      TensorProduct.equivFinsuppOfBasisLeft c (coact (R := R) (C := A) (f (b j))) i =
        (coefficientMatrix (C := A) c *
          (LinearMap.toMatrix b c f).map (algebraMap R A)) i j := by
    rw [← c.sum_repr (f (b j))]
    simp only [map_sum, map_smul, coact_basis_eq_sum_coefficientMatrix c]
    simp [Finset.sum_apply, Finsupp.single_apply, Matrix.mul_apply, LinearMap.toMatrix_apply,
      Algebra.smul_def, Algebra.commutes]
  constructor
  · intro h
    ext i j
    exact (hright i j).symm.trans
      ((congrArg (fun z => TensorProduct.equivFinsuppOfBasisLeft c z i)
        (LinearMap.congr_fun h (b j))).symm.trans (hleft i j))
  · intro h
    apply b.ext
    intro j
    apply (TensorProduct.equivFinsuppOfBasisLeft c).injective
    ext i
    exact (hleft i j).trans ((congrFun (congrFun h i) j).symm.trans (hright i j).symm)

end Module.Basis

namespace TauCeti.Comodule.Hom

variable {R A M N ι κ : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Coalgebra R A] [AddCommMonoid M] [Module R M] [Comodule R A M]
  [AddCommMonoid N] [Module R N] [Comodule R A N] [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- A native comodule morphism intertwines coefficient matrices in any finite bases. -/
theorem coefficientMatrix_mul_toMatrix (f : Hom R A M N) (b : Basis ι R M)
    (c : Basis κ R N) :
    coefficientMatrix (C := A) c * (LinearMap.toMatrix b c f.toLinearMap).map
        (algebraMap R A) =
      (LinearMap.toMatrix b c f.toLinearMap).map (algebraMap R A) *
        coefficientMatrix (C := A) b :=
  (b.map_coact_iff_coefficientMatrix c f.toLinearMap).mp f.map_coact

end TauCeti.Comodule.Hom
