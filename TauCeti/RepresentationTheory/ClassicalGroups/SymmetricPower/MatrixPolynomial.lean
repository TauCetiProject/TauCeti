/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.MvPolynomial.HomogeneousAction
public import TauCeti.LinearAlgebra.SymmetricPower.Algebra
public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import TauCeti.RepresentationTheory.SymmetricPower
public import TauCeti.RepresentationTheory.Tensor.External
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Symmetric powers and forms on rectangular matrices

In the tensor product of the two standard representations, the tensor of the `i`-th and `j`-th
standard vectors corresponds to the variable `X (i, j)`. Multiplication identifies the `d`-th
symmetric power with the degree-`d` forms carrying the two-sided transpose action. This is the
coordinate identification used before applying Schur–Weyl duality to decompose the forms.
-/

public section

open Matrix MvPolynomial Module
open scoped TensorProduct Kronecker

namespace TauCeti

variable (R : Type) [CommSemiring R] (m n d : ℕ)

/-- The symmetric power of the external tensor product of the two standard representations is
the representation on forms in the matrix entries, via the tensor product of their bases. -/
noncomputable def symmetricPowerExternalTensorStdEquivMatrixForms :
    (((stdRep R m).externalTensor (stdRep R n)).symmetricPower d).Equiv
      (rectangularHomogeneousMatrixRep (m := Fin m) (n := Fin n) (R := R) d) := by
  let b := (Pi.basisFun R (Fin m)).tensorProduct (Pi.basisFun R (Fin n))
  refine .mk ((SymmetricPower.equivHomogeneous d).trans
    (SymmetricAlgebra.homogeneousSubmoduleEquivMvPolynomial R _ b d)) fun g ↦ ?_
  -- The product-basis calculation of `TensorProduct.toMatrix_map`, here over a semiring.
  have hmat : LinearMap.toMatrix b b ((stdRep R m).externalTensor (stdRep R n) g) =
      (g.1 : Matrix (Fin m) (Fin m) R) ⊗ₖ (g.2 : Matrix (Fin n) (Fin n) R) := by
    ext ⟨i, j⟩ ⟨a, c⟩
    simp [b, LinearMap.toMatrix_apply, Basis.tensorProduct_apply, mul_comm]
  refine SymmetricPower.ext fun v ↦ Subtype.ext ?_
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Representation.symmetricPower_apply_tprod, LinearEquiv.trans_apply,
    SymmetricAlgebra.coe_homogeneousSubmoduleEquivMvPolynomial_apply,
    SymmetricPower.coe_equivHomogeneous_apply, SymmetricPower.toSymmetricAlgebra_tprod,
    map_prod, _root_.SymmetricAlgebra.equivMvPolynomial_ι, Basis.constr_apply_fintype,
    smul_eq_C_mul, coe_rectangularHomogeneousMatrixRep_apply]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [polynomialAction_sum_C_mul_X, ← hmat]
  simp only [Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]

/-- The comparison sends a pure symmetric tensor of standard basis pairs to the product of the
corresponding matrix-entry variables. -/
@[simp]
theorem coe_symmetricPowerExternalTensorStdEquivMatrixForms_tprod
    (a : Fin d → Fin m) (b : Fin d → Fin n) :
    (symmetricPowerExternalTensorStdEquivMatrixForms R m n d
        (⨂ₛ[R] i, Pi.single (a i) 1 ⊗ₜ[R] Pi.single (b i) 1) :
          MvPolynomial (Fin m × Fin n) R) = ∏ i, X (a i, b i) := by
  simp only [symmetricPowerExternalTensorStdEquivMatrixForms, Representation.Equiv.mk_apply,
    LinearEquiv.trans_apply, SymmetricAlgebra.coe_homogeneousSubmoduleEquivMvPolynomial_apply,
    SymmetricPower.coe_equivHomogeneous_apply, SymmetricPower.toSymmetricAlgebra_tprod, map_prod,
    ← Pi.basisFun_apply, ← Basis.tensorProduct_apply,
    _root_.SymmetricAlgebra.equivMvPolynomial_ι_apply]

end TauCeti
