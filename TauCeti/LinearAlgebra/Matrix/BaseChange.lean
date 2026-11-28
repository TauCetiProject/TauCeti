/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import TauCeti.LinearAlgebra.TensorProduct.Quotient
import TauCeti.Algebra.Algebra.Pi

/-!
# Scalar extension of matrix cokernels

Mapping the entries of a finite matrix along an algebra map presents the scalar extension
of its cokernel. No flatness is required: this is right exactness of tensor product, expressed
in the standard bases. The equivalence keeps track of the quotient generators, so it can be
used to descend module presentations to smaller coefficient rings.

The construction uses Mathlib's finite-product tensor equivalence and the cokernel
base-change equivalence in `TauCeti.LinearAlgebra.TensorProduct.Quotient`.

In the other direction, the `R`-rational solutions of a system `A x = 0` over `S`, that is the
vectors `x : n → R` with `A *ᵥ (algebraMap R S ∘ x) = 0`, form the kernel of the `R`-linear map
`A.mulVecLin.restrictScalars R ∘ₗ Pi.algebraMap n R S`
(`Matrix.mem_ker_mulVecLin_restrictScalars_comp_piAlgebraMap_iff`).

Finally, under `TensorProduct.piScalarRight` and basis coordinates `Module.Basis.equivFun`, the
scalar extension `(Matrix.mulVecLin M).baseChange L` agrees with any linear map `f` whose matrix
is `M.map (algebraMap E L)` (`TensorProduct.piScalarRight_equivFun_intertwining`), which is used to
descend intertwining maps between framed representations.
-/

public section

open TensorProduct

namespace Matrix

section Semiring

variable {R S m n : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The standard-basis identifications intertwine scalar extension of a matrix map with
mapping its entries along the algebra map. -/
theorem piScalarRight_comp_baseChange_mulVecLin (A : Matrix m n R) :
    (piScalarRight R S S m).toLinearMap.comp (A.mulVecLin.baseChange S) =
      (A.map (algebraMap R S)).mulVecLin.comp (piScalarRight R S S n).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro b x
  ext i
  simp [piScalarRight_apply, piScalarRightHom_tmul, mulVec, dotProduct,
    Algebra.smul_def, Finset.sum_mul, mul_assoc]

/-- Pointwise form of `Matrix.piScalarRight_comp_baseChange_mulVecLin`. -/
theorem piScalarRight_baseChange_mulVecLin (A : Matrix m n R) (x : S ⊗[R] (n → R)) :
    piScalarRight R S S m (A.mulVecLin.baseChange S x) =
      (A.map (algebraMap R S)).mulVec (piScalarRight R S S n x) := by
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, mulVecLin_apply] using
    LinearMap.congr_fun (piScalarRight_comp_baseChange_mulVecLin (S := S) A) x

end Semiring

section RationalSolutions

variable {R S m n : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [Fintype n]

/-- A vector `x : n → R` lies in the kernel of
`A.mulVecLin.restrictScalars R ∘ₗ Pi.algebraMap n R S` exactly when its coordinatewise image in
`n → S` solves `A x = 0`. -/
theorem mem_ker_mulVecLin_restrictScalars_comp_piAlgebraMap_iff (A : Matrix m n S) (x : n → R) :
    x ∈ LinearMap.ker (A.mulVecLin.restrictScalars R ∘ₗ Pi.algebraMap n R S) ↔
      A *ᵥ (fun i ↦ algebraMap R S (x i)) = 0 := by
  have hx : Pi.algebraMap n R S x = fun i ↦ algebraMap R S (x i) :=
    funext (TauCeti.piAlgebraMap_apply S x)
  rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply, mulVecLin_apply,
    hx]

end RationalSolutions

variable {R S m n : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Scalar extension of a finite matrix cokernel is the cokernel of the matrix obtained by
mapping its entries. This holds for arbitrary commutative coefficient algebras. -/
noncomputable def cokernelBaseChangeEquiv (A : Matrix m n R) :
    S ⊗[R] ((m → R) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[S]
      (m → S) ⧸ LinearMap.range (A.map (algebraMap R S)).mulVecLin :=
  A.mulVecLin.cokernelBaseChangeEquiv ≪≫ₗ
    Submodule.Quotient.equiv _ _ (piScalarRight R S S m) (by
      rw [← LinearMap.range_comp, piScalarRight_comp_baseChange_mulVecLin,
        LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)])

/-- On quotient representatives the cokernel comparison maps each coordinate along the
algebra map and multiplies by the tensor's scalar. -/
@[simp]
theorem cokernelBaseChangeEquiv_tmul (A : Matrix m n R) (s : S) (x : m → R) :
    A.cokernelBaseChangeEquiv (S := S) (s ⊗ₜ[R] Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (fun i ↦ algebraMap R S (x i) * s) := by
  simp [cokernelBaseChangeEquiv, Submodule.Quotient.equiv_apply,
    piScalarRight_apply, piScalarRightHom_tmul, Algebra.smul_def]

/-- The inverse comparison carries a scalar multiple of a standard quotient generator to
the corresponding pure tensor. -/
@[simp]
theorem cokernelBaseChangeEquiv_symm_mk_single (A : Matrix m n R) (i : m) (s : S) :
    (A.cokernelBaseChangeEquiv (S := S)).symm (Submodule.Quotient.mk (Pi.single i s)) =
      s ⊗ₜ[R] Submodule.Quotient.mk (Pi.single i 1) := by
  classical
  apply (A.cokernelBaseChangeEquiv (S := S)).injective
  rw [LinearEquiv.apply_symm_apply, cokernelBaseChangeEquiv_tmul]
  congr 1
  ext j
  simp [Pi.single_apply]

end Matrix

namespace TensorProduct

/-- Under `TensorProduct.piScalarRight` and basis coordinates `Module.Basis.equivFun`, the
scalar extension of `Matrix.mulVecLin M` intertwines with a linear map `f` whose matrix is
`M.map (algebraMap E L)`. -/
theorem piScalarRight_equivFun_intertwining {E L V W ιV ιW : Type*}
    [CommSemiring E] [CommSemiring L] [Algebra E L]
    [AddCommMonoid V] [Module L V] [AddCommMonoid W] [Module L W]
    [Fintype ιV] [DecidableEq ιV] [Fintype ιW] [DecidableEq ιW]
    (bV : Module.Basis ιV L V) (bW : Module.Basis ιW L W)
    (f : V →ₗ[L] W) (M : Matrix ιW ιV E)
    (hM : M.map (algebraMap E L) = LinearMap.toMatrix bV bW f)
    (x : L ⊗[E] (ιV → E)) :
    bW.equivFun.symm (TensorProduct.piScalarRight E L L ιW ((Matrix.mulVecLin M).baseChange L x)) =
      f (bV.equivFun.symm (TensorProduct.piScalarRight E L L ιV x)) := by
  apply bW.equivFun.injective
  rw [LinearEquiv.apply_symm_apply, Matrix.piScalarRight_baseChange_mulVecLin, hM]
  have hrepr : (bV.repr (bV.equivFun.symm (TensorProduct.piScalarRight E L L ιV x)) : ιV → L) =
      TensorProduct.piScalarRight E L L ιV x := by
    ext i
    simp only [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [← hrepr, LinearMap.toMatrix_mulVec_repr bV bW f, hrepr]
  exact (Module.Basis.equivFun_apply bW _).symm

end TensorProduct
