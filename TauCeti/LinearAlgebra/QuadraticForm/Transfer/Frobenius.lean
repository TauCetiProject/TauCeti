/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic

/-!
# Frobenius reciprocity for Scharlau transfer

Scharlau transfer satisfies the projection formula: transferring the tensor product of a
quadratic form over an extension with a scalar-extended form from the base is isometric to the
tensor product of the transferred form with the original base form.  The isometry is the
canonical cancellation

`V ⊗[L] (L ⊗[K] W) ≃ V ⊗[K] W`.

This is the form-level Frobenius reciprocity needed to make transfer on Witt groups linear over
the Witt ring of the base field.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter VII, §1.
-/

public section

open scoped TensorProduct

namespace QuadraticMap

variable {K L V W : Type*} [CommRing K] [CommRing L] [Algebra K L]
  [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
  [AddCommGroup W] [Module K W]

section FrobeniusReciprocity

variable [Invertible (2 : K)]

/-- Pulling the tensor product of the transferred form and a base form back along the canonical
tensor cancellation gives the transfer of the tensor product with its scalar extension. -/
theorem scharlauTransfer_tmul_baseChange_comp_cancelBaseChange
    (Q : QuadraticForm L V) (R : QuadraticForm K W) (s : L →ₗ[K] K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    ((Q.scharlauTransfer s).tmul R).comp
          (LinearEquiv.toLinearMap
            ((TensorProduct.AlgebraTensorModule.cancelBaseChange K L L V W).restrictScalars K)) =
        (Q.tmul (R.baseChange L)).scharlauTransfer s := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  refine (associated_rightInverse K).injective ?_
  rw [associated_comp, QuadraticForm.associated_tmul]
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hx hx'
  | tmul v aw =>
      induction aw using TensorProduct.inductionOn with
      | add aw aw' haw haw' =>
          rw [TensorProduct.tmul_add]
          simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) haw haw'
      | tmul a w =>
          induction y using TensorProduct.inductionOn with
          | add y y' hy hy' =>
              simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hy hy'
          | tmul v' aw' =>
              induction aw' using TensorProduct.inductionOn with
              | add aw' aw'' haw' haw'' =>
                  rw [TensorProduct.tmul_add]
                  simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) haw' haw''
              | tmul a' w' =>
                  rw [LinearMap.compl₁₂_apply]
                  -- Expose the restricted scalar equivalence so its pure-tensor cancellation
                  -- equation can rewrite both arguments of the bilinear form.
                  change
                    ((LinearMap.BilinForm.tmul (associated (Q.scharlauTransfer s)) (associated R))
                        (TensorProduct.AlgebraTensorModule.cancelBaseChange K L L V W
                          (v ⊗ₜ[L] (a ⊗ₜ[K] w))))
                      (TensorProduct.AlgebraTensorModule.cancelBaseChange K L L V W
                        (v' ⊗ₜ[L] (a' ⊗ₜ[K] w'))) = _
                  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
                    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
                  rw [associated_scharlauTransfer (Q.tmul (R.baseChange L)) s
                    (v ⊗ₜ[L] (a ⊗ₜ[K] w)) (v' ⊗ₜ[L] (a' ⊗ₜ[K] w')),
                    QuadraticForm.associated_tmul]
                  simp [LinearMap.BilinForm.tmul, LinearMap.BilinForm.tensorDistrib,
                    QuadraticForm.associated_baseChange, associated_scharlauTransfer]
                  ring_nf

/-- **Frobenius reciprocity for Scharlau transfer.**  Transferring `Q` tensored with the
scalar extension of `R` is isometric to the tensor product of the transfer of `Q` with `R`.
The underlying isometry is the canonical cancellation
`V ⊗[L] (L ⊗[K] W) ≃ V ⊗[K] W`. -/
def IsometryEquiv.scharlauTransferTmulBaseChange
    (Q : QuadraticForm L V) (R : QuadraticForm K W) (s : L →ₗ[K] K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    ((Q.tmul (R.baseChange L)).scharlauTransfer s).IsometryEquiv
      ((Q.scharlauTransfer s).tmul R) := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  exact
    { toLinearEquiv :=
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K L L V W).restrictScalars K
      map_app' x := DFunLike.congr_fun
        (scharlauTransfer_tmul_baseChange_comp_cancelBaseChange Q R s) x }

/-- The linear equivalence underlying Frobenius reciprocity is tensor cancellation. -/
@[simp]
theorem IsometryEquiv.scharlauTransferTmulBaseChange_toLinearEquiv
    (Q : QuadraticForm L V) (R : QuadraticForm K W) (s : L →ₗ[K] K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    (IsometryEquiv.scharlauTransferTmulBaseChange Q R s).toLinearEquiv =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K L L V W).restrictScalars K := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rfl

/-- The Frobenius-reciprocity isometry is the canonical cancellation of scalar extension. -/
@[simp]
theorem IsometryEquiv.scharlauTransferTmulBaseChange_apply
    (Q : QuadraticForm L V) (R : QuadraticForm K W) (s : L →ₗ[K] K)
    (x : V ⊗[L] (L ⊗[K] W)) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    IsometryEquiv.scharlauTransferTmulBaseChange Q R s x =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K L L V W).restrictScalars K x := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  exact LinearEquiv.congr_fun
    (IsometryEquiv.scharlauTransferTmulBaseChange_toLinearEquiv Q R s) x

/-- The inverse Frobenius-reciprocity isometry inserts the unit in the scalar-extension
factor on pure tensors. -/
@[simp]
theorem IsometryEquiv.scharlauTransferTmulBaseChange_symm_apply
    (Q : QuadraticForm L V) (R : QuadraticForm K W) (s : L →ₗ[K] K) (v : V) (w : W) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    (IsometryEquiv.scharlauTransferTmulBaseChange Q R s).symm (v ⊗ₜ[K] w) =
      v ⊗ₜ[L] (1 ⊗ₜ[K] w) := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  -- `IsometryEquiv.symm` is definitionally the inverse of its underlying linear
  -- equivalence; expose the restricted cancellation equivalence so its inverse lemma applies.
  change
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange K L L V W).restrictScalars K).symm
        (v ⊗ₜ[K] w) = _
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul K L L v w

end FrobeniusReciprocity

end QuadraticMap
