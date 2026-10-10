/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic
public import TauCeti.LinearAlgebra.TensorProduct.ScalarExtension
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

/-!
# Base change of Scharlau transfer

For `K`-algebras `L` and `E`, extend a functional `s : L →ₗ[K] K` to the `E`-linear
functional on `E ⊗[K] L` sending `e ⊗ l` to `e * algebraMap K E (s l)`. Mathlib's
`LinearMap.liftBaseChange` constructs this functional. Transfer along it commutes with scalar
extension of quadratic forms, under the canonical identification
`(E ⊗[K] L) ⊗[L] V ≃ₗ[E] E ⊗[K] V`.

The scalar-extended algebra need not be a field. The result holds over commutative rings with
two invertible, without finiteness, separability, regularity, or nonzeroness of the functional.
It supplies the form-level comparison needed to transport transfers along field extensions.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter VII, §1.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {K L E V : Type*} [CommRing K] [CommRing L] [CommRing E]
  [Algebra K L] [Algebra K E] [AddCommGroup V] [Module L V] [Module K V]
  [IsScalarTower K L V] [Invertible (2 : K)]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Pulling back the transfer of the scalar-extended form along inverse tensor cancellation is
scalar extension of the original transfer. The extended functional is `s` followed by the scalar
embedding and extended by Mathlib's `LinearMap.liftBaseChange`. -/
theorem _root_.QuadraticMap.scharlauTransfer_baseChange_comp_cancelBaseChangeRight_symm
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    ((Q.baseChange (E ⊗[K] L)).scharlauTransfer
      (((Algebra.linearMap K E).comp s).liftBaseChange E)).comp
        (TensorProduct.cancelBaseChangeRight K L E V).symm.toLinearMap =
      (Q.scharlauTransfer s).baseChange E := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  apply baseChange_ext
  intro v
  simp [QuadraticMap.comp_apply, Algebra.smul_def,
    Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

/-- **Base change of Scharlau transfer.** Extending a form and its transfer functional, then
transferring, is isometric to extending the transferred form. -/
def _root_.QuadraticMap.IsometryEquiv.scharlauTransferBaseChange
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    ((Q.baseChange (E ⊗[K] L)).scharlauTransfer
      (((Algebra.linearMap K E).comp s).liftBaseChange E)).IsometryEquiv
        ((Q.scharlauTransfer s).baseChange E) := by
  letI : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  refine { toLinearEquiv := TensorProduct.cancelBaseChangeRight K L E V, map_app' := ?_ }
  intro x
  simpa only [QuadraticMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
      (DFunLike.congr_fun (Q.scharlauTransfer_baseChange_comp_cancelBaseChangeRight_symm s)
        (TensorProduct.cancelBaseChangeRight K L E V x)).symm

/-- The linear equivalence underlying transfer base change is tensor cancellation. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.scharlauTransferBaseChange_toLinearEquiv
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    (QuadraticMap.IsometryEquiv.scharlauTransferBaseChange (E := E) Q s).toLinearEquiv =
      TensorProduct.cancelBaseChangeRight K L E V := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rfl

/-- The base-change comparison sends `(e ⊗ l) ⊗ v` to `e ⊗ (l • v)`. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.scharlauTransferBaseChange_tmul
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) (e : E) (l : L) (v : V) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    QuadraticMap.IsometryEquiv.scharlauTransferBaseChange (E := E) Q s
      ((e ⊗ₜ[K] l) ⊗ₜ[L] v) = e ⊗ₜ[K] (l • v) := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [← QuadraticMap.IsometryEquiv.coe_toLinearEquiv,
    QuadraticMap.IsometryEquiv.scharlauTransferBaseChange_toLinearEquiv]
  exact TensorProduct.cancelBaseChangeRight_tmul K L E V e l v

/-- The inverse comparison inserts the unit in the scalar-extended algebra. -/
@[simp]
theorem _root_.QuadraticMap.IsometryEquiv.scharlauTransferBaseChange_symm_tmul
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) (e : E) (v : V) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    (QuadraticMap.IsometryEquiv.scharlauTransferBaseChange (E := E) Q s).symm (e ⊗ₜ[K] v) =
      (e ⊗ₜ[K] (1 : L)) ⊗ₜ[L] v := by
  let : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [← QuadraticMap.IsometryEquiv.coe_toLinearEquiv,
    ← QuadraticMap.IsometryEquiv.coe_symm_toLinearEquiv,
    QuadraticMap.IsometryEquiv.scharlauTransferBaseChange_toLinearEquiv]
  exact TensorProduct.cancelBaseChangeRight_symm_tmul K L E V e v

end TauCeti
