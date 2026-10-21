/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic
public import TauCeti.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

/-!
# Base change of Scharlau transfer

In a pushout square of commutative algebras `K → L`, `E → F`, extend a functional
`s : L →ₗ[K] K` to `F →ₗ[E] E` using Mathlib's `IsBaseChange.toDual`. Transfer along this
functional commutes with scalar extension of quadratic forms under the canonical identification
`F ⊗[L] V ≃ₗ[E] E ⊗[K] V`, supplied by `Algebra.IsPushout.cancelBaseChange`.

Taking `F = E ⊗[K] L` recovers the tensor-product base change. The scalar-extended algebra need
not be a field. The result holds over commutative rings with two invertible, without finiteness,
separability, regularity, or nonzeroness of the functional. The comparison supplies base change
for transfer on regular-form classes and Witt rings when the pushout algebras are fields.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter VII, §1.
-/

public section

open scoped TensorProduct

namespace QuadraticMap

variable {K L E F V : Type*} [CommRing K] [CommRing L] [CommRing E] [CommRing F]
  [Algebra K L] [Algebra K E] [Algebra K F] [Algebra E F] [Algebra L F]
  [IsScalarTower K E F] [IsScalarTower K L F] [Algebra.IsPushout K E L F]
  [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
  [Invertible (2 : K)] [Invertible (2 : L)]

/-- Across a pushout square, transfer of an extended quadratic form pulls back to the extended
transfer under canonical cancellation of scalar extension. -/
theorem scharlauTransfer_baseChange_comp_cancelBaseChange_symm
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) :
    ((Q.baseChange F).scharlauTransfer
      ((Algebra.IsPushout.out (R := K) (S := E) (R' := L) (S' := F)).toDual s)).comp
        (Algebra.IsPushout.cancelBaseChange K E L F V).symm.toLinearMap =
      (Q.scharlauTransfer s).baseChange E := by
  apply baseChange_ext
  intro v
  simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, scharlauTransfer_apply,
    QuadraticForm.baseChange_tmul, map_one, mul_one, Algebra.smul_def]
  exact IsBaseChange.toDual_comp_apply _ s (Q v)

/-- Transfer commutes with extension of scalars in a pushout square. No regularity, finiteness,
separability or nonzeroness assumption on the functional is needed at the form level. -/
noncomputable def IsometryEquiv.scharlauTransferBaseChange
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) :
    ((Q.baseChange F).scharlauTransfer
      ((Algebra.IsPushout.out (R := K) (S := E) (R' := L) (S' := F)).toDual s)).IsometryEquiv
      ((Q.scharlauTransfer s).baseChange E) := by
  refine { toLinearEquiv := Algebra.IsPushout.cancelBaseChange K E L F V, map_app' := ?_ }
  intro x
  simpa only [QuadraticMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
      (DFunLike.congr_fun (Q.scharlauTransfer_baseChange_comp_cancelBaseChange_symm (F := F) s)
        (Algebra.IsPushout.cancelBaseChange K E L F V x)).symm

/-- The pushout transfer comparison uses the canonical cancellation equivalence. -/
@[simp]
theorem IsometryEquiv.scharlauTransferBaseChange_toLinearEquiv
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) :
    (IsometryEquiv.scharlauTransferBaseChange (E := E) (F := F) Q s).toLinearEquiv =
      Algebra.IsPushout.cancelBaseChange K E L F V := (rfl)

/-- The base-change comparison sends a scalar-extended pure tensor to the same pure tensor. -/
@[simp]
theorem IsometryEquiv.scharlauTransferBaseChange_tmul
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) (e : E) (v : V) :
    IsometryEquiv.scharlauTransferBaseChange (E := E) (F := F) Q s
      (algebraMap E F e ⊗ₜ[L] v) = e ⊗ₜ[K] v := by
  rw [← IsometryEquiv.coe_toLinearEquiv,
    IsometryEquiv.scharlauTransferBaseChange_toLinearEquiv,
    ← Algebra.IsPushout.cancelBaseChange_symm_tmul K E L F V e v,
    LinearEquiv.apply_symm_apply]

/-- The base-change comparison preserves a pure tensor with unit scalar. This rule also
applies when the input no longer displays the unit as an algebra-map image. -/
@[simp]
theorem IsometryEquiv.scharlauTransferBaseChange_one_tmul
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) (v : V) :
    IsometryEquiv.scharlauTransferBaseChange (E := E) (F := F) Q s
      (1 ⊗ₜ[L] v) = 1 ⊗ₜ[K] v := by
  simpa only [map_one] using
    IsometryEquiv.scharlauTransferBaseChange_tmul (E := E) (F := F) Q s 1 v

/-- The inverse base-change comparison extends the scalar through the pushout algebra. -/
@[simp]
theorem IsometryEquiv.scharlauTransferBaseChange_symm_tmul
    (Q : QuadraticForm L V) (s : L →ₗ[K] K) (e : E) (v : V) :
    (IsometryEquiv.scharlauTransferBaseChange (E := E) (F := F) Q s).symm (e ⊗ₜ[K] v) =
      algebraMap E F e ⊗ₜ[L] v := by
  rw [← IsometryEquiv.coe_toLinearEquiv, ← IsometryEquiv.coe_symm_toLinearEquiv,
    IsometryEquiv.scharlauTransferBaseChange_toLinearEquiv]
  exact Algebra.IsPushout.cancelBaseChange_symm_tmul K E L F V e v

end QuadraticMap
