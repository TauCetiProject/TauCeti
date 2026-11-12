/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Witt.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Class.BaseChange

/-!
# Base change of Scharlau transfer on Witt rings

For a pushout square of fields `K → L`, `E → F`, extending a Witt class from `L` to `F` and
transferring it to `E` agrees with transferring it to `K` and extending it to `E`. The functional
on `F` is the canonical scalar extension `Algebra.IsPushout.out.toDual` of the functional on `L`.
This is an equality of additive maps; Scharlau transfer is not generally multiplicative.

The square is required to be a field-valued pushout, so the tensor algebra is a field. No
separability is assumed. As in the underlying transfer API, the Witt rings of `L` and `F` use
the explicit instances `invertibleTwoOfBaseField K L` and `invertibleTwoOfBaseField E F`.
These choices are written in the statements because the Witt-ring carriers depend on them.
The instances on the two base fields `K` and `E` remain those supplied by the caller.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter VII, §1.
-/

public section
noncomputable section

namespace TauCeti

variable {K L E F : Type*} [Field K] [Field L] [Field E] [Field F]
  [Algebra K L] [Algebra K E] [Algebra K F] [Algebra E F] [Algebra L F]
  [IsScalarTower K E F] [IsScalarTower K L F] [Algebra.IsPushout K E L F]
  [FiniteDimensional K L]
  [Invertible (2 : K)] [Invertible (2 : E)]

/-- **Base change of Scharlau transfer on Witt rings.** The transfer square commutes at every
Witt class for the canonical extended functional. -/
@[simp]
theorem WittRing.scharlauTransfer_baseChange (s : L →ₗ[K] K) (hs : s ≠ 0) :
    letI : FiniteDimensional E F :=
      Module.Finite.equiv (Algebra.IsPushout.equiv K E L F).toLinearEquiv
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    letI : Invertible (2 : F) := invertibleTwoOfBaseField E F
    ∀ x : WittRing L,
    WittRing.scharlauTransfer
        ((Algebra.IsPushout.out (R := K) (S := E) (R' := L) (S' := F)).toDual s)
        (IsBaseChange.toDual_ne_zero _ s hs) (WittRing.baseChange (L := F) x) =
      WittRing.baseChange (L := E) (WittRing.scharlauTransfer s hs x) := by
  let _ : FiniteDimensional E F :=
    Module.Finite.equiv (Algebra.IsPushout.equiv K E L F).toLinearEquiv
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
  let _ : Invertible (2 : F) := invertibleTwoOfBaseField E F
  intro x
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  rw [WittRing.baseChange_wittClass, WittRing.scharlauTransfer_wittClass,
    WittRing.scharlauTransfer_wittClass, WittRing.baseChange_wittClass]
  exact congrArg wittClass
    (RegularFormClass.scharlauTransfer_baseChange (E := E) (F := F) s hs q)

/-- The commuting transfer square, as an equality of additive homomorphisms. -/
theorem WittRing.scharlauTransfer_comp_baseChange (s : L →ₗ[K] K) (hs : s ≠ 0) :
    letI : FiniteDimensional E F :=
      Module.Finite.equiv (Algebra.IsPushout.equiv K E L F).toLinearEquiv
    letI : Invertible (2 : L) := invertibleTwoOfBaseField K L
    letI : Invertible (2 : F) := invertibleTwoOfBaseField E F
    (WittRing.scharlauTransfer
        ((Algebra.IsPushout.out (R := K) (S := E) (R' := L) (S' := F)).toDual s)
        (IsBaseChange.toDual_ne_zero _ s hs)).comp
        (WittRing.baseChange (K := L) (L := F)).toAddMonoidHom =
      (WittRing.baseChange (K := K) (L := E)).toAddMonoidHom.comp
        (WittRing.scharlauTransfer s hs) := by
  let _ : FiniteDimensional E F :=
    Module.Finite.equiv (Algebra.IsPushout.equiv K E L F).toLinearEquiv
  let _ : Invertible (2 : L) := invertibleTwoOfBaseField K L
  let _ : Invertible (2 : F) := invertibleTwoOfBaseField E F
  ext x
  exact WittRing.scharlauTransfer_baseChange s hs x

end TauCeti
