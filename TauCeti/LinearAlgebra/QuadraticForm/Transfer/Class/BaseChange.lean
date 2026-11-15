/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Class
public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.BaseChange

/-!
# Base change of Scharlau transfer on regular-form classes

For a pushout square of fields, scalar extension commutes with transfer on regular-form classes.
The extended functional is Mathlib's `IsBaseChange.toDual` applied to the pushout map. Its
nonzeroness follows from faithfulness of field extension, so no separability hypothesis is needed.

The pushout hypothesis says that the tensor product of the two extensions is itself the given
field. This result does not treat a split tensor algebra as a field.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter VII, §1.
-/

public section
noncomputable section

open QuadraticMap QuadraticForm
open scoped TensorProduct

namespace TauCeti

variable {K L E F : Type*} [Field K] [Field L] [Field E] [Field F]
  [Algebra K L] [Algebra K E] [Algebra K F] [Algebra E F] [Algebra L F]
  [IsScalarTower K E F] [IsScalarTower K L F] [Algebra.IsPushout K E L F]
  [FiniteDimensional K L]
  [Invertible (2 : K)] [Invertible (2 : E)] [iL : Invertible (2 : L)]

/-- **Base change of Scharlau transfer on regular-form classes.** Transfer along the canonical
extended functional commutes with scalar extension across a pushout square of fields.
The instance of invertibility in `L` is a parameter because scalar extension of `x` uses the
caller's instance. -/
@[simp]
theorem RegularFormClass.scharlauTransfer_baseChange
    (s : L →ₗ[K] K) (hs : s ≠ 0) (x : RegularFormClass L) :
    letI : FiniteDimensional E F :=
      Module.Finite.equiv (Algebra.IsPushout.equiv K E L F).toLinearEquiv
    RegularFormClass.scharlauTransfer
        ((Algebra.IsPushout.out (R := K) (S := E) (R' := L) (S' := F)).toDual s)
        (IsBaseChange.toDual_ne_zero _ s hs) (x.baseChange F) =
      (RegularFormClass.scharlauTransfer s hs x).baseChange E := by
  let _ : FiniteDimensional E F :=
    Module.Finite.equiv (Algebra.IsPushout.equiv K E L F).toLinearEquiv
  -- The existing form-class transfer equation uses the instance induced from `K`.
  have hL : iL = ((Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm) :=
    Subsingleton.elim _ _
  cases hL
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  let _ : Invertible (2 : F) :=
    (Invertible.map (algebraMap E F) 2).copy 2 (map_ofNat _ _).symm
  induction x using Quotient.inductionOn with
  | h p =>
    let _ : FiniteDimensional E (F ⊗[L] (Fin p.1 → L)) :=
      FiniteDimensional.trans E F _
    rw [← formClass_presentedForm p, ← QuadraticForm.formClass_baseChange,
      RegularFormClass.scharlauTransfer_formClass,
      RegularFormClass.scharlauTransfer_formClass, ← QuadraticForm.formClass_baseChange]
    exact (formClass_eq_iff _ _ _ _).mpr
      ⟨QuadraticMap.IsometryEquiv.scharlauTransferBaseChange (presentedForm p) s⟩

end TauCeti
