/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Class
public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Frobenius
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Ring

/-!
# Frobenius reciprocity for Scharlau transfer of isometry classes

Form-level Frobenius reciprocity descends to isometry classes: transfer of a class over the
extension multiplied by a scalar-extended class from the base field is the transfer multiplied by
the original base class. Applying this to the hyperbolic class, which is its own scalar extension,
computes the transfer of a hyperbolic plane as `[L : K]` hyperbolic planes over the base field.

Both results are statements about regular-form classes only. They are the input for the descent of
transfer to Witt rings, where the second one shows that the hyperbolic ideal is preserved.

## Main results

* `TauCeti.RegularFormClass.scharlauTransfer_mul_baseChange`: Frobenius reciprocity on regular
  form classes.
* `TauCeti.RegularFormClass.scharlauTransfer_hyperbolicClass`: transfer of a hyperbolic plane is
  a sum of `[L : K]` hyperbolic planes.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter VII, §1.
-/

public section
noncomputable section

open scoped TensorProduct
open QuadraticMap QuadraticForm

namespace TauCeti

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Invertible (2 : K)]

/-- **Frobenius reciprocity on regular-form classes.** Transfer of a class over `L` multiplied
by a scalar-extended class from `K` is the transfer multiplied by the original base class. -/
@[simp]
theorem RegularFormClass.scharlauTransfer_mul_baseChange (s : L →ₗ[K] K) (hs : s ≠ 0)
    (x : RegularFormClass L) (y : RegularFormClass K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.scharlauTransfer s hs (x * y.baseChange L) =
      RegularFormClass.scharlauTransfer s hs x * y := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      let _ : FiniteDimensional K
          ((Fin p.1 → L) ⊗[L] (L ⊗[K] (Fin q.1 → K))) :=
        FiniteDimensional.trans K L _
      rw [← formClass_presentedForm p, ← formClass_presentedForm q,
        ← QuadraticForm.formClass_baseChange, ← formClass_tmul,
        RegularFormClass.scharlauTransfer_formClass,
        RegularFormClass.scharlauTransfer_formClass, ← formClass_tmul]
      exact (formClass_eq_iff _ _ _ _).mpr
        ⟨QuadraticMap.IsometryEquiv.scharlauTransferTmulBaseChange
          (presentedForm p) (presentedForm q) s⟩

/-- Transfer of a hyperbolic plane over `L` is a sum of `[L : K]` hyperbolic planes over `K`.
This is the hyperbolic-preservation statement that makes transfer descend to Witt rings. -/
@[simp]
theorem RegularFormClass.scharlauTransfer_hyperbolicClass (s : L →ₗ[K] K) (hs : s ≠ 0) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.scharlauTransfer s hs (hyperbolicClass L) =
      Module.finrank K L • hyperbolicClass K := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  calc
    RegularFormClass.scharlauTransfer s hs (hyperbolicClass L) =
        RegularFormClass.scharlauTransfer s hs
          (1 * RegularFormClass.baseChange L (hyperbolicClass K)) := by
            rw [one_mul, RegularFormClass.baseChange_hyperbolicClass]
    _ = RegularFormClass.scharlauTransfer s hs 1 * hyperbolicClass K :=
      RegularFormClass.scharlauTransfer_mul_baseChange s hs 1 (hyperbolicClass K)
    _ = RegularFormClass.rank (RegularFormClass.scharlauTransfer s hs 1) •
        hyperbolicClass K := RegularFormClass.mul_hyperbolicClass _
    _ = Module.finrank K L • hyperbolicClass K := by simp

end TauCeti
