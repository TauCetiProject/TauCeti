/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic

/-!
# Scharlau transfer of isometry classes

Scharlau transfer along a nonzero linear functional carries regular quadratic forms over a finite
field extension to regular quadratic forms over the base field. Since transfer preserves
isometries and orthogonal sums, it induces an additive map on isometry classes. This file
constructs that map and records its values on forms, its rank, and its identity and tower laws.

The class-level construction is the input for the transfer on Witt rings. It also lets results
about a transferred form be stated without choosing a diagonalization.

## Main definitions

* `TauCeti.RegularFormClass.scharlauTransfer`: Scharlau transfer as an additive homomorphism on
  isometry classes of regular forms.
* `TauCeti.RegularFormClass.traceTransfer`: the specialization to the algebra trace of a finite
  separable extension.

## Main results

* `TauCeti.RegularFormClass.scharlauTransfer_formClass`: transfer of the class of a regular form
  is the class of its transferred form.
* `TauCeti.RegularFormClass.rank_scharlauTransfer`: transfer multiplies rank by the degree of the
  field extension.
* `TauCeti.RegularFormClass.scharlauTransfer_id`: transfer along the identity is the identity.
* `TauCeti.RegularFormClass.scharlauTransfer_comp`: transfers compose in a tower.
* `TauCeti.RegularFormClass.traceTransfer_formClass`: trace transfer agrees with the form-level
  trace transfer.

## References

* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter VII, §1.
-/

public section
noncomputable section

open QuadraticMap

namespace TauCeti

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Invertible (2 : K)]

private def scharlauTransferClassAux (s : L →ₗ[K] K) (hs : s ≠ 0) :
    RegularFormClass L → RegularFormClass K :=
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  Quotient.lift
      (fun p ↦ formClass ((presentedForm p).scharlauTransfer s)
        ((presentedForm p).nondegenerate_scharlauTransfer_iff_of_ne_zero s hs |>.mpr
          (nondegenerate_presentedForm p)))
      fun p q h ↦ by
        apply (formClass_eq_iff _ _ _ _).mpr
        exact h.scharlauTransfer s

private theorem scharlauTransferClassAux_mk (s : L →ₗ[K] K) (hs : s ≠ 0)
    (p : RegularFormPresentation L) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    scharlauTransferClassAux s hs (Quotient.mk (regularFormSetoid L) p) =
        formClass ((presentedForm p).scharlauTransfer s)
          ((presentedForm p).nondegenerate_scharlauTransfer_iff_of_ne_zero s hs |>.mpr
            (nondegenerate_presentedForm p)) := by
  rfl

private theorem scharlauTransferClassAux_add (s : L →ₗ[K] K) (hs : s ≠ 0)
    (x y : RegularFormClass L) :
    scharlauTransferClassAux s hs (x + y) =
      scharlauTransferClassAux s hs x + scharlauTransferClassAux s hs y := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  induction x using Quotient.inductionOn with
  | h p =>
    induction y using Quotient.inductionOn with
    | h q =>
      rw [RegularFormClass.mk_add_mk, scharlauTransferClassAux_mk,
        scharlauTransferClassAux_mk, scharlauTransferClassAux_mk, ← formClass_prod]
      apply (formClass_eq_iff _ _ _ _).mpr
      simpa only [QuadraticMap.scharlauTransfer_prod] using
        (equivalent_presentedForm_append_prod p q).scharlauTransfer s

/-- **Scharlau transfer of isometry classes.** Transfer along a nonzero `K`-linear functional
`s : L → K` is an additive homomorphism from regular-form classes over `L` to regular-form
classes over `K`. -/
def RegularFormClass.scharlauTransfer (s : L →ₗ[K] K) (hs : s ≠ 0) :
    RegularFormClass L →+ RegularFormClass K := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  exact
    { toFun := scharlauTransferClassAux s hs
      map_zero' := by
        apply RegularFormClass.rank_eq_zero_iff.mp
        rw [RegularFormClass.zero_def, scharlauTransferClassAux_mk, rank_formClass]
        rw [← Module.finrank_mul_finrank K L (Fin 0 → L)]
        simp
      map_add' := scharlauTransferClassAux_add s hs }

/-- Scharlau transfer of classes is computed on a diagonal presentation by transferring its
presented form. -/
@[simp]
theorem RegularFormClass.scharlauTransfer_mk (s : L →ₗ[K] K) (hs : s ≠ 0)
    (p : RegularFormPresentation L) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.scharlauTransfer s hs (Quotient.mk (regularFormSetoid L) p) =
        formClass ((presentedForm p).scharlauTransfer s)
          ((presentedForm p).nondegenerate_scharlauTransfer_iff_of_ne_zero s hs |>.mpr
            (nondegenerate_presentedForm p)) := by
  rfl

/-- The transfer of the isometry class of a regular form is the isometry class of its transfer.
This is the class-level form of `QuadraticMap.Equivalent.scharlauTransfer`. -/
@[simp]
theorem RegularFormClass.scharlauTransfer_formClass {V : Type w} [AddCommGroup V]
    [Module L V] [Module K V] [IsScalarTower K L V] [FiniteDimensional L V]
    (s : L →ₗ[K] K) (hs : s ≠ 0) (Q : QuadraticForm L V) (hQ : Q.Nondegenerate) :
    letI : FiniteDimensional K V := FiniteDimensional.trans K L V
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.scharlauTransfer s hs (formClass Q hQ) =
      formClass (Q.scharlauTransfer s)
        (Q.nondegenerate_scharlauTransfer_iff_of_ne_zero s hs |>.mpr hQ) := by
  let _ : FiniteDimensional K V := FiniteDimensional.trans K L V
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p hp, RegularFormClass.scharlauTransfer_mk]
  apply (formClass_eq_iff _ _ _ _).mpr
  exact (hp.scharlauTransfer s).symm

/-- Scharlau transfer multiplies the rank of an isometry class by the degree of the field
extension. -/
@[simp]
theorem RegularFormClass.rank_scharlauTransfer (s : L →ₗ[K] K) (hs : s ≠ 0)
    (x : RegularFormClass L) :
    (RegularFormClass.scharlauTransfer s hs x).rank = Module.finrank K L * x.rank := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  induction x using Quotient.inductionOn with
  | h p =>
    rw [RegularFormClass.scharlauTransfer_mk, rank_formClass, RegularFormClass.rank_mk,
      ← Module.finrank_mul_finrank K L (Fin p.1 → L)]
    simp

/-- Scharlau transfer along the identity functional is the identity on isometry classes. -/
@[simp]
theorem RegularFormClass.scharlauTransfer_id :
    RegularFormClass.scharlauTransfer (LinearMap.id : K →ₗ[K] K) one_ne_zero =
      AddMonoidHom.id (RegularFormClass K) := by
  ext x
  induction x using Quotient.inductionOn with
  | h p =>
    rw [RegularFormClass.scharlauTransfer_mk]
    apply formClass_mk _ _ p
    rw [QuadraticMap.scharlauTransfer_id]
    exact QuadraticMap.Equivalent.refl _

variable {E : Type w} [Field E] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
  [FiniteDimensional L E]

/-- Scharlau transfers compose in a tower of finite field extensions. -/
@[simp]
theorem RegularFormClass.scharlauTransfer_comp (s : L →ₗ[K] K) (hs : s ≠ 0)
    (t : E →ₗ[L] L) (ht : t ≠ 0) :
    letI : FiniteDimensional K E := FiniteDimensional.trans K L E
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    (RegularFormClass.scharlauTransfer s hs).comp
        (RegularFormClass.scharlauTransfer t ht) =
      RegularFormClass.scharlauTransfer (s.comp (t.restrictScalars K))
        (s.comp_restrictScalars_ne_zero t hs ht) := by
  let _ : FiniteDimensional K E := FiniteDimensional.trans K L E
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  let _ : Invertible (2 : E) :=
    (Invertible.map (algebraMap K E) 2).copy 2 (map_ofNat _ _).symm
  ext x
  induction x using Quotient.inductionOn with
  | h p =>
    rw [AddMonoidHom.comp_apply, RegularFormClass.scharlauTransfer_mk,
      RegularFormClass.scharlauTransfer_formClass, RegularFormClass.scharlauTransfer_mk]
    apply (formClass_eq_iff _ _ _ _).mpr
    rw [QuadraticMap.scharlauTransfer_scharlauTransfer]
    exact QuadraticMap.Equivalent.refl _

/-! ### Transfer along the trace -/

variable [Algebra.IsSeparable K L]

variable (K) in
/-- Trace transfer on isometry classes, defined using the nonzero algebra trace of a finite
separable field extension. -/
def RegularFormClass.traceTransfer : RegularFormClass L →+ RegularFormClass K :=
  RegularFormClass.scharlauTransfer (Algebra.trace K L) (Algebra.trace_ne_zero K L)

/-- Class-level trace transfer is Scharlau transfer along the algebra trace. -/
theorem RegularFormClass.traceTransfer_eq_scharlauTransfer (x : RegularFormClass L) :
    RegularFormClass.traceTransfer K x =
      RegularFormClass.scharlauTransfer (Algebra.trace K L) (Algebra.trace_ne_zero K L) x := by
  rfl

/-- Trace transfer of the class of a regular form is the class of its form-level trace transfer. -/
@[simp]
theorem RegularFormClass.traceTransfer_formClass {V : Type w} [AddCommGroup V]
    [Module L V] [Module K V] [IsScalarTower K L V] [FiniteDimensional L V]
    (Q : QuadraticForm L V) (hQ : Q.Nondegenerate) :
    letI : FiniteDimensional K V := FiniteDimensional.trans K L V
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.traceTransfer K (formClass Q hQ) =
      formClass (Q.traceTransfer K) (Q.nondegenerate_traceTransfer_iff.mpr hQ) := by
  let _ : FiniteDimensional K V := FiniteDimensional.trans K L V
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [RegularFormClass.traceTransfer, RegularFormClass.scharlauTransfer_formClass]
  apply (formClass_eq_iff _ _ _ _).mpr
  rw [QuadraticMap.traceTransfer_eq_scharlauTransfer]

/-- Trace transfer multiplies rank by the degree of the field extension. -/
@[simp]
theorem RegularFormClass.rank_traceTransfer (x : RegularFormClass L) :
    (RegularFormClass.traceTransfer K x).rank = Module.finrank K L * x.rank := by
  rw [RegularFormClass.traceTransfer, RegularFormClass.rank_scharlauTransfer]

end TauCeti
