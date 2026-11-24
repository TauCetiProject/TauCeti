/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import TauCeti.RingTheory.DedekindDomain.Different.Basic

/-!
# Ideal-class lemmas for the different and trace dual

This module connects `FractionalIdeal.dualEquiv` and `differentIdeal` with `ClassGroup` without
adding a `Mathlib.RingTheory.ClassGroup.Basic` dependency to
`TauCeti.RingTheory.DedekindDomain.Different.Basic`.

## Main definitions

* `ClassGroup.different`: the ideal class of `differentIdeal R S` in `ClassGroup S`.

## Main results

* `ClassGroup.different_def`: defining formula for `ClassGroup.different R S`.
* `ClassGroup.mk_dualEquiv`: the ideal class of `dualEquiv R K I` is
  `[dualEquiv R K 1] * [I]⁻¹`.
* `ClassGroup.mk0_differentIdeal`: the ideal class of `differentIdeal R S` is
  `[dualEquiv R K 1]⁻¹`.
* `ClassGroup.different_eq_inv_mk_dualEquiv_one`: `ClassGroup.different R S` equals
  `[dualEquiv R K 1]⁻¹`.
-/

public section

open scoped nonZeroDivisors

section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (R S : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S]
  [Module.Finite R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

/-- **The ideal class of the different ideal** `differentIdeal R S` in `ClassGroup S`. -/
noncomputable def ClassGroup.different : ClassGroup S :=
  ClassGroup.mk0 ⟨differentIdeal R S, mem_nonZeroDivisors_of_ne_zero differentIdeal_ne_bot⟩

/-- Defining equation of `ClassGroup.different`. -/
theorem ClassGroup.different_def :
    ClassGroup.different R S =
      ClassGroup.mk0 ⟨differentIdeal R S, mem_nonZeroDivisors_of_ne_zero differentIdeal_ne_bot⟩ :=
  (rfl)

end

section

variable (R K : Type*) {S L : Type*}
variable [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [CommRing S] [IsDedekindDomain S]
variable [Algebra R L] [Algebra R S] [Algebra S L] [IsScalarTower R K L] [IsScalarTower R S L]
variable [IsFractionRing S L] [IsIntegralClosure S R L]

/-- The ideal class of the trace dual `FractionalIdeal.dualEquiv R K I` is the class of the inverse
different `dualEquiv R K 1` times `[I]⁻¹`. -/
theorem ClassGroup.mk_dualEquiv (I : (FractionalIdeal S⁰ L)ˣ) :
    ClassGroup.mk L (FractionalIdeal.dualEquiv R K I) =
      ClassGroup.mk L (FractionalIdeal.dualEquiv R K 1) * (ClassGroup.mk L I)⁻¹ := by
  rw [FractionalIdeal.dualEquiv_eq_mul_inv, map_mul, map_inv]

/-- The ideal class of the different ideal `differentIdeal R S` is the inverse of the class of the
inverse different `FractionalIdeal.dualEquiv R K 1`. -/
theorem ClassGroup.mk0_differentIdeal [Module.IsTorsionFree R S]
    (hd : differentIdeal R S ∈ (Ideal S)⁰) :
    ClassGroup.mk0 ⟨differentIdeal R S, hd⟩ =
      (ClassGroup.mk L (FractionalIdeal.dualEquiv R K (1 : (FractionalIdeal S⁰ L)ˣ)))⁻¹ := by
  rw [← ClassGroup.mk_mk0 L, ← map_inv]
  congr 1
  apply Units.ext
  rw [FractionalIdeal.coe_mk0, Units.val_inv_eq_inv_val, FractionalIdeal.coe_dualEquiv,
    Units.val_one, coeIdeal_differentIdeal (A := R) (K := K)]

section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The ideal class `ClassGroup.different R S` equals the inverse of the class of the inverse
different `FractionalIdeal.dualEquiv R K 1`. -/
theorem ClassGroup.different_eq_inv_mk_dualEquiv_one [Module.IsTorsionFree R S]
    [Module.Finite R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)] :
    ClassGroup.different R S =
      (ClassGroup.mk L (FractionalIdeal.dualEquiv R K (1 : (FractionalIdeal S⁰ L)ˣ)))⁻¹ := by
  rw [ClassGroup.different_def, ClassGroup.mk0_differentIdeal R K (L := L)]

end

end
