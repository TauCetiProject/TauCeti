/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IntermediateField.LinearDisjoint
public import TauCeti.FieldTheory.Minpoly.IsIntegrallyClosedIn

/-!
# Degree under extension of constants

A finite separable extension of an exact field of constants preserves the degree of a function
field over any rational parameter. This is the degree comparison in Stichtenoth,
*Algebraic Function Fields and Codes*, second edition, Proposition 3.6.1(c).
-/

public section

noncomputable section

open scoped IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]

/-- A finite separable extension of an exact field of constants preserves the degree over any
rational parameter. The equation is stated for the compositum `L = A · B` inside a common ambient
field; `A ⊔ k(x)` is the enlarged rational subfield. -/
theorem finrank_adjoin_eq_of_isIntegrallyClosedIn
    (A B : IntermediateField k L) (x : B)
    (hA : FiniteDimensional k A) [Algebra.IsSeparable k A]
    (hex : IsIntegrallyClosedIn k B)
    (hAB : A ⊔ B = ⊤) :
    Module.finrank ↥(A ⊔ IntermediateField.adjoin k {(x : L)}) L =
      Module.finrank ↥(IntermediateField.adjoin k {(x : L)})
        (IntermediateField.extendScalars
          (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr x.property))) := by
  have h : A.LinearDisjoint B := by
    simpa only [show IsScalarTower.toAlgHom k A L = A.val from rfl,
      IntermediateField.fieldRange_val] using
      (linearDisjoint_fieldRange_of_isIntegrallyClosedIn hex (k' := A) (E := L))
  let C : IntermediateField k L := IntermediateField.adjoin k {(x : L)}
  have hCB : C ≤ B := IntermediateField.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr x.property)
  have hdegree := finrank_sup_eq_finrank_of_linearDisjoint A B C hCB hA h
  have htop : (IntermediateField.extendScalars (sup_le_sup_left hCB A) :
      IntermediateField ↥(A ⊔ C) L) = ⊤ := by
    ext y
    simp only [IntermediateField.mem_extendScalars, hAB, IntermediateField.mem_top]
  rw [htop, IntermediateField.finrank_top'] at hdegree
  exact hdegree

end TauCeti
