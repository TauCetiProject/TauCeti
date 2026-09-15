/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.SquareClassGroup.Multiplicative
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant

/-!
# Discriminants under extension of scalars

The discriminant of a regular quadratic form commutes with extension of the base field. The
comparison uses the functorial map on square-class groups induced by the field homomorphism.

These results let invariants computed over a global field be read after passing to any field
extension, in particular to the completions of a number field.
-/

public section
noncomputable section

open QuadraticMap QuadraticForm
open scoped TensorProduct

namespace TauCeti

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

variable [Invertible (2 : K)]

/-- The canonical coordinate equivalence identifies scalar extension of a presented form with
the presentation obtained by mapping every weight into the larger field. -/
def presentedFormBaseChange (p : RegularFormPresentation K) :
    ((presentedForm p).baseChange L).IsometryEquiv
      (presentedForm (⟨p.1, fun i ↦ Units.map (algebraMap K L).toMonoidHom (p.2 i)⟩ :
        RegularFormPresentation L)) := by
  let e := _root_.QuadraticForm.baseChangeWeightedSumSquares (A := L)
    fun i ↦ (p.2 i : K)
  have hK : presentedForm p =
      QuadraticMap.weightedSumSquares K fun i ↦ (p.2 i : K) := by
    ext x
    simp only [presentedForm_apply, QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
  have hL :
      presentedForm (⟨p.1, fun i ↦ Units.map (algebraMap K L).toMonoidHom (p.2 i)⟩ :
        RegularFormPresentation L) =
        QuadraticMap.weightedSumSquares L fun i ↦ algebraMap K L (p.2 i : K) := by
    ext x
    simp only [presentedForm_apply, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
      Units.coe_map]
    rfl
  refine { toLinearEquiv := e.toLinearEquiv, map_app' := ?_ }
  intro x
  rw [hL, hK]
  exact e.map_app' x

/-- The presentation base-change isometry uses the canonical linear equivalence distributing
the tensor product over the finite coordinate space. -/
@[simp]
theorem presentedFormBaseChange_apply (p : RegularFormPresentation K)
    (x : L ⊗[K] (Fin p.1 → K)) :
    presentedFormBaseChange (L := L) p x = TensorProduct.piScalarRightHom K L L (Fin p.1) x := by
  rw [presentedFormBaseChange]
  exact _root_.QuadraticForm.baseChangeWeightedSumSquares_apply
    (A := L) (fun i ↦ (p.2 i : K)) x

variable [Invertible (2 : L)]

/-- The discriminant of a regular form commutes with extension of the base field. -/
@[simp]
theorem discr_formClass_baseChange (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    RegularFormClass.discr
        (formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)) =
      (algebraMap K L).squareClassMap (RegularFormClass.discr (formClass Q hQ)) := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  have hpL : ((presentedForm p).baseChange L).Equivalent
      (presentedForm (⟨p.1, fun i ↦ Units.map (algebraMap K L).toMonoidHom (p.2 i)⟩ :
        RegularFormPresentation L)) :=
    ⟨presentedFormBaseChange p⟩
  rw [discr_formClass Q hQ p hp,
    discr_formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)
      (⟨p.1, fun i ↦ Units.map (algebraMap K L).toMonoidHom (p.2 i)⟩ :
        RegularFormPresentation L) ((hp.baseChange L).trans hpL)]
  simp only [RingHom.squareClassMap_apply, map_prod]

end TauCeti
