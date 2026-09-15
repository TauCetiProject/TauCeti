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
# Scalar extension of isometry classes and their discriminants

Extension of scalars along a field extension `K → L` carries a diagonal presentation to the
presentation of the same rank whose weights are the images of the original weights. That operation
descends to isometry classes as `TauCeti.RegularFormClass.baseChange`, and the discriminant
commutes with it: the discriminant of an extended class is the image of the original discriminant
under the functorial map on square-class groups induced by the field homomorphism.

Everything here is about field extensions in characteristic different from two. That restriction is
not an artefact: `QuadraticForm.baseChange` is only defined when two is invertible in the base
field, and `TauCeti.RegularFormClass.discr` is only defined over a field in which two is
invertible, so both hypotheses are needed already to state the results.

These results let invariants computed over a global field be read after passing to any such field
extension, in particular to the completions of a number field.

## Main definitions

* `TauCeti.RegularFormPresentation.baseChange`: the presentation whose weights are the images of
  the original weights.
* `TauCeti.RegularFormClass.baseChange`: scalar extension of isometry classes.

## Main results

* `TauCeti.presentedFormBaseChange`: extending a presented form presents the extended weights.
* `TauCeti.formClass_baseChange`: the class of an extended form is the extension of its class.
* `TauCeti.RegularFormClass.discr_baseChange` and `QuadraticForm.discr_formClass_baseChange`: the
  discriminant commutes with scalar extension, stated on classes and on forms.
-/

public section
noncomputable section

open QuadraticMap QuadraticForm
open scoped TensorProduct

namespace TauCeti

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

variable (L) in
/-- The presentation obtained by mapping every weight into the extension field `L`. The rank is
unchanged, so the definition is `@[expose]`d: statements about the mapped presentation are indexed
by `Fin (RegularFormPresentation.baseChange L p).1`, and unfolding identifies that with
`Fin p.1`. -/
@[expose]
def RegularFormPresentation.baseChange (p : RegularFormPresentation K) :
    RegularFormPresentation L :=
  ⟨p.1, fun i ↦ Units.map (algebraMap K L).toMonoidHom (p.2 i)⟩

variable [Invertible (2 : K)]

/-- The canonical coordinate equivalence identifies scalar extension of a presented form with
the presentation obtained by mapping every weight into the larger field. -/
def presentedFormBaseChange (p : RegularFormPresentation K) :
    ((presentedForm p).baseChange L).IsometryEquiv
      (presentedForm (RegularFormPresentation.baseChange L p)) := by
  let e := _root_.QuadraticForm.baseChangeWeightedSumSquares (A := L)
    fun i ↦ (p.2 i : K)
  have hK : presentedForm p =
      QuadraticMap.weightedSumSquares K fun i ↦ (p.2 i : K) := by
    simp only [presentedForm_eq_weightedSumSquares, QuadraticMap.weightedSumSquares,
      Units.smul_def]
  have hL : presentedForm (RegularFormPresentation.baseChange L p) =
      QuadraticMap.weightedSumSquares L fun i ↦ algebraMap K L (p.2 i : K) := by
    simp only [RegularFormPresentation.baseChange, presentedForm_eq_weightedSumSquares,
      QuadraticMap.weightedSumSquares, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Units.smul_def]
    -- The two sums are indexed by `Fin (RegularFormPresentation.baseChange L p).1` and by
    -- `Fin p.1`, which are the same type once the mapped presentation is unfolded.
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

variable (L) in
/-- **Scalar extension of isometry classes**: the class over `L` presented by the images of the
weights of any presentation over `K`. -/
def RegularFormClass.baseChange : RegularFormClass K → RegularFormClass L :=
  Quotient.map (RegularFormPresentation.baseChange L) fun p q h ↦ by
    have hp : (presentedForm (RegularFormPresentation.baseChange L p)).Equivalent
        ((presentedForm p).baseChange L) := ⟨(presentedFormBaseChange (L := L) p).symm⟩
    have hq : ((presentedForm q).baseChange L).Equivalent
        (presentedForm (RegularFormPresentation.baseChange L q)) :=
      ⟨presentedFormBaseChange (L := L) q⟩
    exact hp.trans ((QuadraticMap.Equivalent.baseChange h L).trans hq)

/-- Scalar extension of classes is computed on presentations by mapping the weights. -/
@[simp]
theorem RegularFormClass.baseChange_mk (p : RegularFormPresentation K) :
    RegularFormClass.baseChange L (Quotient.mk (regularFormSetoid K) p) =
      Quotient.mk (regularFormSetoid L) (RegularFormPresentation.baseChange L p) :=
  (rfl)

variable {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Invertible (2 : L)]

/-- The class of a form extended to `L` is the scalar extension of its class. -/
@[simp]
theorem formClass_baseChange (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    formClass (Q.baseChange L) (_root_.QuadraticForm.Nondegenerate.baseChange hQ) =
      RegularFormClass.baseChange L (formClass Q hQ) := by
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p hp, RegularFormClass.baseChange_mk,
    formClass_mk _ _ _ ((hp.baseChange L).trans ⟨presentedFormBaseChange p⟩)]

/-- **The discriminant commutes with scalar extension of isometry classes**: extending an isometry
class to `L` pushes its discriminant forward along the induced map of square-class groups. -/
@[simp]
theorem RegularFormClass.discr_baseChange (x : RegularFormClass K) :
    RegularFormClass.discr (RegularFormClass.baseChange L x) =
      (algebraMap K L).squareClassMap (RegularFormClass.discr x) := by
  refine Quotient.inductionOn x fun p ↦ ?_
  rw [RegularFormClass.baseChange_mk, RegularFormClass.discr_mk, RegularFormClass.discr_mk,
    RingHom.squareClassMap_apply, map_prod]
  -- Both weight products are now indexed by `Fin p.1` and have the same mapped terms.
  rfl

end TauCeti

namespace QuadraticForm

open TauCeti

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Invertible (2 : K)] [Invertible (2 : L)]

/-- The discriminant of a regular form commutes with extension of the base field, both fields
being of characteristic different from two. -/
theorem discr_formClass_baseChange (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    RegularFormClass.discr
        (formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)) =
      (algebraMap K L).squareClassMap (RegularFormClass.discr (formClass Q hQ)) := by
  rw [formClass_baseChange, RegularFormClass.discr_baseChange]

end QuadraticForm
