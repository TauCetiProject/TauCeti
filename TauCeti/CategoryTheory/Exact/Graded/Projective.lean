/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Graded.Resolution
public import TauCeti.CategoryTheory.Exact.Projective

/-!
# Projectives and projective resolutions in a graded exact category

The grading shift of a graded exact category is a conflation-exact autoequivalence. Relative
projectivity is therefore invariant under shifting: an object is projective precisely when its
shift, or its inverse shift, is projective. This supplies the shift stability of the canonical
projective class rather than requiring it as an extra hypothesis.

The same equivalence shifts projective presentations and finite projective resolutions term by
term. In particular, the objects of finite projective dimension form a shift-stable property.
These facts are the projective input to graded comparison and horseshoe constructions and to the
graded resolution theorem.

## Main results

* `TauCeti.GradedExactStructure.isProjective_shift_iff`: projectivity is invariant under the
  grading shift.
* `TauCeti.ExactStructure.ProjectivePresentation.shift`: shift a relative projective
  presentation.
* `TauCeti.ExactStructure.FiniteResolution.shiftProjective`: shift a finite projective
  resolution term by term.
* `TauCeti.GradedExactStructure.admitsFiniteProjectiveResolution_inverseImage_shift`: finite
  projective dimension is invariant under the grading shift.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Sections 11--12, for projectives and projective resolutions
  in exact categories.
* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for grading shifts on projective
  resolutions.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

namespace GradedExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] (E : GradedExactStructure C)

/-- An object is projective relative to a graded exact structure exactly when its grading shift
is projective. -/
@[simp]
theorem isProjective_shift_iff (Q : C) :
    E.isProjective (E.shift.functor.obj Q) ↔ E.isProjective Q :=
  E.toExactStructure.isProjective_map_equivalence_iff E.toExactStructure E.shift
    E.shift_exact E.shift_inverse_exact Q

/-- An object is projective relative to a graded exact structure exactly when its inverse grading
shift is projective. -/
@[simp]
theorem isProjective_inverseShift_iff (Q : C) :
    E.isProjective (E.shift.inverse.obj Q) ↔ E.isProjective Q :=
  let _ : E.shift.symm.functor.Additive := inferInstanceAs E.shift.inverse.Additive
  E.toExactStructure.isProjective_map_equivalence_iff E.toExactStructure E.shift.symm
      E.shift_inverse_exact E.shift_exact Q

/-- The relative projectives form a shift-stable object property. -/
@[simp]
theorem isProjective_inverseImage_shift :
    E.isProjective.inverseImage E.shift.functor = E.isProjective := by
  ext Q
  exact E.isProjective_shift_iff Q

/-- The relative projectives are also stable under the inverse grading shift. -/
@[simp]
theorem isProjective_inverseImage_inverseShift :
    E.isProjective.inverseImage E.shift.inverse = E.isProjective := by
  ext Q
  exact E.isProjective_inverseShift_iff Q

/-- The objects of finite projective dimension form a shift-stable property. -/
@[simp]
theorem admitsFiniteProjectiveResolution_inverseImage_shift :
    (E.admitsFiniteResolution E.isProjective).inverseImage E.shift.functor =
      E.admitsFiniteResolution E.isProjective :=
  E.admitsFiniteResolution_inverseImage_shift E.isProjective_inverseImage_shift

/-- The objects of finite projective dimension are also stable under the inverse grading shift. -/
@[simp]
theorem admitsFiniteProjectiveResolution_inverseImage_inverseShift :
    (E.admitsFiniteResolution E.isProjective).inverseImage E.shift.inverse =
      E.admitsFiniteResolution E.isProjective := by
  apply le_antisymm
  · intro X hX
    rw [ObjectProperty.prop_inverseImage_iff] at hX
    rw [← E.admitsFiniteProjectiveResolution_inverseImage_shift,
      ObjectProperty.prop_inverseImage_iff] at hX
    exact (E.admitsFiniteResolution E.isProjective).prop_of_iso (E.shift.counitIso.app X) hX
  · intro X hX
    rw [ObjectProperty.prop_inverseImage_iff]
    have hX' : ((E.admitsFiniteResolution E.isProjective).inverseImage E.shift.functor)
        (E.shift.inverse.obj X) := by
      rw [ObjectProperty.prop_inverseImage_iff]
      exact (E.admitsFiniteResolution E.isProjective).prop_of_iso
        (E.shift.counitIso.app X).symm hX
    rw [E.admitsFiniteProjectiveResolution_inverseImage_shift] at hX'
    exact hX'

end GradedExactStructure

namespace ExactStructure.ProjectivePresentation

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : GradedExactStructure C} {X : C}

/-- Shift every object and morphism in a relative projective presentation. -/
def shift (P : E.toExactStructure.ProjectivePresentation X) :
    E.toExactStructure.ProjectivePresentation (E.shift.functor.obj X) :=
  P.mapAdjunction E.shift.toAdjunction E.shift_exact E.shift_inverse_exact

/-- Apply the inverse grading shift to every object and morphism in a relative projective
presentation. -/
def inverseShift (P : E.toExactStructure.ProjectivePresentation X) :
    E.toExactStructure.ProjectivePresentation (E.shift.inverse.obj X) :=
  let _ : E.shift.symm.functor.Additive := inferInstanceAs E.shift.inverse.Additive
  P.mapAdjunction E.shift.symm.toAdjunction E.shift_inverse_exact E.shift_exact

@[simp] theorem shift_K (P : E.toExactStructure.ProjectivePresentation X) :
    P.shift.K = E.shift.functor.obj P.K := by
  simp [shift]

@[simp] theorem shift_P (P : E.toExactStructure.ProjectivePresentation X) :
    P.shift.P = E.shift.functor.obj P.P := by
  simp [shift]

@[simp] theorem shift_i (P : E.toExactStructure.ProjectivePresentation X) :
    HEq P.shift.i (E.shift.functor.map P.i) := by
  simp [shift]

@[simp] theorem shift_p (P : E.toExactStructure.ProjectivePresentation X) :
    HEq P.shift.p (E.shift.functor.map P.p) := by
  simp [shift]

@[simp] theorem inverseShift_K (P : E.toExactStructure.ProjectivePresentation X) :
    P.inverseShift.K = E.shift.inverse.obj P.K := by
  simp [inverseShift]

@[simp] theorem inverseShift_P (P : E.toExactStructure.ProjectivePresentation X) :
    P.inverseShift.P = E.shift.inverse.obj P.P := by
  simp [inverseShift]

@[simp] theorem inverseShift_i (P : E.toExactStructure.ProjectivePresentation X) :
    HEq P.inverseShift.i (E.shift.inverse.map P.i) := by
  simp [inverseShift]

@[simp] theorem inverseShift_p (P : E.toExactStructure.ProjectivePresentation X) :
    HEq P.inverseShift.p (E.shift.inverse.map P.p) := by
  simp [inverseShift]

end ExactStructure.ProjectivePresentation

namespace ExactStructure.FiniteResolution

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : GradedExactStructure C} {X : C}

/-- Shift every term and conflation of a finite projective resolution. -/
def shiftProjective
    (r : E.toExactStructure.FiniteResolution E.isProjective X) :
    E.toExactStructure.FiniteResolution E.isProjective (E.shift.functor.obj X) :=
  r.map E.shift_exact fun Q hQ ↦ by
    rw [ObjectProperty.prop_inverseImage_iff]
    exact (E.isProjective_shift_iff Q).2 hQ

/-- Apply the inverse grading shift to every term and conflation of a finite projective
resolution. -/
def inverseShiftProjective
    (r : E.toExactStructure.FiniteResolution E.isProjective X) :
    E.toExactStructure.FiniteResolution E.isProjective (E.shift.inverse.obj X) :=
  let _ : E.shift.symm.functor.Additive := inferInstanceAs E.shift.inverse.Additive
  r.map E.shift_inverse_exact fun Q hQ ↦ by
      rw [ObjectProperty.prop_inverseImage_iff]
      exact (E.isProjective_inverseShift_iff Q).2 hQ

@[simp] theorem length_shiftProjective
    (r : E.toExactStructure.FiniteResolution E.isProjective X) :
    r.shiftProjective.length = r.length := by
  simp [shiftProjective]

@[simp] theorem length_inverseShiftProjective
    (r : E.toExactStructure.FiniteResolution E.isProjective X) :
    r.inverseShiftProjective.length = r.length := by
  simp [inverseShiftProjective]

end ExactStructure.FiniteResolution

end TauCeti
