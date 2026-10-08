/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Graded.Projective
public import TauCeti.CategoryTheory.Exact.Resolution.Horseshoe

/-!
# Shifting horseshoes in a graded exact category

A horseshoe over a conflation consists of compatible finite projective resolutions of its three
terms, with a split short complex in every resolution degree. In a graded exact category the
internal shift `{1}` and its inverse preserve both conflations and projective objects, so the
functorial transport of horseshoes applies in both directions.

This file records those two specializations. Their middle resolutions are the shifted and
inverse-shifted middle resolutions already used by the graded comparison theorem. Consequently
the whole horseshoe commutes with the grading shift: its augmentation-compatible chain maps and
degreewise splittings are transported by the shift, and its length is unchanged.

## Main definitions

* `TauCeti.ExactStructure.FiniteResolution.Horseshoe.shift`: transport a finite projective
  horseshoe by `{1}`.
* `TauCeti.ExactStructure.FiniteResolution.Horseshoe.inverseShift`: transport it by `{-1}`.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.Horseshoe.shift_resolution`: the middle resolution of
  the transported horseshoe is the shift of the original middle resolution.
* `TauCeti.ExactStructure.FiniteResolution.Horseshoe.shift_ι_f` and
  `TauCeti.ExactStructure.FiniteResolution.Horseshoe.shift_π_f`: component formulas for the two
  transported chain maps. The parallel `inverseShift_*` results cover `{-1}`.

## References

* Theo Bühler, *Exact Categories*, Sections 11--12.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Lemma 2.2.8.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ExactStructure.FiniteResolution.Horseshoe

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  {E : GradedExactStructure C} {S : ShortComplex C}
  {r₁ : E.toExactStructure.FiniteResolution E.isProjective S.X₁}
  {r₃ : E.toExactStructure.FiniteResolution E.isProjective S.X₃}
  (h : Horseshoe S r₁ r₃)

/-- **The shift of a finite projective horseshoe.** This is the functorial image of the
horseshoe under `{1}`; shift invariance of relative projectivity supplies the required
projective terms. -/
noncomputable def shift :
    Horseshoe (S.map E.shift.functor)
      (r₁.map E.shift_exact E.isProjective_inverseImage_shift.ge)
      (r₃.map E.shift_exact E.isProjective_inverseImage_shift.ge) :=
  h.map E.shift_exact E.isProjective_inverseImage_shift.ge

/-- **The inverse shift of a finite projective horseshoe.** This is the functorial image under
`{-1}`. -/
noncomputable def inverseShift :
    Horseshoe (S.map E.shift.inverse)
      (r₁.map E.shift_inverse_exact E.isProjective_inverseImage_inverseShift.ge)
      (r₃.map E.shift_inverse_exact E.isProjective_inverseImage_inverseShift.ge) :=
  let _ : E.shift.symm.functor.Additive := inferInstanceAs E.shift.inverse.Additive
  h.map E.shift_inverse_exact E.isProjective_inverseImage_inverseShift.ge

/-- The middle resolution of the shifted horseshoe is the shift of the original middle
resolution. -/
theorem shift_resolution : h.shift.resolution = h.resolution.shiftProjective :=
  (Horseshoe.map_resolution h E.shift_exact
    E.isProjective_inverseImage_shift.ge).trans
      (ExactStructure.FiniteResolution.shiftProjective_eq_map h.resolution).symm

/-- The middle resolution of the inversely shifted horseshoe is the inverse shift of the original
middle resolution. -/
theorem inverseShift_resolution :
    h.inverseShift.resolution = h.resolution.inverseShiftProjective :=
  (Horseshoe.map_resolution h E.shift_inverse_exact
    E.isProjective_inverseImage_inverseShift.ge).trans
      (ExactStructure.FiniteResolution.inverseShiftProjective_eq_map h.resolution).symm

/-- The shifted horseshoe has the same middle-resolution length as the original horseshoe. -/
@[simp]
theorem shift_resolution_length : h.shift.resolution.length = h.resolution.length := by
  rw [shift_resolution, length_shiftProjective]

/-- The inversely shifted horseshoe has the same middle-resolution length as the original
horseshoe. -/
@[simp]
theorem inverseShift_resolution_length :
    h.inverseShift.resolution.length = h.resolution.length := by
  rw [inverseShift_resolution, length_inverseShiftProjective]

/-- Each component of the shifted injection is obtained by applying `{1}` to the original
component and conjugating by the term identifications of the transported resolutions. -/
@[simp]
theorem shift_ι_f (n : ℕ) : HEq (h.shift.ι.f n)
    ((termMapIso E.shift_exact E.isProjective_inverseImage_shift.ge r₁ n).hom ≫
      E.shift.functor.map (h.ι.f n) ≫
        (termMapIso E.shift_exact E.isProjective_inverseImage_shift.ge h.resolution n).inv ≫
          eqToHom (congrArg (fun r => r.term n)
            (Horseshoe.map_resolution h E.shift_exact
              E.isProjective_inverseImage_shift.ge).symm)) := by
  simp [shift]

/-- Each component of the shifted projection is obtained by applying `{1}` to the original
component and conjugating by the term identifications of the transported resolutions. -/
@[simp]
theorem shift_π_f (n : ℕ) : HEq (h.shift.π.f n)
    ((termMapIso E.shift_exact E.isProjective_inverseImage_shift.ge h.resolution n).hom ≫
      E.shift.functor.map (h.π.f n) ≫
        (termMapIso E.shift_exact E.isProjective_inverseImage_shift.ge r₃ n).inv) := by
  simp [shift]

/-- Each component of the inversely shifted injection is the inverse-shifted original component,
conjugated by the term identifications. -/
@[simp]
theorem inverseShift_ι_f (n : ℕ) : HEq (h.inverseShift.ι.f n)
    ((termMapIso E.shift_inverse_exact E.isProjective_inverseImage_inverseShift.ge r₁ n).hom ≫
      E.shift.inverse.map (h.ι.f n) ≫
        (termMapIso E.shift_inverse_exact E.isProjective_inverseImage_inverseShift.ge
          h.resolution n).inv ≫ eqToHom (congrArg (fun r => r.term n)
            (Horseshoe.map_resolution h E.shift_inverse_exact
              E.isProjective_inverseImage_inverseShift.ge).symm)) := by
  simp [inverseShift]

/-- Each component of the inversely shifted projection is the inverse-shifted original component,
conjugated by the term identifications. -/
@[simp]
theorem inverseShift_π_f (n : ℕ) : HEq (h.inverseShift.π.f n)
    ((termMapIso E.shift_inverse_exact E.isProjective_inverseImage_inverseShift.ge
      h.resolution n).hom ≫ E.shift.inverse.map (h.π.f n) ≫
        (termMapIso E.shift_inverse_exact
          E.isProjective_inverseImage_inverseShift.ge r₃ n).inv) := by
  simp [inverseShift]

end ExactStructure.FiniteResolution.Horseshoe

end TauCeti
