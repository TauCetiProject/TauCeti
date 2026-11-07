/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Resolution.Unbounded.Horseshoe
public import TauCeti.CategoryTheory.Exact.Graded.Projective

/-!
# Internal shifts of unbounded relative projective resolutions

The internal grading autoequivalence and its inverse transport every conflation and projective
term of an unbounded resolution. Their spliced complexes agree with the termwise images of
the original complex. `Horseshoe.map` transports a prescribed horseshoe along either shift
using `GradedExactStructure.shift_exact` or `GradedExactStructure.shift_inverse_exact` and the
corresponding projectivity-invariance theorem. These are internal grading shifts, not
homological translations.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* Theo Bühler, *Exact categories*, Section 12.
-/

public section

namespace TauCeti.ExactStructure.ProjectiveResolution

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : GradedExactStructure C}
  (r : E.toExactStructure.ProjectiveResolution)

/-- Apply the internal grading shift to all terms, syzygies and conflations. -/
abbrev shift : E.toExactStructure.ProjectiveResolution :=
  r.map E.shift_exact E.isProjective_inverseImage_shift.ge

/-- Apply the inverse internal grading shift to all terms, syzygies and conflations. -/
abbrev inverseShift : E.toExactStructure.ProjectiveResolution :=
  r.map E.shift_inverse_exact E.isProjective_inverseImage_inverseShift.ge

/-- Splicing commutes with the internal grading shift. -/
noncomputable def shiftComplexIso : r.shift.complex ≅
    (E.shift.functor.mapHomologicalComplex (ComplexShape.down ℕ)).obj r.complex :=
  r.mapComplexIso E.shift_exact E.isProjective_inverseImage_shift.ge

/-- Splicing commutes with the inverse internal grading shift. -/
noncomputable def inverseShiftComplexIso : r.inverseShift.complex ≅
    (E.shift.inverse.mapHomologicalComplex (ComplexShape.down ℕ)).obj r.complex :=
  r.mapComplexIso E.shift_inverse_exact E.isProjective_inverseImage_inverseShift.ge

end TauCeti.ExactStructure.ProjectiveResolution
