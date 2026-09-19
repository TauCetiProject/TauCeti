/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Graded.Basic
public import TauCeti.CategoryTheory.Exact.Resolution

/-!
# Finite resolutions in a graded exact category

In a graded exact category the grading shift `{1}` and its inverse are conflation-exact, so they
carry finite resolutions to finite resolutions. When the resolving class `P` is stable under the
shift, the shift of a finite `P`-resolution of `X` is a finite `P`-resolution of `X{1}`, with the
same length and the internal degrees of all its terms raised by one.

Consequently the objects of finite `P`-dimension form a shift-stable class as well. This is the
hypothesis under which the full subcategory of such objects carries the induced graded exact
structure of `TauCeti.GradedExactStructure.fullSubcategory`, so that the resolution theorem can
be stated between graded Grothendieck groups.

## Main results

* `TauCeti.GradedExactStructure.admitsFiniteResolution_inverseImage_shift`: if `P` is stable
  under the grading shift, then so is the property of admitting a finite `P`-resolution.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 7,
  for finite resolutions and the resolution theorem.
* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for grading shifts on exact
  categories.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

namespace GradedExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  (E : GradedExactStructure C) {P : ObjectProperty C}

/-- **Shift stability of finite `P`-dimension.** If an object satisfies `P` exactly when its
shift does, then an object admits a finite `P`-resolution exactly when its shift does: a
resolution is carried across by the shift in one direction, and by the inverse shift followed by
transport along the unit isomorphism in the other. -/
theorem admitsFiniteResolution_inverseImage_shift [P.IsClosedUnderIsomorphisms]
    (hshift : P.inverseImage E.shift.functor = P) :
    (E.admitsFiniteResolution P).inverseImage E.shift.functor = E.admitsFiniteResolution P := by
  have hfun : P ≤ P.inverseImage E.shift.functor := hshift.ge
  have hinv : P ≤ P.inverseImage E.shift.inverse := fun Y hY => by
    rw [ObjectProperty.prop_inverseImage_iff, ← hshift, ObjectProperty.prop_inverseImage_iff]
    exact P.prop_of_iso (E.shift.counitIso.app Y).symm hY
  refine le_antisymm (fun X hX => ?_)
    (E.admitsFiniteResolution_le_inverseImage P E.shift_exact hfun)
  exact (E.admitsFiniteResolution P).prop_of_iso (E.shift.unitIso.app X).symm
    (E.admitsFiniteResolution_le_inverseImage P E.shift_inverse_exact hinv _ hX)

end GradedExactStructure

end TauCeti
