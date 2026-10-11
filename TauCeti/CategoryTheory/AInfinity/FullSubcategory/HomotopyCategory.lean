/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.FullSubcategory.Basic
public import TauCeti.CategoryTheory.AInfinity.HomotopyCategory

/-!
# Homotopy-level properties of full A-infinity subcategories

Closed degree-zero morphisms and boundaries of a full subcategory are those of the ambient
category. Consequently cohomological units restrict to full subcategories.

## Main results

* `TauCeti.AInfinityCategory.homCyclesZero_fullSubcategory`
* `TauCeti.AInfinityCategory.range_homDifferential_fullSubcategory`
* `TauCeti.AInfinityCategory.CohomologicalUnits.fullSubcategory`
* `TauCeti.AInfinityCategory.CohomologicallyUnital.fullSubcategory`

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.
-/

public section

namespace TauCeti

universe u v w

open GradedLinearQuiver GradedLinearQuiver.FullSubquiver

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : AInfinityCategory R C) (P : C → Prop)

/-- The closed degree-zero morphisms of the full subcategory are those of `𝒞`. -/
@[simp]
theorem homCyclesZero_fullSubcategory (X Y : FullSubquiver P) :
    (𝒞.fullSubcategory P).homCyclesZero X Y = 𝒞.homCyclesZero X.obj Y.obj := by
  ext f
  simp [FullSubquiver.grading_eq]

/-- The boundaries of the full subcategory are those of `𝒞`. -/
@[simp]
theorem range_homDifferential_fullSubcategory (X Y : FullSubquiver P) :
    LinearMap.range ((𝒞.fullSubcategory P).homDifferential X Y) =
      LinearMap.range (𝒞.homDifferential X.obj Y.obj) := by
  congr 1
  exact LinearMap.ext (𝒞.homDifferential_fullSubcategory P X Y)

variable {𝒞} {e : ∀ X : C, homModule (R := R) X X}

/-- **Cohomological units restrict to full subcategories.** -/
theorem CohomologicalUnits.fullSubcategory (he : 𝒞.CohomologicalUnits e) :
    (𝒞.fullSubcategory P).CohomologicalUnits fun X ↦ e X.obj where
  cycle X := by simpa using he.cycle X.obj
  left_unit X Y f hf := by
    simpa using he.left_unit X.obj Y.obj f (by simpa using hf)
  right_unit X Y f hf := by
    simpa using he.right_unit X.obj Y.obj f (by simpa using hf)

/-- A full subcategory of a cohomologically unital `A∞` category is cohomologically unital. -/
theorem CohomologicallyUnital.fullSubcategory (h𝒞 : 𝒞.CohomologicallyUnital) :
    (𝒞.fullSubcategory P).CohomologicallyUnital := by
  rw [cohomologicallyUnital_iff] at h𝒞 ⊢
  obtain ⟨e, he⟩ := h𝒞
  exact ⟨_, he.fullSubcategory P⟩

end AInfinityCategory

end TauCeti
