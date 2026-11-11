/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Map
public import TauCeti.LinearAlgebra.BilinearMap.IntLinear
public import TauCeti.LinearAlgebra.SesquilinearForm.NumericalQuotient.Functoriality

/-!
# Numerical quotients of the Ext-Euler pairing

The Ext-Euler characteristic descends to a biadditive pairing on the exact Grothendieck groups of
two extension-closed subcategories. This file views that pairing as an integer-bilinear map and
applies the separate left and right numerical-quotient construction to it.

The two subcategories are deliberately kept independent: the Ext-Euler pairing is generally
nonsymmetric, so its left and right radicals can differ. The generic numerical-quotient API supplies
the quotient maps, one-sided pairings, functoriality, and the nondegenerate pairing; this file adds
the Ext-Euler names and the computation rules needed by its users. It also shows that the
numerical Grothendieck groups are invariant under exact functors which are bijective on `Ext` and
essentially surjective onto the target subcategories, even when the induced maps of exact
Grothendieck groups are not injective.

## Main definitions

* `TauCeti.extEulerBilinear`: the integer-bilinear form underlying the descended Ext-Euler
  pairing.
* `TauCeti.ExtEulerLeftNumericalQuotient` and
  `TauCeti.ExtEulerRightNumericalQuotient`: the two numerical Grothendieck groups.
* `TauCeti.extEulerNumericalPairing`: the induced pairing between those two quotients.
* `TauCeti.extEulerLeftNumericalEquiv` and `TauCeti.extEulerRightNumericalEquiv`: the
  identifications of numerical Grothendieck groups induced by an exact functor which is bijective
  on `Ext` and whose images exhaust the target subcategories up to isomorphism.

## Main results

* `TauCeti.mem_extEulerLeftRadical_iff` and
  `TauCeti.mem_extEulerRightRadical_iff` characterize the two radicals using the Ext-Euler
  pairing.
* `TauCeti.extEulerNumericalPairing_mk` computes the quotient pairing on representatives.
* `TauCeti.extEulerNumericalPairing_unique` gives its universal characterization, and
  `TauCeti.extEulerNumericalPairing_nondegenerate` records the resulting two-sided
  nondegeneracy.
* `TauCeti.extEulerNumericalPairing_equiv_equiv`: those identifications preserve the numerical
  pairing.

The q-Euler counterpart is in
`TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Numerical`.

## References

The Ext-Euler construction follows Weibel, *An Introduction to Homological Algebra*, Sections
2.4--2.7, and its nonsymmetric numerical quotient follows Dancso--Licata, *Koszul algebras and
flow lattices*, Section 3.1. No formalization is copied or vendored here; the two constructions
are combined through the existing Tau Ceti APIs.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w w' v v' u u' t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C] [LocallySmall.{w} C]

variable {P Q : ObjectProperty C}

section Definitions

variable [P.EssentiallySmall.{w}] [Q.EssentiallySmall.{w}]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

variable (hP : (ExactStructure.abelian C).IsExtensionClosed P)
  (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
  (h : IsEulerAdmissibleOn.{w} k P Q)

/-- The ordinary Ext-Euler pairing on exact Grothendieck groups, regarded as a bilinear map over
`ℤ` so that it can be fed to the numerical-quotient construction. -/
noncomputable def extEulerBilinear :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP) →ₗ[ℤ]
      ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →ₗ[ℤ] ℤ :=
  (extEulerPairing hP hQ h).toIntLinearMap₂

@[simp]
theorem extEulerBilinear_apply
    (x : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP))
    (y : ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)) :
    extEulerBilinear hP hQ h x y = extEulerPairing hP hQ h x y :=
  (extEulerPairing hP hQ h).toIntLinearMap₂_apply x y

/-- The left numerical quotient of the first exact Grothendieck group for the Ext-Euler pairing. -/
abbrev ExtEulerLeftNumericalQuotient :=
  LeftNumericalQuotient (extEulerBilinear hP hQ h)

/-- The right numerical quotient of the second exact Grothendieck group for the Ext-Euler
pairing. -/
abbrev ExtEulerRightNumericalQuotient :=
  RightNumericalQuotient (extEulerBilinear hP hQ h)

/-- The quotient map from the first exact Grothendieck group to its Ext-Euler numerical quotient. -/
noncomputable def extEulerLeftNumericalQuotientMk :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP) →ₗ[ℤ]
      ExtEulerLeftNumericalQuotient hP hQ h :=
  leftNumericalQuotientMk (extEulerBilinear hP hQ h)

/-- The quotient map from the second exact Grothendieck group to its Ext-Euler numerical
quotient. -/
noncomputable def extEulerRightNumericalQuotientMk :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →ₗ[ℤ]
      ExtEulerRightNumericalQuotient hP hQ h :=
  rightNumericalQuotientMk (extEulerBilinear hP hQ h)

/-- The left radical of the Ext-Euler pairing, characterized by vanishing against every class on
the right. -/
theorem mem_extEulerLeftRadical_iff
    (x : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP)) :
    x ∈ leftRadical (extEulerBilinear hP hQ h) ↔
      ∀ y, extEulerPairing hP hQ h x y = 0 := by
  simp only [mem_leftRadical_iff, extEulerBilinear_apply]

/-- The right radical of the Ext-Euler pairing, characterized by vanishing against every class on
the left. -/
theorem mem_extEulerRightRadical_iff
    (y : ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)) :
    y ∈ rightRadical (extEulerBilinear hP hQ h) ↔
      ∀ x, extEulerPairing hP hQ h x y = 0 := by
  simp only [mem_rightRadical_iff, extEulerBilinear_apply]

/-- The one-sided pairing after quotienting the left exact Grothendieck group. -/
noncomputable def extEulerLeftNumericalPairing :
    ExtEulerLeftNumericalQuotient hP hQ h →ₗ[ℤ]
      ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →ₗ[ℤ] ℤ :=
  leftNumericalPairing (extEulerBilinear hP hQ h)

/-- The one-sided pairing after quotienting the right exact Grothendieck group. -/
noncomputable def extEulerRightNumericalPairing :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP) →ₗ[ℤ]
      ExtEulerRightNumericalQuotient hP hQ h →ₗ[ℤ] ℤ :=
  rightNumericalPairing (extEulerBilinear hP hQ h)

/-- The Ext-Euler pairing between both numerical Grothendieck groups. -/
noncomputable def extEulerNumericalPairing :
    ExtEulerLeftNumericalQuotient hP hQ h →ₗ[ℤ]
      ExtEulerRightNumericalQuotient hP hQ h →ₗ[ℤ] ℤ :=
  numericalPairing (extEulerBilinear hP hQ h)

end Definitions

section Pairing

variable [P.EssentiallySmall.{w}] [Q.EssentiallySmall.{w}]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

variable (hP : (ExactStructure.abelian C).IsExtensionClosed P)
  (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
  (h : IsEulerAdmissibleOn.{w} k P Q)

/-- The left Ext-Euler numerical pairing evaluates on a quotient representative as the descended
Ext-Euler pairing. -/
@[simp]
theorem extEulerLeftNumericalPairing_mk
    (x : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP))
    (y : ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)) :
    extEulerLeftNumericalPairing hP hQ h
        (extEulerLeftNumericalQuotientMk hP hQ h x) y =
      extEulerPairing hP hQ h x y := by
  rw [extEulerLeftNumericalPairing, extEulerLeftNumericalQuotientMk,
    leftNumericalPairing_mk, extEulerBilinear_apply]

/-- The right Ext-Euler numerical pairing evaluates on a quotient representative as the descended
Ext-Euler pairing. -/
@[simp]
theorem extEulerRightNumericalPairing_mk
    (x : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP))
    (y : ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)) :
    extEulerRightNumericalPairing hP hQ h x
        (extEulerRightNumericalQuotientMk hP hQ h y) =
      extEulerPairing hP hQ h x y := by
  rw [extEulerRightNumericalPairing, extEulerRightNumericalQuotientMk,
    rightNumericalPairing_mk, extEulerBilinear_apply]

/-- The Ext-Euler numerical pairing evaluates on two quotient representatives as the descended
Ext-Euler pairing. -/
@[simp]
theorem extEulerNumericalPairing_mk (x : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP))
    (y : ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)) :
    extEulerNumericalPairing hP hQ h
        (extEulerLeftNumericalQuotientMk hP hQ h x)
        (extEulerRightNumericalQuotientMk hP hQ h y) =
      extEulerPairing hP hQ h x y := by
  rw [extEulerNumericalPairing, extEulerLeftNumericalQuotientMk,
    extEulerRightNumericalQuotientMk, numericalPairing_mk, extEulerBilinear_apply]

/-- The Ext-Euler numerical pairing evaluates on classes of objects as the ordinary Ext-Euler
characteristic. -/
theorem extEulerNumericalPairing_of_of (X : P.FullSubcategory) (Y : Q.FullSubcategory) :
    extEulerNumericalPairing hP hQ h
        (extEulerLeftNumericalQuotientMk hP hQ h (ExactK0.of X))
        (extEulerRightNumericalQuotientMk hP hQ h (ExactK0.of Y)) =
      extEuler.{w} k (h.isEulerAdmissible X.property Y.property) := by
  rw [extEulerNumericalPairing_mk, extEulerPairing_of_of]

/-- The left numerical Ext-Euler pairing separates its left argument. -/
theorem extEulerLeftNumericalPairing_separatingLeft :
    (extEulerLeftNumericalPairing hP hQ h).SeparatingLeft :=
  leftNumericalPairing_separatingLeft (extEulerBilinear hP hQ h)

/-- The right numerical Ext-Euler pairing separates its right argument. -/
theorem extEulerRightNumericalPairing_separatingRight :
    (extEulerRightNumericalPairing hP hQ h).SeparatingRight :=
  rightNumericalPairing_separatingRight (extEulerBilinear hP hQ h)

/-- Quotienting by both Ext-Euler radicals makes the ordinary numerical pairing nondegenerate. -/
theorem extEulerNumericalPairing_nondegenerate :
    (extEulerNumericalPairing hP hQ h).Nondegenerate :=
  numericalPairing_nondegenerate (extEulerBilinear hP hQ h)

/-- The Ext-Euler numerical pairing is the unique bilinear pairing whose representative values are
the descended Ext-Euler values. -/
theorem extEulerNumericalPairing_unique
    (c : ExtEulerLeftNumericalQuotient hP hQ h →ₗ[ℤ]
      ExtEulerRightNumericalQuotient hP hQ h →ₗ[ℤ] ℤ)
    (hc : ∀ x y, c (extEulerLeftNumericalQuotientMk hP hQ h x)
        (extEulerRightNumericalQuotientMk hP hQ h y) = extEulerPairing hP hQ h x y) :
    c = extEulerNumericalPairing hP hQ h := by
  apply numericalPairing_unique (extEulerBilinear hP hQ h) c
  intro x y
  simpa only [extEulerLeftNumericalQuotientMk, extEulerRightNumericalQuotientMk,
    extEulerBilinear_apply] using hc x y

end Pairing

section Functoriality

/-! ### Invariance under exact functors

An exact functor `F : C ⥤ D` which carries `P` and `Q` into `P'` and `Q'` and is bijective on the
`Ext` groups of every pair in `P × Q` intertwines the two Ext-Euler pairings
(`TauCeti.extEulerPairing_map_map`). If moreover every object of `P'` and of `Q'` is isomorphic to
the image of an object of `P`, respectively `Q`, then the induced maps of exact `K₀` are
surjective, and the numerical Grothendieck groups on both sides are identified. The maps of exact
`K₀` themselves need not be injective: bijectivity on `Ext` is only required between `P` and `Q`,
so the restriction of `F` to `P` need not be fully faithful. -/

variable {D : Type u'} [Category.{v'} D] [Abelian D] [Linear k D] [HasExt.{w'} D]
  [LocallySmall.{w'} D]
  (F : C ⥤ D) [F.Additive] [F.Linear k] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [P.EssentiallySmall.{w}] [Q.EssentiallySmall.{w}]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]
  {P' Q' : ObjectProperty D} [P'.EssentiallySmall.{w'}] [Q'.EssentiallySmall.{w'}]
  [P'.ContainsZero] [P'.IsClosedUnderBinaryProducts]
  [Q'.ContainsZero] [Q'.IsClosedUnderBinaryProducts]
  (hP : (ExactStructure.abelian C).IsExtensionClosed P)
  (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
  (hP' : (ExactStructure.abelian D).IsExtensionClosed P')
  (hQ' : (ExactStructure.abelian D).IsExtensionClosed Q')
  (h : IsEulerAdmissibleOn.{w} k P Q) (h' : IsEulerAdmissibleOn.{w'} k P' Q')
  (hFP : ∀ ⦃X⦄, P X → P' (F.obj X)) (hFQ : ∀ ⦃Y⦄, Q Y → Q' (F.obj Y))
  (hF : ∀ ⦃X Y⦄, P X → Q Y → ∀ n, Function.Bijective (F.mapExtAddHom.{w, w'} X Y n))
  (hP'F : P' ≤ P.map F) (hQ'F : Q' ≤ Q.map F)

/-- The `ℤ`-linear map of exact `K₀` induced by `F` on the left subcategories. -/
private noncomputable abbrev extEulerLeftK0Map :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP) →ₗ[ℤ]
      ExactK0 ((ExactStructure.abelian D).fullSubcategory P' hP') :=
  (ExactK0.map (P'.lift (P.ι ⋙ F) fun X ↦ hFP X.property)
    ((ExactStructure.abelian C).isConflationExact_lift hP hP' F
      (ExactStructure.isConflationExact_abelian F) fun X ↦ hFP X.property)).toIntLinearMap

/-- The `ℤ`-linear map of exact `K₀` induced by `F` on the right subcategories. -/
private noncomputable abbrev extEulerRightK0Map :
    ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ) →ₗ[ℤ]
      ExactK0 ((ExactStructure.abelian D).fullSubcategory Q' hQ') :=
  (ExactK0.map (Q'.lift (Q.ι ⋙ F) fun Y ↦ hFQ Y.property)
    ((ExactStructure.abelian C).isConflationExact_lift hQ hQ' F
      (ExactStructure.isConflationExact_abelian F) fun Y ↦ hFQ Y.property)).toIntLinearMap

omit [HasExt C] [HasExt D] in
include hP'F in
private theorem extEulerLeftK0Map_surjective :
    Function.Surjective (extEulerLeftK0Map F hP hP' hFP) := by
  rw [AddMonoidHom.coe_toIntLinearMap]
  exact ExactK0.map_lift_surjective F hP hP' (ExactStructure.isConflationExact_abelian F)
    (fun X ↦ hFP X.property) hP'F

omit [HasExt C] [HasExt D] in
include hQ'F in
private theorem extEulerRightK0Map_surjective :
    Function.Surjective (extEulerRightK0Map F hQ hQ' hFQ) := by
  rw [AddMonoidHom.coe_toIntLinearMap]
  exact ExactK0.map_lift_surjective F hQ hQ' (ExactStructure.isConflationExact_abelian F)
    (fun Y ↦ hFQ Y.property) hQ'F

include hF in
/-- The maps of exact `K₀` induced by `F` preserve the integer-bilinear Ext-Euler forms. -/
private theorem extEulerBilinear_map_map
    (x : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP))
    (y : ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)) :
    extEulerBilinear hP' hQ' h' (extEulerLeftK0Map F hP hP' hFP x)
        (extEulerRightK0Map F hQ hQ' hFQ y) =
      extEulerBilinear hP hQ h x y := by
  simp only [AddMonoidHom.coe_toIntLinearMap, extEulerBilinear_apply]
  exact extEulerPairing_map_map F hP hQ hP' hQ' h' hFP hFQ hF x y

/-- **Invariance of the left numerical Grothendieck group.** An exact functor which is bijective
on `Ext` between `P` and `Q`, and whose images of `P` and `Q` exhaust `P'` and `Q'` up to
isomorphism, identifies the left Ext-Euler numerical quotients. -/
noncomputable def extEulerLeftNumericalEquiv :
    ExtEulerLeftNumericalQuotient hP hQ h ≃ₗ[ℤ] ExtEulerLeftNumericalQuotient hP' hQ' h' :=
  leftNumericalEquiv (extEulerBilinear hP hQ h) (extEulerBilinear hP' hQ' h')
    (extEulerLeftK0Map F hP hP' hFP) (extEulerRightK0Map F hQ hQ' hFQ)
    (extEulerLeftK0Map_surjective F hP hP' hFP hP'F)
    (extEulerRightK0Map_surjective F hQ hQ' hFQ hQ'F)
    (extEulerBilinear_map_map F hP hQ hP' hQ' h h' hFP hFQ hF)

/-- **Invariance of the right numerical Grothendieck group.** An exact functor which is bijective
on `Ext` between `P` and `Q`, and whose images of `P` and `Q` exhaust `P'` and `Q'` up to
isomorphism, identifies the right Ext-Euler numerical quotients. -/
noncomputable def extEulerRightNumericalEquiv :
    ExtEulerRightNumericalQuotient hP hQ h ≃ₗ[ℤ] ExtEulerRightNumericalQuotient hP' hQ' h' :=
  rightNumericalEquiv (extEulerBilinear hP hQ h) (extEulerBilinear hP' hQ' h')
    (extEulerLeftK0Map F hP hP' hFP) (extEulerRightK0Map F hQ hQ' hFQ)
    (extEulerLeftK0Map_surjective F hP hP' hFP hP'F)
    (extEulerRightK0Map_surjective F hQ hQ' hFQ hQ'F)
    (extEulerBilinear_map_map F hP hQ hP' hQ' h h' hFP hFQ hF)

/-- The left numerical equivalence sends the class of `x` to the class of its image under the map
of exact `K₀` induced by `F`. -/
@[simp]
theorem extEulerLeftNumericalEquiv_mk
    (x : ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP)) :
    extEulerLeftNumericalEquiv F hP hQ hP' hQ' h h' hFP hFQ hF hP'F hQ'F
        (extEulerLeftNumericalQuotientMk hP hQ h x) =
      extEulerLeftNumericalQuotientMk hP' hQ' h'
        (ExactK0.map (P'.lift (P.ι ⋙ F) fun X ↦ hFP X.property)
          ((ExactStructure.abelian C).isConflationExact_lift hP hP' F
            (ExactStructure.isConflationExact_abelian F) fun X ↦ hFP X.property) x) := by
  rw [extEulerLeftNumericalEquiv, extEulerLeftNumericalQuotientMk,
    extEulerLeftNumericalQuotientMk, leftNumericalEquiv_mk, AddMonoidHom.coe_toIntLinearMap]

/-- The right numerical equivalence sends the class of `y` to the class of its image under the map
of exact `K₀` induced by `F`. -/
@[simp]
theorem extEulerRightNumericalEquiv_mk
    (y : ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)) :
    extEulerRightNumericalEquiv F hP hQ hP' hQ' h h' hFP hFQ hF hP'F hQ'F
        (extEulerRightNumericalQuotientMk hP hQ h y) =
      extEulerRightNumericalQuotientMk hP' hQ' h'
        (ExactK0.map (Q'.lift (Q.ι ⋙ F) fun Y ↦ hFQ Y.property)
          ((ExactStructure.abelian C).isConflationExact_lift hQ hQ' F
            (ExactStructure.isConflationExact_abelian F) fun Y ↦ hFQ Y.property) y) := by
  rw [extEulerRightNumericalEquiv, extEulerRightNumericalQuotientMk,
    extEulerRightNumericalQuotientMk, rightNumericalEquiv_mk, AddMonoidHom.coe_toIntLinearMap]

/-- The two numerical equivalences induced by `F` preserve the Ext-Euler numerical pairing. -/
theorem extEulerNumericalPairing_equiv_equiv
    (x : ExtEulerLeftNumericalQuotient hP hQ h) (y : ExtEulerRightNumericalQuotient hP hQ h) :
    extEulerNumericalPairing hP' hQ' h'
        (extEulerLeftNumericalEquiv F hP hQ hP' hQ' h h' hFP hFQ hF hP'F hQ'F x)
        (extEulerRightNumericalEquiv F hP hQ hP' hQ' h h' hFP hFQ hF hP'F hQ'F y) =
      extEulerNumericalPairing hP hQ h x y := by
  rw [extEulerNumericalPairing, extEulerNumericalPairing, extEulerLeftNumericalEquiv,
    extEulerRightNumericalEquiv, numericalPairing_equiv_equiv]

end Functoriality

end TauCeti
