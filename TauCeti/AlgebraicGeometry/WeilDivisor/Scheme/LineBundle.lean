/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Class
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.LocalTriviality

/-!
# Line-bundle classes attached to Weil divisors

On a Noetherian integral scheme of dimension at most one whose codimension-one local rings are
discrete valuation rings, every Weil divisor `D` is locally principal. Its sheaf `𝓞_X(D)` is
therefore a line bundle. Linearly equivalent divisors have isomorphic sheaves, so this
construction descends from Weil divisors to the divisor class group.

## Main declarations

* `SchemeWeilDivisor.toInvertibleSheaf` packages `𝓞_X(D)` as an invertible sheaf;
* `SchemeWeilDivisor.toLineBundleClass` is its isomorphism class;
* `SchemeWeilDivisor.classGroupToLineBundleClass` is the induced map from the divisor class
  group to line-bundle classes.

This is the set-level divisor-to-line-bundle comparison. Proving compatibility with addition
and tensor product, and proving that the comparison is bijective, require further structure.
-/

public section

open AlgebraicGeometry CategoryTheory Order

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

noncomputable section

variable (hX : ∀ y : X, coheight y ≤ 1)

/-- The invertible sheaf `𝓞_X(D)` associated to a Weil divisor on a Noetherian integral
scheme of dimension at most one whose codimension-one local rings are DVRs. -/
def toInvertibleSheaf (D : SchemeWeilDivisor X) : InvertibleSheaf X :=
  (isLocallyPrincipal_of_forall_coheight_le_one hX D).toInvertibleSheaf hX

/-- The underlying sheaf of `SchemeWeilDivisor.toInvertibleSheaf` is `𝓞_X(D)`. -/
@[simp]
lemma toInvertibleSheaf_obj (D : SchemeWeilDivisor X) :
    (toInvertibleSheaf hX D).obj = sheaf D :=
  IsLocallyPrincipal.toInvertibleSheaf_obj
    (isLocallyPrincipal_of_forall_coheight_le_one hX D) hX

/-- The isomorphism class of the line bundle `𝓞_X(D)` associated to a Weil divisor. -/
def toLineBundleClass (D : SchemeWeilDivisor X) : LineBundleClass X :=
  LineBundleClass.mk (toInvertibleSheaf hX D)

/-- Linearly equivalent Weil divisors determine the same line-bundle class. -/
theorem toLineBundleClass_eq_of_linearlyEquivalent {D E : SchemeWeilDivisor X}
    (hDE : (WeilDivisor.OrderSystem.ofScheme X).LinearlyEquivalent D E) :
    toLineBundleClass hX D = toLineBundleClass hX E := by
  change LineBundleClass.mk (toInvertibleSheaf hX D) =
    LineBundleClass.mk (toInvertibleSheaf hX E)
  rw [LineBundleClass.mk_eq_mk_iff]
  simpa only [toInvertibleSheaf_obj] using nonempty_iso_sheaf_of_linearlyEquivalent hDE

/-- The zero divisor determines the trivial line-bundle class. -/
@[simp]
lemma toLineBundleClass_zero :
    toLineBundleClass hX (0 : SchemeWeilDivisor X) = 1 := by
  change LineBundleClass.mk (toInvertibleSheaf hX 0) = 1
  rw [← LineBundleClass.mk_trivial, LineBundleClass.mk_eq_mk_iff]
  simpa only [toInvertibleSheaf_obj, InvertibleSheaf.trivial_obj] using
    ⟨(unitIsoSheafZero hX).symm ≪≫
      (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf).symm⟩

/-- A principal divisor determines the trivial line-bundle class. -/
@[simp]
lemma toLineBundleClass_principalDivisor (g : Additive X.functionFieldˣ) :
    toLineBundleClass hX
        ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g) = 1 := by
  rw [← toLineBundleClass_zero hX,
    ← zero_add ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor g)]
  exact toLineBundleClass_eq_of_linearlyEquivalent hX
    ((WeilDivisor.OrderSystem.ofScheme X).linearlyEquivalent_add_principalDivisor 0 g)

/-- The map from the divisor class group to isomorphism classes of line bundles which sends
the class of `D` to the class of `𝓞_X(D)`. -/
def classGroupToLineBundleClass :
    (WeilDivisor.OrderSystem.ofScheme X).ClassGroup → LineBundleClass X :=
  Quotient.lift (toLineBundleClass hX) fun D E hDE ↦ by
    apply toLineBundleClass_eq_of_linearlyEquivalent hX
    apply WeilDivisor.OrderSystem.LinearlyEquivalent.symm
    rw [WeilDivisor.OrderSystem.linearlyEquivalent_iff]
    simpa [sub_eq_add_neg, add_comm] using
      (QuotientAddGroup.leftRel_apply.mp hDE)

/-- The map from divisor classes to line-bundle classes sends the class of `D` to the class of
`𝓞_X(D)`. -/
@[simp]
lemma classGroupToLineBundleClass_divisorClass (D : SchemeWeilDivisor X) :
    classGroupToLineBundleClass hX
        ((WeilDivisor.OrderSystem.ofScheme X).divisorClass D) =
      toLineBundleClass hX D := by
  rw [WeilDivisor.OrderSystem.divisorClass_eq_mk']
  rfl

/-- The zero divisor class maps to the trivial line-bundle class. -/
@[simp]
lemma classGroupToLineBundleClass_zero :
    classGroupToLineBundleClass hX
        (0 : (WeilDivisor.OrderSystem.ofScheme X).ClassGroup) = 1 := by
  rw [← map_zero (WeilDivisor.OrderSystem.ofScheme X).divisorClass,
    classGroupToLineBundleClass_divisorClass, toLineBundleClass_zero]

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
