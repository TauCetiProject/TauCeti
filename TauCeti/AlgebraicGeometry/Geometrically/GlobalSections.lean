/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Geometrically.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Constant global functions without a rational point

An integral scheme universally closed over a field has global functions integral over that
field. If the ground field is integrally closed in the function field, those functions are
constants. Geometric integrality supplies this constant-field condition, without a rational
point, a perfectness assumption, or a finite-type assumption.

The canonical map from the ground field to global sections is bijective. This is the
normalization needed for the formula `χ(𝒪_X) = 1 - g` on geometrically integral proper curves.

The proof combines Mathlib's `isIntegral_appTop_of_universallyClosed` with
`isIntegrallyClosedIn_functionField_of_geometricallyIntegral`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Section 5.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) (k : Type u) [Field k] [X.Over (Spec (.of k))]
  [IsIntegral X] [UniversallyClosed (X ↘ Spec (.of k))]

/-- Global functions on a universally closed integral scheme are constants if the ground field
is integrally closed in its function field. No rational point is required. -/
theorem baseRingToGlobalSections_bijective_of_isIntegrallyClosedIn
    (hk : IsIntegrallyClosedIn k X.functionField) :
    Function.Bijective (Modules.baseRingToGlobalSections k X) := by
  let _ : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  let _ : Algebra k Γ(X, ⊤) := (Modules.baseRingToGlobalSections k X).toAlgebra
  have : IsIntegrallyClosedIn k X.functionField := hk
  have hint : (Modules.baseRingToGlobalSections k X).IsIntegral := by
    have hmap : Modules.baseRingToGlobalSections k X =
        (X ↘ Spec (.of k)).appTop.hom.comp
          (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.toRingHom := by
      ext c
      exact Modules.baseRingToGlobalSections_apply k X c
    rw [hmap]
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed (X ↘ Spec (.of k))
  let φ : Γ(X, ⊤) →ₐ[k] X.functionField :=
    { (X.germToFunctionField ⊤).hom with
      commutes' := fun c ↦ (X.baseRingToFunctionField_apply k c).symm }
  refine ⟨(Modules.baseRingToGlobalSections k X).injective, fun a ↦ ?_⟩
  have ha : _root_.IsIntegral k a := hint a
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (ha.map φ)
  exact ⟨c, (X.germToFunctionField_injective ⊤)
    ((φ.commutes c).trans hc)⟩

omit [IsIntegral X] in
/-- A universally closed geometrically integral scheme over any field has only constant global
functions. This holds even when it has no rational point. -/
theorem baseRingToGlobalSections_bijective_of_geometricallyIntegral
    [GeometricallyIntegral (X ↘ Spec (.of k))] :
    Function.Bijective (Modules.baseRingToGlobalSections k X) := by
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton (X ↘ Spec (.of k))
  exact X.baseRingToGlobalSections_bijective_of_isIntegrallyClosedIn k
    TauCeti.AlgebraicGeometry.isIntegrallyClosedIn_functionField_of_geometricallyIntegral

end AlgebraicGeometry.Scheme
