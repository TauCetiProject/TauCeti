/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Geometrically.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import TauCeti.RingTheory.Idempotents.Connected.Algebraic

/-!
# Constant global functions without a rational point

An integral scheme universally closed over a field has global functions integral over that
field. If the ground field is integrally closed in the function field, those functions are
constants. Geometric integrality supplies this constant-field condition, without a rational
point, a perfectness assumption, or a finite-type assumption.

More generally, a universally closed quasi-separated scheme that is geometrically reduced and
geometrically connected has only constant global functions, even if it is reducible. This
covers the nodal curves whose components must not be treated as a single integral scheme.
Over an algebraically closed field, reducedness and connectedness suffice: the integral algebra
of global functions is a field because it has no nontrivial idempotents. Flat base change and
faithfully flat descent give the result over an arbitrary field.

The canonical map from the ground field to global sections is bijective. This is the
normalization needed for the formula `χ(𝒪_X) = 1 - g` on proper geometrically reduced and
geometrically connected curves, and for the universal structure-sheaf pushforward equality.

Mathlib's `isIntegral_appTop_of_universallyClosed` gives integrality of global functions.
The exact constant-field condition is available as
`isIntegrallyClosedIn_functionField_of_geometricallyIntegral`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Section 5.
* The Stacks Project, Section 33.9, *Geometrically integral schemes* (global functions of
  proper geometrically reduced and geometrically connected schemes).

The descent uses Mathlib's `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` and
`RingHom.FaithfullyFlat.codescendsAlong_bijective`.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) (k : Type u) [Field k] [X.Over (Spec (.of k))]
  [UniversallyClosed (X ↘ Spec (.of k))]

/-- Global functions on a universally closed scheme over an affine base are integral over
the base ring. -/
theorem Modules.isIntegral_baseRingToGlobalSections (X : Scheme.{u}) (R : Type u)
    [CommRing R] [X.Over (Spec (.of R))] [UniversallyClosed (X ↘ Spec (.of R))] :
    (Modules.baseRingToGlobalSections R X).IsIntegral := by
  have hmap : Modules.baseRingToGlobalSections R X =
      (X ↘ Spec (.of R)).appTop.hom.comp
        (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.toRingHom := by
    ext c
    exact Modules.baseRingToGlobalSections_apply R X c
  rw [hmap]
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed (X ↘ Spec (.of R))

variable [IsIntegral X]

/-- Global functions on a universally closed integral scheme are constants if the ground field
is integrally closed in its function field. No rational point is required. -/
theorem baseRingToGlobalSections_bijective_of_isIntegrallyClosedIn
    (hk : IsIntegrallyClosedIn k X.functionField) :
    Function.Bijective (Modules.baseRingToGlobalSections k X) := by
  let _ : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  let _ : Algebra k Γ(X, ⊤) := (Modules.baseRingToGlobalSections k X).toAlgebra
  have : IsIntegrallyClosedIn k X.functionField := hk
  have hint := Modules.isIntegral_baseRingToGlobalSections X k
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

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) (k : Type u) [Field k] [X.Over (Spec (.of k))]
  [UniversallyClosed (X ↘ Spec (.of k))]

include k in
/-- The global functions on a reduced connected scheme universally closed over a field form
a field, even when the scheme is reducible. -/
theorem isField_globalSections_of_isReduced_of_connectedSpace
    [IsReduced X] [ConnectedSpace X] : IsField Γ(X, ⊤) := by
  have : CompactSpace X := compactSpace_of_universallyClosed (X ↘ Spec (.of k))
  have : PreconnectedSpace (PrimeSpectrum Γ(X, ⊤)) :=
    X.toSpecΓ.denseRange.preconnectedSpace X.toSpecΓ.continuous
  have : ConnectedSpace (PrimeSpectrum Γ(X, ⊤)) := ⟨inferInstance⟩
  let _ : Algebra k Γ(X, ⊤) := (Modules.baseRingToGlobalSections k X).toAlgebra
  have : Algebra.IsIntegral k Γ(X, ⊤) :=
    ⟨Modules.isIntegral_baseRingToGlobalSections X k⟩
  exact TauCeti.isField_of_isAlgebraic_of_isReduced_of_connectedSpace k Γ(X, ⊤)

/-- Over an algebraically closed field, a reduced connected universally closed scheme has
only constant global functions. -/
theorem appTop_bijective_of_isAlgClosed_of_isReduced_of_connectedSpace
    [IsAlgClosed k] [IsReduced X] [ConnectedSpace X] :
    Function.Bijective (X ↘ Spec (.of k)).appTop := by
  let _ := (X.isField_globalSections_of_isReduced_of_connectedSpace k).toField
  let _ : Algebra k Γ(X, ⊤) := (Modules.baseRingToGlobalSections k X).toAlgebra
  have : Algebra.IsIntegral k Γ(X, ⊤) :=
    ⟨Modules.isIntegral_baseRingToGlobalSections X k⟩
  have h : Function.Bijective (Modules.baseRingToGlobalSections k X) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))
  have hcomp : (Modules.baseRingToGlobalSections k X) =
      (X ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom := by
    ext c
    exact Modules.baseRingToGlobalSections_apply k X c
  rw [hcomp] at h
  exact (Function.Bijective.of_comp_iff _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)).mp h

/-- A universally closed quasi-separated geometrically reduced and geometrically connected
scheme over any field has only constant global functions. No irreducibility or rational point
is required. -/
theorem appTop_bijective_of_geometricallyReduced_of_geometricallyConnected
    [QuasiSeparated (X ↘ Spec (.of k))] [GeometricallyReduced (X ↘ Spec (.of k))]
    [GeometricallyConnected (X ↘ Spec (.of k))] :
    Function.Bijective (X ↘ Spec (.of k)).appTop := by
  let L := AlgebraicClosure k
  let g := Spec.algebraMap k L
  let f := X ↘ Spec (.of k)
  let Y := Limits.pullback f g
  let _ : Y.Over (Spec (.of L)) := ⟨Limits.pullback.snd f g⟩
  have : IsReduced Y :=
    GeometricallyReduced.geometrically_isReduced g _ _ (.of_hasPullback f g)
  have : ConnectedSpace Y :=
    GeometricallyConnected.geometrically_connectedSpace g _ _ (.of_hasPullback f g)
  have : UniversallyClosed (Y ↘ Spec (.of L)) :=
    inferInstanceAs (UniversallyClosed (Limits.pullback.snd f g))
  have hY := Y.appTop_bijective_of_isAlgClosed_of_isReduced_of_connectedSpace L
  have : CompactSpace X := compactSpace_of_universallyClosed f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hpush : IsPushout f.appTop g.appTop
      (Limits.pullback.fst f g).appTop (Limits.pullback.snd f g).appTop := by
    have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
      (IsPullback.of_hasPullback f g) (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
      (by simp) (by simp) (by simp) (isAffineOpen_top _) (isAffineOpen_top _)
      isCompact_univ isQuasiSeparated_univ
    -- State the top-open specialization explicitly: simplification cannot match the dependent
    -- open argument of appLE_eq_app through the chosen pullback object.
    have happ {A B : Scheme.{u}} (i : A ⟶ B) :
        i.appLE ⊤ ⊤ (by simp) = i.appTop := i.appLE_eq_app
    simpa only [happ] using (isIso_pushoutSection_iff _ _ _ _).mp h
  -- Flat base change identifies this square of global sections with a pushout. Descent along
  -- the faithfully flat field extension reflects bijectivity of the structure map.
  let _ := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField k) |>.toField
  algebraize [f.appTop.hom, g.appTop.hom, (Limits.pullback.fst f g).appTop.hom,
    (Limits.pullback.snd f g).appTop.hom, (Limits.pullback.fst f g).appTop.hom.comp f.appTop.hom]
  have : IsScalarTower Γ(Spec (.of k), ⊤) Γ(Spec (.of L), ⊤) Γ(Y, ⊤) :=
    .of_algebraMap_eq fun x ↦ congr($(hpush.w).hom x)
  have : Algebra.IsPushout Γ(Spec (.of k), ⊤) Γ(X, ⊤) Γ(Spec (.of L), ⊤) Γ(Y, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp hpush
  exact RingHom.FaithfullyFlat.codescendsAlong_bijective
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) hY

/-- The canonical map from the ground field to the global functions of a universally closed
quasi-separated geometrically reduced and geometrically connected scheme is bijective. -/
theorem baseRingToGlobalSections_bijective_of_geometricallyReduced_of_geometricallyConnected
    [QuasiSeparated (X ↘ Spec (.of k))] [GeometricallyReduced (X ↘ Spec (.of k))]
    [GeometricallyConnected (X ↘ Spec (.of k))] :
    Function.Bijective (Modules.baseRingToGlobalSections k X) := by
  have hmap : Modules.baseRingToGlobalSections k X =
      (X ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom := by
    ext c
    exact Modules.baseRingToGlobalSections_apply k X c
  rw [hmap]
  exact (X.appTop_bijective_of_geometricallyReduced_of_geometricallyConnected k).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)

end AlgebraicGeometry.Scheme
