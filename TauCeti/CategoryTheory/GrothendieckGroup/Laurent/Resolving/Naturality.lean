/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent.Resolving.Basic

/-!
# Naturality of the graded resolving-subcategory resolution theorem

A graded conflation-exact functor carrying one shift-stable resolving property into another
commutes with the resolution equivalences as a map of Laurent modules. Both the inclusions and
the inverse Euler-class maps are natural. In particular, applying the restricted functor to the
alternating class of any finite resolution gives the alternating class of any resolution of the
image object; no functorial choice of resolutions or projective lifting hypothesis is needed.

A graded exact equivalence identifying the resolving properties restricts to their induced
graded exact structures and intertwines the resolution equivalences in both directions. These
comparison squares allow graded resolution classes to be transported without choosing small
models or requiring definitional equality between their presentations.

## Main results

* `TauCeti.GradedExactStructure.IsResolving.map_comp_laurentResolutionEquiv` and
  `TauCeti.GradedExactStructure.IsResolving.map_comp_laurentResolutionEquiv_symm`: naturality
  of the forward and inverse resolution maps.
* `TauCeti.GradedExactStructure.IsResolving.map_foldAlternating`: transport of a resolution's
  alternating class, independently of the target resolution.
* `TauCeti.GradedExactStructure.IsResolving.mapEquiv_comp_laurentResolutionEquiv` and
  `TauCeti.GradedExactStructure.IsResolving.mapEquiv_comp_laurentResolutionEquiv_symm`:
  invariance under graded exact equivalences identifying the resolving properties.

## References

* Charles A. Weibel, *The K-book*, Chapter II, Theorem 7.6, for the resolution theorem.
* Zsuzsanna Dancso and Anthony Licata, *Koszul algebras and flow lattices*, Section 2.2,
  for the Laurent-module interpretation of graded Grothendieck groups.

The construction uses the resolution equivalence from
`TauCeti.GradedExactStructure.IsResolving.laurentResolutionEquiv` and Mathlib's
`CategoryTheory.Equivalence.congrFullSubcategory` for the restricted equivalence.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w w' v v' u u'

namespace GradedExactStructure.IsResolving

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]
  (E : GradedExactStructure C) (P : ObjectProperty C)
  [E.toExactStructure.IsResolving P]
  (hPshift : P.inverseImage E.shift.functor = P)
  (E' : GradedExactStructure D) (Q : ObjectProperty D)
  [E'.toExactStructure.IsResolving Q]
  (hQshift : Q.inverseImage E'.shift.functor = Q)

local instance : ObjectProperty.EssentiallySmall.{w} P :=
  ObjectProperty.EssentiallySmall.of_le (Q := ⊤) le_top

local instance : ObjectProperty.EssentiallySmall.{w'} Q :=
  ObjectProperty.EssentiallySmall.of_le (Q := ⊤) le_top

local notation "hP" =>
  (ExactStructure.IsResolving.isExtensionClosed (E := E.toExactStructure) (P := P))

local notation "hQ" =>
  (ExactStructure.IsResolving.isExtensionClosed (E := E'.toExactStructure) (P := Q))

section Functor

variable {F : C ⥤ D} [F.Additive] (hF : GradedConflationExact E E' F)
  (hPQ : ∀ X : P.FullSubcategory, Q (F.obj X.obj))

/-- A graded conflation-exact functor preserving resolving objects intertwines the forward
resolution equivalences. This is an equality of Laurent-linear maps, not only additive maps. -/
theorem map_comp_laurentResolutionEquiv :
    (LaurentK0.map hF).comp (laurentResolutionEquiv E P hPshift).toLinearMap =
      (laurentResolutionEquiv E' Q hQshift).toLinearMap.comp
        (LaurentK0.map (hF.lift E P hP hQ hPshift hQshift hPQ)) := by
  apply LaurentK0.hom_ext
  intro X
  simp

/-- Applying a graded conflation-exact functor to a resolution Euler class is the inverse
resolution comparison after applying the ambient functor. -/
theorem map_comp_laurentResolutionEquiv_symm :
    (LaurentK0.map (hF.lift E P hP hQ hPshift hQshift hPQ)).comp
        (laurentResolutionEquiv E P hPshift).symm.toLinearMap =
      (laurentResolutionEquiv E' Q hQshift).symm.toLinearMap.comp (LaurentK0.map hF) := by
  ext x
  apply (laurentResolutionEquiv E' Q hQshift).injective
  have h := DFunLike.congr_fun
    (map_comp_laurentResolutionEquiv E P hPshift E' Q hQshift hF hPQ)
    ((laurentResolutionEquiv E P hPshift).symm x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using h.symm

/-- The alternating class of any finite resolution transports to that of any resolution of the
image object. Resolving objects need not be projective and the two resolutions need not have
the same length or be related by a chain map. -/
theorem map_foldAlternating {X : C}
    (r : E.toExactStructure.FiniteResolution P X)
    (s : E'.toExactStructure.FiniteResolution Q (F.obj X)) :
    LaurentK0.map (hF.lift E P hP hQ hPshift hQshift hPQ)
        (r.foldAlternating fun Z hZ ↦
          LaurentK0.of (E.fullSubcategory P hP hPshift) ⟨Z, hZ⟩) =
      s.foldAlternating fun Z hZ ↦
        LaurentK0.of (E'.fullSubcategory Q hQ hQshift) ⟨Z, hZ⟩ := by
  rw [← laurentResolutionEquiv_symm_of E P hPshift r,
    ← laurentResolutionEquiv_symm_of E' Q hQshift s]
  have h := DFunLike.congr_fun
    (map_comp_laurentResolutionEquiv_symm E P hPshift E' Q hQshift hF hPQ)
    (LaurentK0.of E X)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LaurentK0.map_of] using h

end Functor

section Equivalence

variable (e : GradedExactEquiv E E') (h : Q.inverseImage e.equiv.functor = P)

/-- A graded exact equivalence identifying the resolving properties intertwines their
resolution equivalences and the Laurent-linear equivalences induced on the ambient groups. -/
theorem mapEquiv_comp_laurentResolutionEquiv :
    (LaurentK0.mapEquiv e).toLinearMap.comp
        (laurentResolutionEquiv E P hPshift).toLinearMap =
      (laurentResolutionEquiv E' Q hQshift).toLinearMap.comp
        (LaurentK0.mapEquiv
          (e.congrFullSubcategory hP hQ hPshift hQshift h)).toLinearMap := by
  apply LaurentK0.hom_ext
  intro X
  simp

/-- The inverse resolution comparisons are invariant under graded exact equivalences
identifying the resolving properties. -/
theorem mapEquiv_comp_laurentResolutionEquiv_symm :
    (LaurentK0.mapEquiv
        (e.congrFullSubcategory hP hQ hPshift hQshift h)).toLinearMap.comp
        (laurentResolutionEquiv E P hPshift).symm.toLinearMap =
      (laurentResolutionEquiv E' Q hQshift).symm.toLinearMap.comp
        (LaurentK0.mapEquiv e).toLinearMap := by
  ext x
  apply (laurentResolutionEquiv E' Q hQshift).injective
  have h' := DFunLike.congr_fun
    (mapEquiv_comp_laurentResolutionEquiv E P hPshift E' Q hQshift e h)
    ((laurentResolutionEquiv E P hPshift).symm x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using h'.symm

end Equivalence

end GradedExactStructure.IsResolving

end TauCeti
