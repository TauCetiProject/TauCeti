/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import TauCeti.CategoryTheory.Abelian.FunctorCohomology.OpenSubfunctor
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Functors on rings that are proper over a ring

Let `Z : CommRingCat ⥤ Type*` be a functor on commutative rings with a map
`s : Z ⟶ h_D` to the functor `h_D = Hom(D, -)` corepresented by a ring `D`, so that every point
`z ∈ Z(C)` has a *structure map* `s(z) : D ⟶ C`. Then `Z` is *proper over `D`*
(`CategoryTheory.Functor.IsProperOver`) if

* its diagonal is closed (`CategoryTheory.Functor.IsSeparated` for the rings themselves): for all
  `x, y ∈ Z(C)` there is an ideal `I` of `C` such that a ring map `f : C ⟶ C'` makes the images of
  `x` and `y` in `Z(C')` agree exactly when `I ⊆ ker f`; and
* it satisfies the valuative criterion with one universal point: there are a ring `T` and a point
  `a ∈ Z(T)` such that for every algebraically closed field `K`, every valuation subring `O` of `K`
  and every point `z ∈ Z(K)` whose structure map sends `D` into `O`, some ring map `T ⟶ O` carries
  `a` to `z`, read in `Z(K)` through the inclusion `O ⊆ K`.

The conditions are modelled on the functor of points of a scheme proper over `Spec D`, whose
separatedness gives the closed diagonal, and whose universal point would be the point with values
in the product of the rings of a finite affine open cover, the valuative criterion of properness
supplying the factorisation through `O`; that example is not treated in this file.

## Main results

* `CategoryTheory.Functor.isProperOver_uliftCoyoneda_of_isIntegral`: for an integral ring map
  `D ⟶ B`, the functor corepresented by `B` is proper over `D`, with the identity of `B` as its
  universal point, because valuation rings are integrally closed.
* `CategoryTheory.Functor.IsProperOver.of_comp`: a functor proper over `E` through a map
  `E ⟶ D` is proper over `D`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Theorem II.4.7 (the valuative
  criterion of properness).
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/ProperBaseChange/PlaceSpace.lean` (declaration `New.Variety.IsProperOver`);
  Apache 2.0, Copyright 2026 Anthropic, PBC. The definition is adapted from this declaration.
-/

public section

open CategoryTheory Opposite

universe w u

namespace CategoryTheory.Functor

/-- A functor `Z` on commutative rings with a map `s : Z ⟶ h_D` to the functor corepresented by `D`
is *proper over `D`* if
(i) its diagonal is closed: for all `x, y ∈ Z(C)` there is an ideal `I` of `C` such that
`f : C ⟶ C'` makes `Z(f)(x) = Z(f)(y)` exactly when `I ⊆ ker f`; and
(ii) it satisfies a valuative criterion with one universal point: there are a ring `T` and
`a ∈ Z(T)` such that for every algebraically closed field `K`, every valuation subring `O` of `K`
and every `z ∈ Z(K)` whose structure map `s(z) : D ⟶ K` sends `D` into `O`, some ring map
`g : T ⟶ O` carries `a` to `z`, read in `Z(K)` through the inclusion `O ⊆ K`. -/
structure IsProperOver (Z : CommRingCat.{u} ⥤ Type (max w u)) {D : CommRingCat.{u}}
    (s : Z ⟶ uliftCoyoneda.{w}.obj (op D)) : Prop where
  /-- The diagonal of `Z` is closed. -/
  isSeparated : Z.IsSeparated (𝟭 CommRingCat.{u})
  /-- The valuative criterion with one universal point `a ∈ Z(T)`. -/
  exists_universal_valuative_lift : ∃ (T : CommRingCat.{u}) (a : Z.obj T),
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (O : ValuationSubring K)
      (z : Z.obj (CommRingCat.of K)),
        (∀ d : D, (ULift.down (s.app _ z) : D ⟶ CommRingCat.of K) d ∈ O) →
        ∃ g : T ⟶ CommRingCat.of O, Z.map (g ≫ CommRingCat.ofHom O.subtype) a = z

namespace IsProperOver

variable {Z : CommRingCat.{u} ⥤ Type (max w u)} {D E : CommRingCat.{u}}
  {s : Z ⟶ uliftCoyoneda.{w}.obj (op D)}

/-- A functor proper over `E` through a ring map `φ : E ⟶ D` is proper over `D`: a structure map
sending `D` into a valuation ring sends `E` into it as well. -/
lemma of_comp (φ : E ⟶ D) (h : Z.IsProperOver (s ≫ uliftCoyoneda.{w}.map φ.op)) :
    Z.IsProperOver s where
  isSeparated := h.isSeparated
  exists_universal_valuative_lift := by
    obtain ⟨T, a, ha⟩ := h.exists_universal_valuative_lift
    exact ⟨T, a, fun K _ _ O z hz ↦ ha K O z fun e ↦ hz (φ e)⟩

end IsProperOver

/-- If `φ : D ⟶ B` is an integral ring map, the functor corepresented by `B`, with the map to `h_D`
induced by `φ`, is proper over `D`. Its universal point is the identity of `B`: a ring map
`ψ : B ⟶ K` to a field sending `D` into a valuation subring `O` sends all of `B` into `O`, since
the elements of `B` are integral over `D` and `O` is integrally closed in `K`. -/
theorem isProperOver_uliftCoyoneda_of_isIntegral {D B : CommRingCat.{u}} (φ : D ⟶ B)
    (hφ : φ.hom.IsIntegral) :
    (uliftCoyoneda.{w}.obj (op B)).IsProperOver (uliftCoyoneda.{w}.map φ.op) where
  isSeparated :=
    ((CorepresentableBy.equivUliftCoyonedaIso _ B).symm (Iso.refl _)).isSeparated
  exists_universal_valuative_lift := by
    refine ⟨B, ⟨𝟙 B⟩, fun K _ _ O z hz ↦ ?_⟩
    obtain ⟨ψ : B ⟶ CommRingCat.of K⟩ := z
    -- The restriction `D ⟶ O` of `φ ≫ ψ`, through which the integrality of `B` is transported.
    let φ' : D →+* O := (ψ.hom.comp φ.hom).codRestrict O hz
    have hB (b : B) : ψ b ∈ O := by
      let := φ.hom.toAlgebra
      have hb : IsIntegral D b := hφ b
      have hint : IsIntegral O (ψ b) :=
        hb.map_of_comp_eq φ' ψ.hom (by ext; simp [φ', RingHom.algebraMap_toAlgebra])
      exact (Subring.isIntegrallyClosed_iff (S := O)).1 inferInstance hint
    refine ⟨CommRingCat.ofHom (ψ.hom.codRestrict O hB), ULift.ext ?_⟩
    exact CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl)

end CategoryTheory.Functor
