/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
import TauCeti.RingTheory.Localization.Tower

/-!
# Complements on affine schemes

For an affine scheme `X`, Mathlib's `AlgebraicGeometry.Scheme.isoSpec` is the isomorphism
`X ≅ Spec Γ(X, ⊤)`. This file computes the map of global sections of its inverse: it is the
inverse of Mathlib's `AlgebraicGeometry.Scheme.ΓSpecIso`. It is the scheme-level companion of
Mathlib's `AlgebraicGeometry.IsAffineOpen.isoSpec_inv_appTop` for an affine open.

It also shows that for a compatible tower `R → B ↪ R_a`, localizing `B` at `a` gives `R_a`,
so `Spec B ⟶ Spec R` is an isomorphism over the basic open `D(a)`. The map from `R` need not
be injective. This is the local reason why an affine blowup changes nothing away from its center.

## Main results

* `AlgebraicGeometry.Scheme.isoSpec_inv_appTop`: the global sections of `X.isoSpec.inv` are
  `(Scheme.ΓSpecIso Γ(X, ⊤)).inv`.
* `AlgebraicGeometry.isIso_SpecMap_morphismRestrict_basicOpen_of_injective`: for an `R`-algebra `B`
  embedded in a localization of `R` away from `a`, the morphism `Spec B ⟶ Spec R` restricts to an
  isomorphism over `D(a)`.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The global sections of the inverse of `X ≅ Spec Γ(X, ⊤)`, for an affine scheme `X`. -/
theorem Scheme.isoSpec_inv_appTop (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  have h : X.isoSpec.inv.appTop ≫ X.isoSpec.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rw [← Iso.comp_hom_eq_id]
  simpa [Scheme.isoSpec] using h

/-- **`Spec` of an intermediate ring of a localization.** Let `S` be a localization of `R` away
from `a`, and let `B` be an `R`-algebra whose map to `S` is injective, for instance an
`R`-subalgebra of `S`. Then `Spec B ⟶ Spec R` restricts to an isomorphism over the basic open
`D(a)`. -/
theorem isIso_SpecMap_morphismRestrict_basicOpen_of_injective {R B : Type u} {S : Type*}
    [CommRing R] [CommRing B] [CommSemiring S] [Algebra R B] [Algebra B S] [Algebra R S]
    [IsScalarTower R B S] (a : R) [IsLocalization.Away a S]
    (h : Function.Injective (algebraMap B S)) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R B)) ∣_ PrimeSpectrum.basicOpen a) := by
  -- Over `D(a)`, the morphism is `Spec` of the isomorphism `R_a ≅ B_a`.
  have : IsIso (CommRingCat.ofHom (Localization.awayMap (algebraMap R B) a)) :=
    (RingEquiv.ofBijective _
      (IsLocalization.Away.bijective_awayMap_of_injective a h)).toCommRingCatIso.isIso_hom
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (algebraMap R B)) a)).mpr
    (inferInstanceAs (IsIso (Spec.map _)))

end AlgebraicGeometry
