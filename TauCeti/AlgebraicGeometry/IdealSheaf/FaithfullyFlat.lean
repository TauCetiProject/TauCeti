/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.SchemeTheoreticallyDominant
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticallyDominant

/-!
# Inverse images of ideal sheaves along flat surjective morphisms

Let `g : Y ⟶ X` be a flat surjective morphism of schemes. Taking inverse images along `g` reflects
inclusion of ideal sheaves on `X` (`comap_le_comap_iff_of_flat_of_surjective`), so it is injective
(`comap_inj_of_flat_of_surjective`): two closed subschemes of `X`, for instance two effective
Cartier divisors, are equal as soon as their inverse images in `Y` are. This is the uniqueness
half of faithfully flat descent of closed subschemes, and it needs neither quasi-compactness of `g`
nor any finiteness hypothesis on the ideal sheaves.
Equalities of closed subschemes after a flat surjective base change, which is how scheme-theoretic
conditions such as Drinfeld level structures are stated, therefore already hold before it.

These are the flat surjective cases of the corresponding statements for morphisms all of whose
base changes are scheme-theoretically dominant
(`comap_le_comap_iff_of_universally_isSchemeTheoreticallyDominant` and
`comap_injective_of_universally_isSchemeTheoreticallyDominant`, in
`TauCeti.AlgebraicGeometry.IdealSheaf.SchemeTheoreticallyDominant`), which apply since flat
surjective morphisms are universally scheme-theoretically dominant
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.universally_of_flat_of_surjective`, in
`TauCeti.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticallyDominant`).

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.comap_le_comap_iff_of_flat_of_surjective`: inverse
  images along a flat surjective morphism reflect inclusion.
* `AlgebraicGeometry.Scheme.IdealSheafData.comap_inj_of_flat_of_surjective`: two ideal sheaves are
  equal exactly when their inverse images along a flat surjective morphism are.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §1.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.3.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g] [Surjective g]

/-- **Inverse images along a flat surjective morphism reflect inclusion.** For `g : Y ⟶ X` flat
and surjective, `I.comap g ≤ J.comap g` exactly when `I ≤ J`. -/
@[simp]
theorem comap_le_comap_iff_of_flat_of_surjective {I J : X.IdealSheafData} :
    I.comap g ≤ J.comap g ↔ I ≤ J :=
  comap_le_comap_iff_of_universally_isSchemeTheoreticallyDominant g
    (IsSchemeTheoreticallyDominant.universally_of_flat_of_surjective g)

/-- **Equalities of closed subschemes descend along flat surjective morphisms.** Two ideal
sheaves are equal exactly when their inverse images along a flat surjective morphism are. -/
@[simp]
theorem comap_inj_of_flat_of_surjective {I J : X.IdealSheafData} :
    I.comap g = J.comap g ↔ I = J :=
  (comap_injective_of_universally_isSchemeTheoreticallyDominant g
    (IsSchemeTheoreticallyDominant.universally_of_flat_of_surjective g)).eq_iff

end AlgebraicGeometry.Scheme.IdealSheafData
