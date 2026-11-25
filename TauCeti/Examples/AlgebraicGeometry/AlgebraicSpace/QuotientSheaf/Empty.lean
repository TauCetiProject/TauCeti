/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.EtaleEquivRel.Examples
public import TauCeti.AlgebraicGeometry.AlgebraicSpace.QuotientSheaf

/-!
# The quotient sheaf of the empty pre-relation does not restrict along coverings

For a scheme `U` and an empty scheme `R`, the empty pre-relation `s = t : R ⟶ U` relates no
points, and its quotient sheaf is the representable sheaf: `U/∅ ≅ h_U`
(`TauCeti.AlgebraicGeometry.Spaces.QuotientSheafEmptyExample.isIso_π_of_isEmpty`).

Restricting along the fold map `g : U ⨿ U ⟶ U`, an fppf covering, gives the pulled-back
pre-relation `R' = R ×_{U × U} (U' × U')` on `U' = U ⨿ U` (`TauCeti.CategoryTheory.restrictRel`),
which is again empty (`TauCeti.AlgebraicGeometry.Spaces.isEmpty_restrictRel`), so
`U'/R' ≅ h_{U ⨿ U}`. For nonempty `U` the comparison `U'/R' ⟶ U/R` induced by `g` is not an
isomorphism
(`TauCeti.AlgebraicGeometry.Spaces.QuotientSheafEmptyExample.not_isIso_desc_restrictRel`), since
`g` is not: for `U = Spec k`, `U'/∅` has two points over `k` and `U/∅` one. So the restriction of
quotient sheaves along a covering (Stacks, Lemma 39.20.5 (045Z)) needs an equivalence relation, or
a pre-equivalence relation: the pre-relation must identify the two preimages of each point of `U`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Spaces.QuotientSheafEmptyExample

open TauCeti.CategoryTheory

variable {R U : Scheme.{u}} [IsEmpty R]

/-- **`U/∅ ≅ h_U`.** For an empty scheme `R`, the projection onto the quotient sheaf of the empty
pre-relation `s, t : R ⟶ U` is an isomorphism. -/
theorem isIso_π_of_isEmpty (s t : R ⟶ U) :
    IsIso (TauCeti.CategoryTheory.quotientSheaf.π.{u + 1} Scheme.fppfTopology s t) := by
  obtain rfl : s = t := AlgebraicGeometry.isInitialOfIsEmpty.hom_ext _ _
  infer_instance

variable (U)

/-- **Restriction fails for the empty pre-relation.** For a nonempty scheme `U`, an empty scheme
`R` and the empty pre-relation `s, t : R ⟶ U`, the map `U'/R' ⟶ U/R` from the quotient sheaf of
the restriction of the pre-relation along the fold map `U' = U ⨿ U ⟶ U`, induced by the fold
map, is not an isomorphism: both quotient sheaves are representable, by `U ⨿ U` and by `U`, and
the fold map is not an isomorphism. -/
theorem not_isIso_desc_restrictRel [Nonempty U] (s t : R ⟶ U) :
    ¬ IsIso (TauCeti.CategoryTheory.quotientSheaf.desc
      (Scheme.fppfTopology.uliftYoneda.{u + 1}.map (coprod.desc (𝟙 U) (𝟙 U)) ≫
        TauCeti.CategoryTheory.quotientSheaf.π.{u + 1} Scheme.fppfTopology s t)
      (quotientSheaf.restrictRel_condition.{u + 1} Scheme.fppfTopology s t
        (coprod.desc (𝟙 U) (𝟙 U)))) := by
  intro h
  have := isIso_π_of_isEmpty s t
  have := isIso_π_of_isEmpty (restrictRel.snd (coprod.desc (𝟙 U) (𝟙 U)) t s)
    (restrictRel.fst (coprod.desc (𝟙 U) (𝟙 U)) t s)
  -- `h g ≫ π = π' ≫ desc` and `π` are isomorphisms, so `h g` and `g` are, and `g` is mono.
  have := IsIso.of_isIso_fac_right (TauCeti.CategoryTheory.quotientSheaf.π_desc _
    (quotientSheaf.restrictRel_condition.{u + 1} Scheme.fppfTopology s t
      (coprod.desc (𝟙 U) (𝟙 U)))).symm
  have := isIso_of_fully_faithful Scheme.fppfTopology.uliftYoneda.{u + 1}
    (coprod.desc (𝟙 U) (𝟙 U))
  exact not_mono_coprodDesc (𝟙 U) inferInstance

end TauCeti.AlgebraicGeometry.Spaces.QuotientSheafEmptyExample
