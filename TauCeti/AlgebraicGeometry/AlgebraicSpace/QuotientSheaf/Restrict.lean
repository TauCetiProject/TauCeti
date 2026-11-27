/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.AlgebraicSpace.QuotientSheaf
public import TauCeti.CategoryTheory.Sites.QuotientSheaf.Restrict

/-!
# Restricting the quotient sheaf of an equivalence relation of schemes

Let `s t : R ⟶ U` be an equivalence relation of schemes and `g : U' ⟶ U` an fppf covering (flat,
locally of finite presentation and surjective). The restriction `R' = R ×_{U × U} (U' × U')` of
the relation along `g` (`TauCeti.CategoryTheory.restrictRel g t s`) has the same quotient sheaf:
`U'/R' ≅ U/R` (Stacks, Lemma 39.20.5 (045Z)). This is
`TauCeti.CategoryTheory.quotientSheaf.restrictIso` at `J := Scheme.fppfTopology`.

## Main definitions

* `TauCeti.AlgebraicGeometry.Spaces.quotientSheaf.restrictIso`: for an equivalence relation and
  an fppf covering `g : U' ⟶ U`, the isomorphism `U'/R' ≅ U/R` induced by `g`.

## References

* [Stacks Project, Lemma 39.20.5](https://stacks.math.columbia.edu/tag/045Z)
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry TauCeti.CategoryTheory

universe u

variable {R U U' : Scheme.{u}} (s t : R ⟶ U) (g : U' ⟶ U)

/-- **Restriction along an fppf covering** (Stacks, Lemma 39.20.5 (045Z)): for an equivalence
relation `(t, s)` on `U` and an fppf covering `g : U' ⟶ U`, the quotient sheaf of the restriction
`R' = R ×_{U × U} (U' × U')` of the relation along `g` is the quotient sheaf of the relation,
`U'/R' ≅ U/R`. -/
noncomputable def quotientSheaf.restrictIso [IsEquivalenceRelation t s] [Flat g]
    [LocallyOfFinitePresentation g] [Surjective g] :
    quotientSheaf (restrictRel.snd g t s) (restrictRel.fst g t s) ≅ quotientSheaf s t :=
  TauCeti.CategoryTheory.quotientSheaf.restrictIso s t
    (Precoverage.generate_mem_toGrothendieck g.singleton_mem_fppfPrecoverage)

/-- The projection onto `U'/R'`, followed by `U'/R' ≅ U/R`, is the map `h_{U'} ⟶ h_U` induced by
`g` followed by the projection onto `U/R`. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.π_restrictIso_hom [IsEquivalenceRelation t s] [Flat g]
    [LocallyOfFinitePresentation g] [Surjective g] :
    TauCeti.CategoryTheory.quotientSheaf.π Scheme.fppfTopology (restrictRel.snd g t s)
        (restrictRel.fst g t s) ≫ (quotientSheaf.restrictIso s t g).hom =
      Scheme.fppfTopology.uliftYoneda.{u + 1}.map g ≫
        TauCeti.CategoryTheory.quotientSheaf.π Scheme.fppfTopology s t :=
  TauCeti.CategoryTheory.quotientSheaf.π_restrictIso_hom _ _ _

/-- The map `h_{U'} ⟶ h_U` induced by `g`, followed by the projection onto `U/R` and the inverse
of `U'/R' ≅ U/R`, is the projection onto `U'/R'`. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.uliftYoneda_map_π_restrictIso_inv [IsEquivalenceRelation t s] [Flat g]
    [LocallyOfFinitePresentation g] [Surjective g] :
    Scheme.fppfTopology.uliftYoneda.{u + 1}.map g ≫
        TauCeti.CategoryTheory.quotientSheaf.π Scheme.fppfTopology s t ≫
          (quotientSheaf.restrictIso s t g).inv =
      TauCeti.CategoryTheory.quotientSheaf.π Scheme.fppfTopology (restrictRel.snd g t s)
        (restrictRel.fst g t s) :=
  TauCeti.CategoryTheory.quotientSheaf.uliftYoneda_map_π_restrictIso_inv _ _ _

end TauCeti.AlgebraicGeometry.Spaces
