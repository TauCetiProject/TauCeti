/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Relative

/-!
# Small-chain comparisons in singular cohomology

Restricting singular cochains of a topological space `X` to the singular simplices subordinate to
an open cover `U` of `X` is a quasi-isomorphism
(`TauCeti.quasiIso_cochainComplexMap_smallSingularSubcomplex_ι`), giving the natural isomorphism
`TauCeti.smallSingularCohomologyIso`.

For a family of subsets `U : ι → Set X` with each member open in `⋃ i, U i`, restricting cochains
along `TopCat.smallSingularSubcomplexToIUnion U` and `TopCat.smallSingularSubcomplexPairToIUnion U`
is likewise a quasi-isomorphism
(`TopCat.quasiIso_cochainComplexMap_smallSingularSubcomplexToIUnion`,
`TopCat.quasiIso_cochainComplexMap_smallSingularSubcomplexPairToIUnion`), inducing isomorphisms on
cohomology (`TopCat.isIso_homologyMap_cochainComplexMap_smallSingularSubcomplexPairToIUnion`), with
binary-union specializations `TopCat.quasiIso_cochainComplexMap_smallSingularSubcomplexToUnion`,
`TopCat.quasiIso_cochainComplexMap_smallSingularSubcomplexPairToUnion`, and
`TopCat.isIso_homologyMap_cochainComplexMap_smallSingularSubcomplexPairToUnion`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.21.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)
  {X : TopCat.{w}} {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
  (hcov : ⋃ i, U i = Set.univ)

/-- The isomorphism on singular cohomology induced by restricting cochains to the chains
subordinate to an open cover. It is dual to `TauCeti.smallSingularHomologyIso`. -/
def smallSingularCohomologyIso (n : ℕ) :
    X.singularCohomology R k M n ≅
      (((X.smallSingularSubcomplex U : SSet).chainComplex R).linearYonedaObj k M).homology n :=
  ((smallSingularChainHomotopyEquiv R U hU hcov).linearYonedaFunctorMap k M).toHomologyIso n

/-- The small-chain cohomology isomorphism is the map induced by the inclusion of the singular
simplices subordinate to the cover. -/
@[simp]
lemma smallSingularCohomologyIso_hom (n : ℕ) :
    (smallSingularCohomologyIso R k M U hU hcov n).hom =
      HomologicalComplex.homologyMap (SSet.cochainComplexMap (X.smallSingularSubcomplex U).ι)
        n := by
  simp [smallSingularCohomologyIso, HomotopyEquiv.toHomologyIso, SSet.cochainComplexMap]

include hU hcov in
/-- Restricting singular cochains to the chains subordinate to an open cover is a
quasi-isomorphism, since the inclusion of those chains is a chain homotopy equivalence. -/
theorem quasiIso_cochainComplexMap_smallSingularSubcomplex_ι :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      (X.smallSingularSubcomplex U).ι) := by
  have := ((smallSingularChainHomotopyEquiv R U hU hcov).linearYonedaFunctorMap k M).quasiIso_hom
  rwa [HomotopyEquiv.linearYonedaFunctorMap_hom, smallSingularChainHomotopyEquiv_hom] at this

/-- The small-chain cohomology isomorphism is natural under maps carrying members of one cover
into members of another. -/
lemma smallSingularCohomologyIso_naturality {κ : Type*} {Y : TopCat.{w}} (V : κ → Set Y)
    (f : X ⟶ Y) (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) (hV : ∀ j, IsOpen (V j))
    (hcovV : ⋃ j, V j = Set.univ) (n : ℕ) :
    TopCat.singularCohomologyMap f n ≫ (smallSingularCohomologyIso R k M U hU hcov n).hom =
      (smallSingularCohomologyIso R k M V hV hcovV n).hom ≫
        HomologicalComplex.homologyMap
          (SSet.cochainComplexMap (X.smallSingularSubcomplexMap U V f r hf)) n := by
  simp only [smallSingularCohomologyIso_hom, TopCat.singularCohomologyMap,
    TopCat.singularCochainComplexMap, ← HomologicalComplex.homologyMap_comp,
    ← SSet.cochainComplexMap_comp, TopCat.smallSingularSubcomplexMap_ι]

end TauCeti

namespace TopCat

open TauCeti.ChainComplex

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C) {X : TopCat.{w}}

/-- The singular simplices of `X` lying in some member of `U` compute the cohomology of
`⋃ i, U i`, since `TopCat.smallSingularSubcomplexToIUnion` induces a chain homotopy equivalence
when each `U i` is open in `⋃ j, U j`. -/
lemma quasiIso_cochainComplexMap_smallSingularSubcomplexToIUnion {ι : Type*} (U : ι → Set X)
    (hU : ∀ i, IsOpen ((↑) ⁻¹' U i : Set ↥(⋃ j, U j))) :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexToIUnion U)) := by
  have := ((smallSingularSubcomplexToIUnionChainHomotopyEquiv R U hU).linearYonedaFunctorMap k
    M).quasiIso_hom
  rwa [HomotopyEquiv.linearYonedaFunctorMap_hom,
    smallSingularSubcomplexToIUnionChainHomotopyEquiv_hom] at this

/-- The cohomology of `X` relative to its singular simplices lying in a member of `U` is that of
`(X, ⋃ i, U i)`, by the small-chain theorem for the cover of `⋃ i, U i` by the traces of `U i`. -/
lemma quasiIso_cochainComplexMap_smallSingularSubcomplexPairToIUnion {ι : Type*} (U : ι → Set X)
    (hU : ∀ i, IsOpen ((↑) ⁻¹' U i : Set ↥(⋃ j, U j))) :
    QuasiIso (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexPairToIUnion U)) := by
  have : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexPairToIUnion U).left) := by
    rw [smallSingularSubcomplexPairToIUnion_left]
    exact quasiIso_cochainComplexMap_smallSingularSubcomplexToIUnion R k M U hU
  have : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexPairToIUnion U).right) := by
    have : IsIso (SSet.chainComplexMap (smallSingularSubcomplexPairToIUnion U).right R) := by
      rw [chainComplexMap_smallSingularSubcomplexPairToIUnion_right]
      exact IsIso.id _
    have : IsIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
        (smallSingularSubcomplexPairToIUnion U).right) :=
      Functor.map_isIso (linearYonedaFunctor k M) _
    exact quasiIso_of_isIso _
  exact SSetPair.quasiIso_cochainComplexMap _

/-- When each `U i` is open in `⋃ j, U j`, restricting cochains of `(X, ⋃ i, U i)` to the chains
of `X` relative to its singular simplices lying in a member of `U` is an isomorphism on
cohomology. -/
lemma isIso_homologyMap_cochainComplexMap_smallSingularSubcomplexPairToIUnion {ι : Type*}
    (U : ι → Set X) (hU : ∀ i, IsOpen ((↑) ⁻¹' U i : Set ↥(⋃ j, U j))) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexPairToIUnion U)) n) := by
  have := quasiIso_cochainComplexMap_smallSingularSubcomplexPairToIUnion R k M U hU
  infer_instance

/-- The singular simplices of `X` lying in `U` or in `V` compute the cohomology of `U ∪ V`, since
`TopCat.smallSingularSubcomplexToUnion` induces a chain homotopy equivalence when `U` and `V` are
open in `U ∪ V`. -/
lemma quasiIso_cochainComplexMap_smallSingularSubcomplexToUnion (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) :
    QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexToUnion U V)) := by
  have := ((smallSingularSubcomplexToUnionChainHomotopyEquiv R U V hU hV).linearYonedaFunctorMap k
    M).quasiIso_hom
  rwa [HomotopyEquiv.linearYonedaFunctorMap_hom,
    smallSingularSubcomplexToUnionChainHomotopyEquiv_hom] at this

/-- The cohomology of `X` relative to its singular simplices lying in `U` or in `V` is that of
`(X, U ∪ V)`, by the small-chain theorem for the cover of `U ∪ V` by `U` and `V`, which only needs
to be open in `U ∪ V`. -/
lemma quasiIso_cochainComplexMap_smallSingularSubcomplexPairToUnion (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) :
    QuasiIso (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexPairToUnion U V)) := by
  have : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexPairToUnion U V).left) := by
    rw [smallSingularSubcomplexPairToUnion_left]
    exact quasiIso_cochainComplexMap_smallSingularSubcomplexToUnion R k M U V hU hV
  have : QuasiIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexPairToUnion U V).right) := by
    have : IsIso (SSet.chainComplexMap (smallSingularSubcomplexPairToUnion U V).right R) := by
      rw [chainComplexMap_smallSingularSubcomplexPairToUnion_right]
      exact IsIso.id _
    have : IsIso (SSet.cochainComplexMap (R := R) (k := k) (M := M)
        (smallSingularSubcomplexPairToUnion U V).right) :=
      Functor.map_isIso (linearYonedaFunctor k M) _
    exact quasiIso_of_isIso _
  exact SSetPair.quasiIso_cochainComplexMap _

/-- For `U` and `V` open in `U ∪ V`, restricting cochains of `(X, U ∪ V)` to the chains of `X`
relative to its singular simplices lying in `U` or in `V` is an isomorphism on cohomology. -/
lemma isIso_homologyMap_cochainComplexMap_smallSingularSubcomplexPairToUnion (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (SSetPair.cochainComplexMap (R := R) (k := k) (M := M)
      (smallSingularSubcomplexPairToUnion U V)) n) := by
  have := quasiIso_cochainComplexMap_smallSingularSubcomplexPairToUnion R k M U V hU hV
  infer_instance

end TopCat
