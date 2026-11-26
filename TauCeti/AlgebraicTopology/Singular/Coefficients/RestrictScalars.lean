/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Pairing
public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients

/-!
# Singular chains and homology under a change of coefficient ring

Let `f : R →+* k` be a homomorphism of commutative rings and write `G` for restriction of scalars
`ModuleCat k ⥤ ModuleCat R` along `f`. Singular chains of a space `X` over `R` with coefficients
in an `R`-module `T` map to the singular chains over `k` with coefficients in `k`, viewed as
`R`-modules, once a map `c : T ⟶ G k` is chosen: the chain map
`TopCat.restrictScalarsChainMap` sends the simplex `σ` with coefficient `t` to `σ` with
coefficient `c t`. On homology this gives

`TopCat.restrictScalarsHomologyMap : Hₙ(X; T) ⟶ G Hₙ(X; k)`.

Restriction of scalars is exact and preserves coproducts, which is what makes these maps well
defined: the chain comparison is built from the identification
`CategoryTheory.Functor.singularChainComplexFunctorObjCompMapIso` of `G` applied to chains over `k`
with chains with coefficients in `G k` (Mathlib's `SSet.chainComplexFunctorObjCompMapIso` for
singular simplices), and the homology comparison from its homology version
`CategoryTheory.Functor.singularHomologyFunctorObjCompIso`.

## Main definitions and results

* `TopCat.restrictScalarsChainMap`, `TopCat.restrictScalarsHomologyMap`: the comparison of chains
  and of homology.
* `TopCat.restrictScalarsHomologyMap_eq`: the homology comparison is the map induced by the chain
  comparison.
* `TopCat.homologyπ_restrictScalarsHomologyMap`: the homology comparison on the class of a cycle.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.A (change of coefficients).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex Simplicial

universe w

namespace TopCat

variable (X : TopCat.{w}) {R k : Type w} [CommRing R] [CommRing k] (f : R →+* k)
  {T : ModuleCat.{w} R} (c : T ⟶ (ModuleCat.restrictScalars f).obj (𝟙_ (ModuleCat.{w} k)))

/-- The chain map from singular chains over `R` with coefficients in `T` to the restriction of
scalars of singular chains over `k`, applying `c` to the coefficient of each simplex. -/
def restrictScalarsChainMap :
    (toSSet.obj X).chainComplex T ⟶
      ((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj
        ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))) :=
  ((singularChainComplexFunctor _).map c).app X ≫
    ((ModuleCat.restrictScalars f).singularChainComplexFunctorObjCompMapIso
      (𝟙_ (ModuleCat.{w} k))).inv.app X

/-- The chain comparison in terms of Mathlib's simplicial comparison
`SSet.chainComplexFunctorObjCompMapIso`, whose objects are the chain complexes
`(toSSet.obj X).chainComplex _` rather than their singular-functor forms. -/
private lemma restrictScalarsChainMap_eq :
    X.restrictScalarsChainMap f c =
      ((SSet.chainComplexFunctor _).map c).app (toSSet.obj X) ≫
        (SSet.chainComplexFunctorObjCompMapIso (ModuleCat.restrictScalars f)
          (𝟙_ (ModuleCat.{w} k))).inv.app (toSSet.obj X) :=
  congrArg (_ ≫ ·) (Functor.singularChainComplexFunctorObjCompMapIso_inv_app _ _ X)

/-- The chain comparison applies `c` to the coefficient of a simplex. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_restrictScalarsChainMap_f {n : ℕ} (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫ (X.restrictScalarsChainMap f c).f n =
      c ≫ (ModuleCat.restrictScalars f).map ((toSSet.obj X).ιChainComplex σ) := by
  rw [restrictScalarsChainMap_eq, HomologicalComplex.comp_f]
  simp

/-- The chain comparison along an isomorphism of coefficients is an isomorphism. -/
instance [IsIso c] : IsIso (X.restrictScalarsChainMap f c) := by
  rw [restrictScalarsChainMap_eq]
  infer_instance

/-- The comparison `Hₙ(X; T) ⟶ G Hₙ(X; k)`: the map `Hₙ(X; T) ⟶ Hₙ(X; G k)` induced by `c`,
followed by the identification `CategoryTheory.Functor.singularHomologyFunctorObjCompIso` of
`Hₙ(X; G k)` with the restriction of scalars of `Hₙ(X; k)`. -/
def restrictScalarsHomologyMap (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{w} R) n).obj T).obj X ⟶
      (ModuleCat.restrictScalars f).obj
        (((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :=
  ((singularHomologyFunctor (ModuleCat.{w} R) n).map c).app X ≫
    ((ModuleCat.restrictScalars f).singularHomologyFunctorObjCompIso
      (𝟙_ (ModuleCat.{w} k)) n).inv.app X

/-- The homology comparison is the map induced by `TopCat.restrictScalarsChainMap`, followed by the
identification of the homology of the restricted complex with the restriction of its homology. -/
lemma restrictScalarsHomologyMap_eq (n : ℕ) :
    X.restrictScalarsHomologyMap f c n =
      homologyMap (X.restrictScalarsChainMap f c) n ≫
        ((ModuleCat.restrictScalars f).mapHomologicalComplexCompHomologyFunctorIso _ n).hom.app
          ((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))) := by
  rw [restrictScalarsChainMap_eq, homologyMap_comp, Category.assoc]
  -- The map induced by `c` on singular homology is by definition the one induced on chains.
  exact congrArg (_ ≫ ·) ((Functor.singularHomologyFunctorObjCompIso_inv_app _ _ n X).trans
    (congrArg (homologyMap · n ≫ _)
      (Functor.singularChainComplexFunctorObjCompMapIso_inv_app _ _ X)))

/-- The homology comparison on the class of a cycle `z` is the restriction of the class of the
cycle `c_* z`. -/
@[reassoc]
lemma homologyπ_restrictScalarsHomologyMap (n : ℕ) :
    ((toSSet.obj X).chainComplex T).homologyπ n ≫ X.restrictScalarsHomologyMap f c n =
      cyclesMap (X.restrictScalarsChainMap f c) n ≫
        ((((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).sc n).mapCyclesIso
          (ModuleCat.restrictScalars f)).hom ≫
        (ModuleCat.restrictScalars f).map
          (((toSSet.obj X).chainComplex (𝟙_ (ModuleCat.{w} k))).homologyπ n) :=
  -- The comparison and the class maps name the same objects in their singular-functor and
  -- chain-complex forms, so the squares are composed as terms.
  (congrArg (_ ≫ ·) (X.restrictScalarsHomologyMap_eq f c n)).trans <|
    (homologyπ_naturality_assoc (X.restrictScalarsChainMap f c) n _).trans <|
      congrArg (_ ≫ ·)
        (Functor.homologyπ_comp_mapHomologicalComplexCompHomologyFunctorIso_hom_app _ _ _ _)

/-- The homology comparison along an isomorphism of coefficients is an isomorphism. -/
instance [IsIso c] (n : ℕ) : IsIso (X.restrictScalarsHomologyMap f c n) := by
  rw [restrictScalarsHomologyMap]
  infer_instance

end TopCat
