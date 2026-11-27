/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
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

In particular, for an `R`-algebra `S` and an `S`-module `M` carrying a compatible `R`-module
structure (`IsScalarTower R S M`), singular homology with `R`-module coefficients `M` is naturally
isomorphic to singular homology with `S`-module coefficients `M` followed by restriction of scalars
along `algebraMap R S` (`TauCeti.singularHomologyRestrictScalarsNatIso`). Because restriction of
scalars is faithful and reflects isomorphisms, singular homology with `R`-module coefficients `M`
vanishes if and only if singular homology with `S`-module coefficients `M` does
(`TopCat.isZero_singularHomology_restrictScalars_iff`), and a continuous map induces an
isomorphism on one if and only if it induces an isomorphism on the other
(`TopCat.Hom.isIso_singularHomologyMap_restrictScalars_iff`).

## Main definitions and results

* `TopCat.restrictScalarsChainMap`, `TopCat.restrictScalarsHomologyMap`: the comparison of chains
  and of homology.
* `TopCat.restrictScalarsHomologyMap_eq`: the homology comparison is the map induced by the chain
  comparison.
* `TopCat.homologyπ_restrictScalarsHomologyMap`: the homology comparison on the class of a cycle.
* `TopCat.restrictScalarsHomologyMap_naturality`: the homology comparison is natural in the space.
* `TauCeti.singularHomologyRestrictScalarsNatIso`: natural isomorphism comparing `Hₙ(-; M)` over
  `R` with restriction of scalars of `Hₙ(-; M)` over `S`.
* `TopCat.isZero_singularHomology_restrictScalars_iff`: vanishing of singular homology with
  coefficients `M` is invariant under restriction of scalars along `algebraMap R S`.
* `TopCat.Hom.isIso_singularHomologyMap_restrictScalars_iff`: inducing an isomorphism on singular
  homology with coefficients `M` is invariant under restriction of scalars along `algebraMap R S`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.A (change of coefficients).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex Simplicial

universe u u₁ u₂ w

namespace TauCeti

/-- For an `R`-algebra `S` and an `S`-module `M` carrying a compatible `R`-module structure,
singular homology with `R`-module coefficients `M` is naturally isomorphic to singular homology with
`S`-module coefficients `M` followed by restriction of scalars along `algebraMap R S`. -/
def singularHomologyRestrictScalarsNatIso (R : Type u₁) (S : Type u₂) [CommRing R] [Ring S]
    [Algebra R S] (M : Type u) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (n : ℕ) :
    (singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R M) ≅
      (singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S M) ⋙
        ModuleCat.restrictScalars.{u} (algebraMap R S) :=
  (singularHomologyFunctor (ModuleCat.{u} R) n).mapIso
      (ModuleCat.restrictScalarsAlgebraMapIso (R := R) (S := S) M).symm ≪≫
    (Functor.singularHomologyFunctorObjCompIso
      (ModuleCat.restrictScalars.{u} (algebraMap R S))
      (ModuleCat.of S M) n).symm

end TauCeti

namespace TopCat

/-- Singular homology with coefficients in an `S`-module `M`, viewed as an `R`-module through
`IsScalarTower R S M`, vanishes exactly when singular homology with `S`-module coefficients `M`
does. -/
theorem isZero_singularHomology_restrictScalars_iff (X : TopCat.{u})
    (R : Type u₁) (S : Type u₂) [CommRing R] [Ring S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R M)).obj X) ↔
      IsZero (((singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S M)).obj X) := by
  rw [Iso.isZero_iff (((singularHomologyFunctor (ModuleCat.{u} R) n).mapIso
      (ModuleCat.restrictScalarsAlgebraMapIso (R := R) (S := S) M).symm).app X)]
  exact (ModuleCat.restrictScalars.{u} (algebraMap R S)).isZero_singularHomologyFunctor_iff
    (ModuleCat.of S M) n X

section MapComparison

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

variable {X} in
/-- **The homology comparison is natural in the space**: for a continuous map `g : X ⟶ Y`, the
comparison `Hₙ(-; T) ⟶ G Hₙ(-; k)` commutes with the maps `g_*` on both sides. -/
@[reassoc]
lemma restrictScalarsHomologyMap_naturality {Y : TopCat.{w}} (g : X ⟶ Y) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{w} R) n).obj T).map g ≫
        Y.restrictScalarsHomologyMap f c n =
      X.restrictScalarsHomologyMap f c n ≫ (ModuleCat.restrictScalars f).map
        (((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).map g) := by
  rw [restrictScalarsHomologyMap, restrictScalarsHomologyMap, NatTrans.naturality_assoc,
    Category.assoc]
  exact congrArg (_ ≫ ·)
    (((ModuleCat.restrictScalars f).singularHomologyFunctorObjCompIso
      (𝟙_ (ModuleCat.{w} k)) n).inv.naturality g)

end MapComparison

end TopCat

namespace TopCat.Hom

/-- A continuous map induces an isomorphism on singular homology with coefficients in an
`S`-module `M`, viewed as an `R`-module through `IsScalarTower R S M`, exactly when it induces one
with `S`-module coefficients `M`. -/
theorem isIso_singularHomologyMap_restrictScalars_iff {X Y : TopCat.{u}} (f : X ⟶ Y)
    (R : Type u₁) (S : Type u₂) [CommRing R] [Ring S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R M)).map f) ↔
      IsIso (((singularHomologyFunctor (ModuleCat.{u} S) n).obj (ModuleCat.of S M)).map f) :=
  (NatIso.isIso_map_iff (TauCeti.singularHomologyRestrictScalarsNatIso R S M n) f).trans
    (isIso_iff_of_reflects_iso _ (ModuleCat.restrictScalars.{u} (algebraMap R S)))

end TopCat.Hom

end
