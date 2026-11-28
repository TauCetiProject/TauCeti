/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Coefficients
public import TauCeti.AlgebraicTopology.Singular.Relative

/-!
# Changing the category of coefficients of singular homology

Let `F : C ⥤ D` be an additive functor between preadditive categories which preserves coproducts,
and let `R : C`. The singular `n`-chains of a space `X` with coefficients in `R` are a coproduct of
copies of `R`, one for each singular `n`-simplex, so applying `F` to them gives the singular
`n`-chains with coefficients in `F R`. This identifies the singular chain complex with coefficients
in `F R` with the image under `F` of the one with coefficients in `R`, naturally in `X`
(`CategoryTheory.Functor.singularChainComplexFunctorObjCompMapIso`); it is Mathlib's simplicial
statement `SSet.chainComplexFunctorObjCompMapIso` applied to the singular simplicial set. When `F`
also preserves homology, for instance when it is an exact functor of abelian categories, it follows
that `F` commutes with singular homology
(`CategoryTheory.Functor.singularHomologyFunctorObjCompIso`):

`F (Hₙ(X; R)) ≅ Hₙ(X; F R)`.

The main example is restriction of scalars `ModuleCat S ⥤ ModuleCat R` along a ring homomorphism
`R →+* S`: it preserves all colimits, being left adjoint to coextension of scalars, and it is exact.
So the homology with coefficients in an `S`-module `M`, regarded as an `R`-module, is the homology
with coefficients in `M` regarded as an `R`-module. Along `ℤ →+* ℤ/2` this compares integral chains
reduced modulo two with mod-two chains; see
`TauCeti.AlgebraicTopology.Singular.Coefficients.ModTwo`.
Extension of scalars is another example of the chain-level statement, since it preserves colimits.
When exact (e.g. flat ring maps), it also commutes with relative and absolute singular homology,
feeding scalar extension of local homology, module orientations, and fundamental classes.

## Main declarations

* `CategoryTheory.Functor.singularChainComplexFunctorObjCompMapIso`: `F (C(X; R)) ≅ C(X; F R)`,
  naturally in `X`.
* `CategoryTheory.Functor.singularHomologyFunctorObjCompIso`: `F (Hₙ(X; R)) ≅ Hₙ(X; F R)`,
  naturally in `X`.
* `CategoryTheory.Functor.isZero_singularHomologyFunctor_iff`: when `F` is also faithful,
  `Hₙ(X; F R) = 0` if and only if `Hₙ(X; R) = 0`.
* `TopPair.singularHomologyObjIso`: `F (Hₙ(P; R)) ≅ Hₙ(P; F R)` for a topological pair `P`.
* `RingHom.singularHomologyExtendScalarsIso`: `S ⊗[R] Hₖ(M; R) ≅ Hₖ(M; S)` for exact `f : R →+* S`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial

universe w v v' u u'

namespace CategoryTheory.Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasCoproducts.{w} C] [HasCoproducts.{w} D]
  (F : C ⥤ D) [F.Additive] [∀ T : Type w, PreservesColimitsOfShape (Discrete T) F] (R : C)

/-- **Singular chains commute with a coproduct-preserving functor of coefficients**: for an additive
functor `F : C ⥤ D` preserving coproducts, the singular chain complex with coefficients in `F R` is
the image under `F` of the one with coefficients in `R`, naturally in the space. -/
def singularChainComplexFunctorObjCompMapIso :
    (singularChainComplexFunctor C).obj R ⋙ F.mapHomologicalComplex (.down ℕ) ≅
      (singularChainComplexFunctor D).obj (F.obj R) :=
  Functor.isoWhiskerLeft TopCat.toSSet (SSet.chainComplexFunctorObjCompMapIso F R)

/-- The inverse of `F (C(X; R)) ≅ C(X; F R)` at a space `X` is the inverse of Mathlib's simplicial
comparison at the singular simplicial set of `X`. -/
lemma singularChainComplexFunctorObjCompMapIso_inv_app (X : TopCat.{w}) :
    (singularChainComplexFunctorObjCompMapIso F R).inv.app X =
      (SSet.chainComplexFunctorObjCompMapIso F R).inv.app (TopCat.toSSet.obj X) :=
  (rfl)

variable [CategoryWithHomology C] [CategoryWithHomology D] [F.PreservesHomology]

/-- **Singular homology commutes with an exact coproduct-preserving functor of coefficients**: for
an additive functor `F : C ⥤ D` preserving coproducts and homology, `F (Hₙ(X; R)) ≅ Hₙ(X; F R)`,
naturally in the space. Its component at `X` is the comparison of the homology of the image complex
with the image of the homology, followed by the map induced by `F (C(X; R)) ≅ C(X; F R)`. -/
def singularHomologyFunctorObjCompIso (n : ℕ) :
    (singularHomologyFunctor C n).obj R ⋙ F ≅ (singularHomologyFunctor D n).obj (F.obj R) :=
  Functor.isoWhiskerLeft TopCat.toSSet (SSet.homologyFunctorObjCompIso F R n)

/-- The component at a space `X` of `F (Hₙ(X; R)) ≅ Hₙ(X; F R)` is the comparison of the image of
the homology with the homology of the image complex, followed by the map induced by
`F (C(X; R)) ≅ C(X; F R)`. -/
lemma singularHomologyFunctorObjCompIso_hom_app (n : ℕ) (X : TopCat.{w}) :
    (singularHomologyFunctorObjCompIso F R n).hom.app X =
      (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).inv.app
          (((singularChainComplexFunctor C).obj R).obj X) ≫
        HomologicalComplex.homologyMap ((singularChainComplexFunctorObjCompMapIso F R).hom.app X)
          n :=
  SSet.homologyFunctorObjCompIso_hom_app F R n (TopCat.toSSet.obj X)

/-- The inverse component at a space `X` of `F (Hₙ(X; R)) ≅ Hₙ(X; F R)`. -/
lemma singularHomologyFunctorObjCompIso_inv_app (n : ℕ) (X : TopCat.{w}) :
    (singularHomologyFunctorObjCompIso F R n).inv.app X =
      HomologicalComplex.homologyMap ((singularChainComplexFunctorObjCompMapIso F R).inv.app X) n ≫
        (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).hom.app
          (((singularChainComplexFunctor C).obj R).obj X) :=
  SSet.homologyFunctorObjCompIso_inv_app F R n (TopCat.toSSet.obj X)

/-- The inverse of `F (Hₙ(X; R)) ≅ Hₙ(X; F R)` at a space `X` is the map induced by
`C(X; F R) ≅ F (C(X; R))`, followed by the comparison of the homology of the image complex with
the image of the homology. -/
lemma singularHomologyFunctorObjCompIso_inv_app (n : ℕ) (X : TopCat.{w}) :
    (singularHomologyFunctorObjCompIso F R n).inv.app X =
      HomologicalComplex.homologyMap ((singularChainComplexFunctorObjCompMapIso F R).inv.app X)
          n ≫
        (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).hom.app
          (((singularChainComplexFunctor C).obj R).obj X) :=
  (rfl)

/-- For a faithful additive functor `F : C ⥤ D` preserving coproducts and homology,
`Hₙ(X; F R) = 0` if and only if `Hₙ(X; R) = 0`. -/
lemma isZero_singularHomologyFunctor_iff [F.Faithful] (n : ℕ) (X : TopCat.{w}) :
    IsZero (((singularHomologyFunctor D n).obj (F.obj R)).obj X) ↔
      IsZero (((singularHomologyFunctor C n).obj R).obj X) := by
  rw [← ((singularHomologyFunctorObjCompIso F R n).app X).isZero_iff,
    IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero, Functor.comp_obj, ← F.map_id, F.map_eq_zero_iff]

end CategoryTheory.Functor

namespace TopPair
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Preadditive C]
  [Preadditive D] [HasCoproducts.{w} C] [HasCoproducts.{w} D] [CategoryWithHomology C]
  [CategoryWithHomology D] (F : C ⥤ D) [F.Additive]
  [∀ T : Type w, PreservesColimitsOfShape (Discrete T) F] [F.PreservesHomology] (R : C)
/-- **Relative singular homology commutes with exact coproduct-preserving `F`**: `F Hₙ ≅ Hₙ F`. -/
def singularHomologyObjIso (P : TopPair.{w}) (n : ℕ) :
    F.obj (P.singularHomology R n) ≅ P.singularHomology (F.obj R) n :=
  (SSetPair.homologyFunctorObjCompIso F R n).app (toSSetPair.obj P)
lemma singularHomologyObjIso_hom (P : TopPair.{w}) (n : ℕ) : (singularHomologyObjIso F R P n).hom =
    (SSetPair.homologyFunctorObjCompIso F R n).hom.app (toSSetPair.obj P) := (rfl)
lemma singularHomologyObjIso_inv (P : TopPair.{w}) (n : ℕ) : (singularHomologyObjIso F R P n).inv =
    (SSetPair.homologyFunctorObjCompIso F R n).inv.app (toSSetPair.obj P) := (rfl)
@[reassoc] lemma map_singularHomologyMap_comp_singularHomologyObjIso_hom {P P' : TopPair.{w}}
    (f : P ⟶ P') (n : ℕ) :
    F.map (TopPair.singularHomologyMap f R n) ≫ (singularHomologyObjIso F R P' n).hom =
      (singularHomologyObjIso F R P n).hom ≫ TopPair.singularHomologyMap f (F.obj R) n :=
  (SSetPair.homologyFunctorObjCompIso F R n).hom.naturality (toSSetPair.map f)
@[reassoc] lemma map_singularHomologyπ_comp_singularHomologyObjIso_hom (P : TopPair.{w}) (n : ℕ) :
    F.map (P.singularHomologyπ R n) ≫ (singularHomologyObjIso F R P n).hom =
      (SSet.homologyObjIso F R (TopCat.toSSet.obj P.fst) n).hom ≫ P.singularHomologyπ (F.obj R) n :=
  SSetPair.map_homologyπ_comp_homologyFunctorObjCompIso_hom_app F R n (toSSetPair.obj P)
end TopPair

namespace RingHom
open ModuleCat (extendScalars of)
open CategoryTheory.Functor.Monoidal (εIso)
open TopCat (toSSet ofHom)
open SSet (homologyMap homologyObjIso homologyIsoOfCoefficientsIso)
variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
  [PreservesFiniteLimits (extendScalars.{w} f)]
section
variable (M : Type w) [TopologicalSpace M] (k : ℕ)
/-- **Extension of scalars commutes with singular homology** along exact `f : R →+* S`. -/
def singularHomologyExtendScalarsIso :
    (extendScalars.{w} f).obj ((toSSet.obj (TopCat.of M)).homology (of R R) k) ≅
      (toSSet.obj (TopCat.of M)).homology (of S S) k :=
  (f.simplicialHomologyFunctorExtendScalarsIso k).app (toSSet.obj (TopCat.of M))
lemma singularHomologyExtendScalarsIso_hom : (f.singularHomologyExtendScalarsIso M k).hom =
    (homologyObjIso (extendScalars.{w} f) (of R R) (toSSet.obj (TopCat.of M)) k).hom ≫
      (homologyIsoOfCoefficientsIso (εIso _).symm (toSSet.obj (TopCat.of M)) k).hom :=
  f.simplicialHomologyFunctorExtendScalarsIso_hom_app _ k
lemma singularHomologyExtendScalarsIso_inv : (f.singularHomologyExtendScalarsIso M k).inv =
    (homologyIsoOfCoefficientsIso (εIso _).symm (toSSet.obj (TopCat.of M)) k).inv ≫
      (homologyObjIso (extendScalars.{w} f) (of R R) (toSSet.obj (TopCat.of M)) k).inv :=
  f.simplicialHomologyFunctorExtendScalarsIso_inv_app _ k
end
@[reassoc] lemma map_homologyMap_comp_singularHomologyExtendScalarsIso_hom {M N : Type w}
    [TopologicalSpace M] [TopologicalSpace N] (g : C(M, N)) (k : ℕ) :
    (extendScalars.{w} f).map (homologyMap (toSSet.map (ofHom g)) (of R R) k) ≫
        (f.singularHomologyExtendScalarsIso N k).hom = (f.singularHomologyExtendScalarsIso M k).hom
          ≫ homologyMap (toSSet.map (ofHom g)) (of S S) k :=
  (f.simplicialHomologyFunctorExtendScalarsIso k).hom.naturality (toSSet.map (ofHom g))
end RingHom
