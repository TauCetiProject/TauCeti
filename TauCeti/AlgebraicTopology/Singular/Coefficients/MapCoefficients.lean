/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

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

## Main declarations

* `CategoryTheory.Functor.singularChainComplexFunctorObjCompMapIso`: `F (C(X; R)) ≅ C(X; F R)`,
  naturally in `X`.
* `CategoryTheory.Functor.singularHomologyFunctorObjCompIso`: `F (Hₙ(X; R)) ≅ Hₙ(X; F R)`,
  naturally in `X`.
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

/-- The identification `F (C(X; R)) ≅ C(X; F R)` sends the image under `F` of the summand of a
singular simplex to the summand of that simplex. -/
@[simp, reassoc]
lemma map_ιChainComplex_singularChainComplexFunctorObjCompMapIso_hom_app_f (X : TopCat.{w})
    {n : ℕ} (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    F.map ((TopCat.toSSet.obj X).ιChainComplex (R := R) x) ≫
        ((singularChainComplexFunctorObjCompMapIso F R).hom.app X).f n =
      (TopCat.toSSet.obj X).ιChainComplex x :=
  SSet.map_ιChainComplex_chainComplexFunctorObjCompMapIso_hom_app_f _ F x

variable [CategoryWithHomology C] [CategoryWithHomology D] [F.PreservesHomology]

/-- **Singular homology commutes with an exact coproduct-preserving functor of coefficients**: for
an additive functor `F : C ⥤ D` preserving coproducts and homology, `F (Hₙ(X; R)) ≅ Hₙ(X; F R)`,
naturally in the space. Its component at `X` is the comparison of the homology of the image complex
with the image of the homology, followed by the map induced by `F (C(X; R)) ≅ C(X; F R)`. -/
def singularHomologyFunctorObjCompIso (n : ℕ) :
    (singularHomologyFunctor C n).obj R ⋙ F ≅ (singularHomologyFunctor D n).obj (F.obj R) :=
  -- Mathlib's `singularHomologyFunctor` is by definition singular chains followed by homology
  Functor.isoWhiskerLeft ((singularChainComplexFunctor C).obj R)
      (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).symm ≪≫
    Functor.isoWhiskerRight (singularChainComplexFunctorObjCompMapIso F R)
      (HomologicalComplex.homologyFunctor D (.down ℕ) n)

/-- The component at a space `X` of `F (Hₙ(X; R)) ≅ Hₙ(X; F R)` is the comparison of the image of
the homology with the homology of the image complex, followed by the map induced by
`F (C(X; R)) ≅ C(X; F R)`. -/
lemma singularHomologyFunctorObjCompIso_hom_app (n : ℕ) (X : TopCat.{w}) :
    (singularHomologyFunctorObjCompIso F R n).hom.app X =
      (F.mapHomologicalComplexCompHomologyFunctorIso (.down ℕ) n).inv.app
          (((singularChainComplexFunctor C).obj R).obj X) ≫
        HomologicalComplex.homologyMap ((singularChainComplexFunctorObjCompMapIso F R).hom.app X)
          n :=
  (rfl)

end CategoryTheory.Functor
