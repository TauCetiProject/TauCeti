/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Rat

/-!
# Exactness of simplicial chains in the coefficients

Simplicial chains send a short exact sequence of coefficients to a short exact sequence of chain
complexes whenever coproducts in the coefficient category are exact. The construction is Mathlib's
`SSet.chainComplexFunctor`, whose degree-n object is a coproduct of coefficient objects over
the n-simplices. Applying the homology long
exact sequence gives the coefficient connecting homomorphisms, including Bockstein maps.

Extension of scalars along a ring map `f : R →+* S` with exact extension of scalars, such as a
flat one, commutes with homology: `SSet.homologyExtendScalarsIso` identifies the extension of
scalars of the homology with coefficients in `R` with the homology with coefficients in `S`,
naturally in the simplicial set (`SSet.homologyExtendScalarsIso_hom_naturality`). The instance
`ModuleCat.preservesFiniteLimits_extendScalars_intCastRat`, the `ℤ → ℚ` case of
`ModuleCat.preservesFiniteLimits_extendScalars_algebraMap`, supplies the exactness for the flat
map `ℤ → ℚ`, which compares integral and rational homology.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.A, change of coefficients.
-/

public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe w v u

namespace CategoryTheory.ShortComplex.ShortExact

/-- Simplicial chains preserve short exact coefficient sequences when coproducts are exact. -/
lemma map_simplicialChains {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] [AB4OfSize.{w} C] {S : ShortComplex C}
    (hS : S.ShortExact) (X : SSet.{w}) :
    (S.map ((SSet.chainComplexFunctor C).flip.obj X)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let F : C ⥤ C := Functor.const (Discrete (X _⦋n⦌)) ⋙ colim
  -- In degree n the chain functor is the coproduct of the constant coefficient diagram.
  convert hS.map_of_exact F using 1
  rfl

end CategoryTheory.ShortComplex.ShortExact

namespace ModuleCat

/-- Rational extension of scalars is exact, since `ℚ` is a localization of `ℤ`. This is the
`ℤ → ℚ` case of `ModuleCat.preservesFiniteLimits_extendScalars_algebraMap`, stated for
`Int.castRingHom ℚ`, which instance search does not match against `algebraMap ℤ ℚ`. -/
instance preservesFiniteLimits_extendScalars_intCastRat :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars (Int.castRingHom ℚ) : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ) :=
  haveI : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  preservesFiniteLimits_extendScalars_algebraMap (R := ℤ) (S := ℚ)

end ModuleCat

namespace SSet

/-- **Extension of scalars commutes with simplicial homology** along a ring map `f : R →+* S` whose
extension of scalars is exact, for instance a flat one
(`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`): extending scalars of the homology with
coefficients in `R` gives the homology with coefficients in `S`. The `R`-coefficient object is the
native `ULift R`; the `S`-coefficient object is `S`. -/
def homologyExtendScalarsIso {R S : Type u} [CommRing R] [CommRing S] (X : SSet.{u})
    (f : R →+* S) [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f)] (n : ℕ) :
    (ModuleCat.extendScalars f).obj (X.homology (ModuleCat.of R (ULift.{u} R)) n) ≅
      X.homology (ModuleCat.of S S) n := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := ModuleCat.extendScalars f
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let M := ModuleCat.of R (ULift.{u} R)
  let C := X.chainComplex M
  let eUnit : F.obj (ModuleCat.of R R) ≅ ModuleCat.of S S :=
    letI := f.toAlgebra
    (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso
  let eM : F.obj M ≅ ModuleCat.of S S :=
    F.mapIso ULift.moduleEquiv.toModuleIso ≪≫ eUnit
  let eH : F.obj (C.homology n) ≅ X.homology (F.obj M) n :=
    ((C.sc n).mapHomologyIso F).symm ≪≫
      HomologicalComplex.homologyMapIso ((SSet.chainComplexFunctorObjCompMapIso F M).app X) n
  let eC : X.homology (F.obj M) n ≅ X.homology (ModuleCat.of S S) n :=
    HomologicalComplex.homologyMapIso
      (((SSet.chainComplexFunctor.{u} (ModuleCat.{u} S)).flip.obj X).mapIso eM) n
  exact eH ≪≫ eC

/-- The identification `SSet.homologyExtendScalarsIso` is the composite of three comparisons:
extension of scalars commutes with the homology of the chain complex, with the simplicial chain
complex, and carries the coefficients `ULift R` to `S`. -/
theorem homologyExtendScalarsIso_hom {R S : Type u} [CommRing R] [CommRing S] (X : SSet.{u})
    (f : R →+* S) [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f)] (n : ℕ) :
    (X.homologyExtendScalarsIso f n).hom =
      (((X.chainComplex (ModuleCat.of R (ULift.{u} R))).sc n).mapHomologyIso
          (ModuleCat.extendScalars f)).inv ≫
        HomologicalComplex.homologyMap ((SSet.chainComplexFunctorObjCompMapIso
          (ModuleCat.extendScalars f) (ModuleCat.of R (ULift.{u} R))).hom.app X) n ≫
        HomologicalComplex.homologyMap
          (((SSet.chainComplexFunctor (ModuleCat.{u} S)).flip.obj X).map
            ((ModuleCat.extendScalars f).map ULift.moduleEquiv.toModuleIso.hom ≫
              (letI := f.toAlgebra; (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso.hom)))
          n :=
  (rfl)

/-- The identification of the extension of scalars of the homology with coefficients in `R` with
the homology with coefficients in `S` is natural in the simplicial set. -/
@[reassoc]
theorem homologyExtendScalarsIso_hom_naturality {R S : Type u} [CommRing R] [CommRing S]
    {X Y : SSet.{u}} (g : X ⟶ Y) (f : R →+* S)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f)] (n : ℕ) :
    (ModuleCat.extendScalars f).map (SSet.homologyMap g (ModuleCat.of R (ULift.{u} R)) n) ≫
        (Y.homologyExtendScalarsIso f n).hom =
      (X.homologyExtendScalarsIso f n).hom ≫ SSet.homologyMap g (ModuleCat.of S S) n := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := ModuleCat.extendScalars f
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let M := ModuleCat.of R (ULift.{u} R)
  let eM : F.obj M ≅ ModuleCat.of S S := F.mapIso ULift.moduleEquiv.toModuleIso ≪≫
    (letI := f.toAlgebra; (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso)
  -- `homologyExtendScalarsIso` is the composite of three comparisons, each natural.
  have h₁ := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.down ℕ) n).map (chainComplexMap g M)) F
  have h₂ := congrArg (HomologicalComplex.homologyMap · n)
    ((SSet.chainComplexFunctorObjCompMapIso F M).hom.naturality g)
  have h₃ := congrArg (HomologicalComplex.homologyMap · n)
    (((SSet.chainComplexFunctor (ModuleCat.{u} S)).map eM.hom).naturality g)
  simp only [HomologicalComplex.homologyMap_comp, Functor.comp_map] at h₂ h₃
  rw [homologyExtendScalarsIso_hom, homologyExtendScalarsIso_hom]
  -- The squares name the same objects in different unfolded forms, so they are chained explicitly.
  exact ((reassoc_of% h₁) _).trans <| congrArg (_ ≫ ·) <| ((reassoc_of% h₂) _).trans <|
    congrArg (_ ≫ ·) h₃

end SSet
