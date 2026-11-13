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
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.MapHomologicalComplex
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
scalars of the homology with coefficients in `R` with the homology with coefficients in `S`.
The instance `ModuleCat.preservesFiniteLimits_extendScalars_intCastRat` supplies the exactness
for the flat map `ℤ → ℚ`, which compares integral and rational homology.

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

/-- Rational extension of scalars is exact, since `ℚ` is a localization of `ℤ`. -/
instance preservesFiniteLimits_extendScalars_intCastRat :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars (Int.castRingHom ℚ) : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ) := by
  have hflat : (Int.castRingHom ℚ).Flat := by
    -- RingHom.Flat uses the algebra induced by Int.castRingHom, whereas localization
    -- flatness uses the canonical integer action. These actions are definitionally equal;
    -- change aligns the instance arguments, which rewriting the proposition alone cannot do.
    change Module.Flat ℤ ℚ
    exact IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  exact ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat

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

end SSet
