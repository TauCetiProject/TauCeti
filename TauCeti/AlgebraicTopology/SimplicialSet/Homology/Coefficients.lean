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

For rational coefficients, extension of scalars along the flat map `ℤ → ℚ` commutes with homology.
`SSet.rationalHomologyExtendScalarsIso` compares rational extension of the integral homology
with rational homology, on the native chain and module carriers. This fixed rational
specialization needs no manifold, orientation, compactness or finite CW hypothesis.

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

/-- Rational extension of integral simplicial homology is rational homology. The integral
coefficient object is the native `ULift ℤ`; the rational coefficient object is `ℚ`. -/
def rationalHomologyExtendScalarsIso (X : SSet.{0}) (n : ℕ) :
    (ModuleCat.extendScalars (Int.castRingHom ℚ)).obj
      (X.homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n) ≅
        X.homology (ModuleCat.of ℚ ℚ) n := by
  let F : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ := ModuleCat.extendScalars (Int.castRingHom ℚ)
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  let C := X.chainComplex R
  let eUnit : F.obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℚ ℚ :=
    (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toModuleIso
  let eR : F.obj R ≅ ModuleCat.of ℚ ℚ :=
    F.mapIso ULift.moduleEquiv.toModuleIso ≪≫ eUnit
  let eH : F.obj (C.homology n) ≅ X.homology (F.obj R) n :=
    ((C.sc n).mapHomologyIso F).symm ≪≫
      HomologicalComplex.homologyMapIso ((SSet.chainComplexFunctorObjCompMapIso F R).app X) n
  let eC : X.homology (F.obj R) n ≅ X.homology (ModuleCat.of ℚ ℚ) n :=
    HomologicalComplex.homologyMapIso
      (((SSet.chainComplexFunctor.{0} (ModuleCat.{0} ℚ)).flip.obj X).mapIso eR) n
  exact eH ≪≫ eC

end SSet
