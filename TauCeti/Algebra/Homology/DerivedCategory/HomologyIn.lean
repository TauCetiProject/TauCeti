/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import TauCeti.Algebra.Homology.DerivedCategory.ExactFunctor
public import TauCeti.CategoryTheory.ObjectProperty.Extensions

/-!
# Objects of the derived category with homology in a given class

Let `C` be an abelian category and `P` a property of objects of `C`. This file defines the
property `DerivedCategory.homologyIn P` of objects of the derived category `D(C)` whose homology
objects in all degrees satisfy `P`; it is often written `D_P(C)`. For example, for the category of
`𝒪_X`-modules on a scheme `X` and `P` quasi-coherence, this is the derived category `D_QCoh(𝒪_X)`
of complexes with quasi-coherent cohomology sheaves.

When `P` is closed under isomorphisms, contains zero and is closed under kernels, cokernels and
extensions (a weak Serre subcategory), `homologyIn P` is a triangulated subcategory of `D(C)`: it
is stable under shifts, and the long exact homology sequence of a distinguished triangle shows
that it is closed under extensions. If the homology functors preserve colimits of some shape and
`P` is closed under them, then so is `homologyIn P`; this applies to coproducts in a category with
exact coproducts, for instance a Grothendieck abelian category. An object placed in one degree
lies in `homologyIn P` exactly when it satisfies `P`, and the functor induced by an exact functor
sends `homologyIn P` into `homologyIn P'` as soon as the exact functor sends `P` into `P'`.

## Main results

* `DerivedCategory.homologyIn`: the objects of `D(C)` whose homology objects all satisfy `P`.
* `DerivedCategory.homologyIn` is a triangulated subcategory when `P` is a weak Serre subcategory
  (an instance of `CategoryTheory.ObjectProperty.IsTriangulated`).
* `DerivedCategory.homologyIn_singleFunctor_obj_iff`: an object placed in one degree lies in
  `homologyIn P` if and only if it satisfies `P`.
* `DerivedCategory.homologyIn_mapDerivedCategory_obj`: exact functors preserve `homologyIn`.

## References

* The Stacks project, chapter Derived Categories: the triangulated subcategory `D_B(A)` of
  complexes with cohomology in a weak Serre subcategory `B` of an abelian category `A`.
-/

public section

open CategoryTheory Limits Pretriangulated ZeroObject

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

namespace DerivedCategory

variable (P : ObjectProperty C)

/-- The objects of the derived category `D(C)` all of whose homology objects satisfy `P`, often
written `D_P(C)`. -/
def homologyIn : ObjectProperty (DerivedCategory C) :=
  fun K ↦ ∀ n : ℤ, P ((homologyFunctor C n).obj K)

variable {P} in
theorem homologyIn_iff (K : DerivedCategory C) :
    homologyIn P K ↔ ∀ n : ℤ, P ((homologyFunctor C n).obj K) :=
  Iff.rfl

instance [P.IsClosedUnderIsomorphisms] : (homologyIn P).IsClosedUnderIsomorphisms where
  of_iso e hK n := P.prop_of_iso ((homologyFunctor C n).mapIso e) (hK n)

instance [P.IsClosedUnderIsomorphisms] : (homologyIn P).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun K hK n ↦
    P.prop_of_iso (((homologyFunctor C 0).shiftIso a n (a + n) rfl).app K).symm (hK (a + n))⟩

instance [P.IsClosedUnderIsomorphisms] [P.ContainsZero] : (homologyIn P).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun n ↦
    P.prop_of_isZero ((homologyFunctor C n).map_isZero (isZero_zero _))⟩

instance [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderExtensions] : (homologyIn P).IsTriangulatedClosed₂ :=
  .mk' fun T hT h₁ h₃ n ↦
    P.prop_X₂_of_exact_of_exact_of_exact (HomologySequence.exact₂ T hT n) _ _
      (HomologySequence.exact₁ T hT (n - 1) n) (HomologySequence.exact₃ T hT n (n + 1))
      (h₃ (n - 1)) (h₁ n) (h₃ n) (h₁ (n + 1))

/-- When `P` is a weak Serre subcategory, the objects of `D(C)` with homology in `P` form a
triangulated subcategory. -/
instance [P.IsClosedUnderIsomorphisms] [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] : (homologyIn P).IsTriangulated where

/-- If the homology functors preserve colimits of shape `J` and `P` is closed under them, then
`homologyIn P` is closed under colimits of shape `J`. -/
instance {J : Type*} [Category* J] [∀ n, PreservesColimitsOfShape J (homologyFunctor C n)]
    [P.IsClosedUnderColimitsOfShape J] : (homologyIn P).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro _ ⟨h⟩ n
    exact P.prop_of_isColimit (isColimitOfPreserves (homologyFunctor C n) h.isColimit)
      (fun j ↦ h.prop_diag_obj j n)

variable {P} in
/-- An object placed in one degree has homology in `P` if and only if it satisfies `P`. -/
@[simp]
theorem homologyIn_singleFunctor_obj_iff [P.IsClosedUnderIsomorphisms] [P.ContainsZero] (A : C)
    (n : ℤ) : homologyIn P ((singleFunctor C n).obj A) ↔ P A := by
  refine ⟨fun h ↦ P.prop_of_iso ((singleFunctorCompHomologyFunctorIso C n).app A) (h n),
    fun h m ↦ ?_⟩
  by_cases hmn : m = n
  · subst hmn
    exact P.prop_of_iso ((singleFunctorCompHomologyFunctorIso C m).app A).symm h
  · -- in the other degrees the homology vanishes
    exact P.prop_of_isZero ((HomologicalComplex.isZero_single_obj_homology _ _ A m hmn).of_iso
      ((homologyFunctor C m).mapIso ((singleFunctorIsoCompQ C n).app A) ≪≫
        (homologyFunctorFactors C m).app _))

/-- The functor on derived categories induced by an exact functor `F` sends objects with homology
in `P` to objects with homology in `P'`, as soon as `F` sends objects satisfying `P` to objects
satisfying `P'`. -/
theorem homologyIn_mapDerivedCategory_obj {D : Type*} [Category* D] [Abelian D]
    [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {P : ObjectProperty C} {P' : ObjectProperty D}
    [P'.IsClosedUnderIsomorphisms] (hF : ∀ A, P A → P' (F.obj A)) {K : DerivedCategory C}
    (hK : homologyIn P K) : homologyIn P' (F.mapDerivedCategory.obj K) := fun n ↦
  P'.prop_of_iso ((F.mapDerivedCategoryCompHomologyFunctorIso n).app K).symm (hF _ (hK n))

end DerivedCategory
