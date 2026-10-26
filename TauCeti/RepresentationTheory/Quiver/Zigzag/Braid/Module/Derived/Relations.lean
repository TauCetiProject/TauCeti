/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Module.Derived.Basic

/-!
# The commuting and braid isomorphisms on the derived category

The positive derived vertex tensor functors on the ordinary derived category of internally
graded zigzag modules commute naturally at distinct nonadjacent vertices. At adjacent vertices,
the words with vertex sequences `i,j,i` and `j,i,j` are naturally isomorphic.

Comparisons with the standard localization `DerivedCategory.Qh` identify derived tensor words
of length two and three with the corresponding homotopy words after localization. On the image
of a homotopy object, each descended commuting or braid component is the image of the original
homotopy component, conjugated by these word-comparison isomorphisms.

These statements use a commutative coefficient ring, a finite simple graph and the supplied
`HasDerivedCategory` interface. The internal grading of the modules and the external
cohomological degree of their cochain complexes remain independent.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Functor

universe u w z

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "c" => ComplexShape.up ℤ

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

-- Keep the grading parameters explicit in the section instance binder.
variable [HasDerivedCategory.{z}
  (GradedModuleCat.{max u w} (zigzagAlgebraInternalGrading k G).piece)]

@[instance_reducible]
private def vertexQhSquare (i : V) :
    CatCommSq
      (_root_.DerivedCategory.Qh.{z} (C := GradedModuleCat.{max u w} (Γ).piece))
      (zigzagBraidAutoequivalence k G i).functor
      (zigzagBraidDerivedFunctor k G i)
      _root_.DerivedCategory.Qh.{z} :=
  CatCommSq.mk (Localization.Lifting.iso _ (HomotopyCategory.quasiIso
    (GradedModuleCat.{max u w} (Γ).piece) c) _ _)

/-- The two-vertex derived tensor word agrees with its homotopy word through `Qh`. -/
def zigzagBraidDerivedFunctorCompQhIso (i j : V) :
    _root_.DerivedCategory.Qh.{z} (C := GradedModuleCat.{max u w} (Γ).piece) ⋙
        (zigzagBraidDerivedFunctor k G i ⋙ zigzagBraidDerivedFunctor k G j) ≅
      ((zigzagBraidAutoequivalence k G i).functor ⋙
        (zigzagBraidAutoequivalence k G j).functor) ⋙ _root_.DerivedCategory.Qh.{z} := by
  letI := CatCommSq.vComp' (vertexQhSquare k G i) (vertexQhSquare k G j)
  exact CatCommSq.iso _ _ _ _

/-- The three-vertex derived tensor word agrees with its homotopy word through `Qh`. -/
def zigzagBraidDerivedFunctorTripleQhIso (i j l : V) :
    _root_.DerivedCategory.Qh.{z} (C := GradedModuleCat.{max u w} (Γ).piece) ⋙
        (zigzagBraidDerivedFunctor k G i ⋙
          (zigzagBraidDerivedFunctor k G j ⋙ zigzagBraidDerivedFunctor k G l)) ≅
      ((zigzagBraidAutoequivalence k G i).functor ⋙
        ((zigzagBraidAutoequivalence k G j).functor ⋙
          (zigzagBraidAutoequivalence k G l).functor)) ⋙ _root_.DerivedCategory.Qh.{z} := by
  letI := CatCommSq.vComp' (vertexQhSquare k G i)
    (CatCommSq.vComp' (vertexQhSquare k G j) (vertexQhSquare k G l))
  exact CatCommSq.iso _ _ _ _

/-- Distinct nonadjacent derived vertex functors commute by descent of the homotopy isomorphism. -/
def zigzagBraidDerivedFunctorCommIso {i j : V} (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    zigzagBraidDerivedFunctor k G i ⋙ zigzagBraidDerivedFunctor k G j ≅
      zigzagBraidDerivedFunctor k G j ⋙ zigzagBraidDerivedFunctor k G i :=
  Localization.liftNatIso _root_.DerivedCategory.Qh.{z}
    (HomotopyCategory.quasiIso (GradedModuleCat.{max u w} (Γ).piece) c)
    (_root_.DerivedCategory.Qh.{z} ⋙
      (zigzagBraidDerivedFunctor k G i ⋙ zigzagBraidDerivedFunctor k G j))
    (_root_.DerivedCategory.Qh.{z} ⋙
      (zigzagBraidDerivedFunctor k G j ⋙ zigzagBraidDerivedFunctor k G i)) _ _
    (zigzagBraidDerivedFunctorCompQhIso k G i j ≪≫
      isoWhiskerRight (zigzagBraidAutoequivalenceCommIso k G hij hadj)
        _root_.DerivedCategory.Qh.{z} ≪≫ (zigzagBraidDerivedFunctorCompQhIso k G j i).symm)

/-- Adjacent derived vertex functors satisfy the braid isomorphism inherited from homotopy. -/
def zigzagBraidDerivedFunctorBraidIso {i j : V} (h : G.Adj i j) :
    zigzagBraidDerivedFunctor k G i ⋙
        (zigzagBraidDerivedFunctor k G j ⋙ zigzagBraidDerivedFunctor k G i) ≅
      zigzagBraidDerivedFunctor k G j ⋙
        (zigzagBraidDerivedFunctor k G i ⋙ zigzagBraidDerivedFunctor k G j) :=
  Localization.liftNatIso _root_.DerivedCategory.Qh.{z}
    (HomotopyCategory.quasiIso (GradedModuleCat.{max u w} (Γ).piece) c)
    (_root_.DerivedCategory.Qh.{z} ⋙
      (zigzagBraidDerivedFunctor k G i ⋙
        (zigzagBraidDerivedFunctor k G j ⋙ zigzagBraidDerivedFunctor k G i)))
    (_root_.DerivedCategory.Qh.{z} ⋙
      (zigzagBraidDerivedFunctor k G j ⋙
        (zigzagBraidDerivedFunctor k G i ⋙ zigzagBraidDerivedFunctor k G j))) _ _
    (zigzagBraidDerivedFunctorTripleQhIso k G i j i ≪≫
      isoWhiskerRight (zigzagBraidAutoequivalenceBraidIso k G h)
        _root_.DerivedCategory.Qh.{z} ≪≫
      (zigzagBraidDerivedFunctorTripleQhIso k G j i j).symm)

/-- On a homotopy image, the descended commuting map is the original map conjugated by `Qh`. -/
@[simp]
theorem zigzagBraidDerivedFunctorCommIso_hom_app_Qh_obj {i j : V} (hij : i ≠ j)
    (hadj : ¬ G.Adj i j) (X : HomotopyCategory (GradedModuleCat.{max u w} (Γ).piece) c) :
    (zigzagBraidDerivedFunctorCommIso k G hij hadj).hom.app
        (_root_.DerivedCategory.Qh.{z}.obj X) =
      (zigzagBraidDerivedFunctorCompQhIso k G i j).hom.app X ≫
        _root_.DerivedCategory.Qh.{z}.map
          ((zigzagBraidAutoequivalenceCommIso k G hij hadj).hom.app X) ≫
        (zigzagBraidDerivedFunctorCompQhIso k G j i).inv.app X := by
  simp [zigzagBraidDerivedFunctorCommIso]

/-- On a homotopy image, the descended braid map is the original map conjugated by `Qh`. -/
@[simp]
theorem zigzagBraidDerivedFunctorBraidIso_hom_app_Qh_obj {i j : V} (h : G.Adj i j)
    (X : HomotopyCategory (GradedModuleCat.{max u w} (Γ).piece) c) :
    (zigzagBraidDerivedFunctorBraidIso k G h).hom.app (_root_.DerivedCategory.Qh.{z}.obj X) =
      (zigzagBraidDerivedFunctorTripleQhIso k G i j i).hom.app X ≫
        _root_.DerivedCategory.Qh.{z}.map
          ((zigzagBraidAutoequivalenceBraidIso k G h).hom.app X) ≫
        (zigzagBraidDerivedFunctorTripleQhIso k G j i j).inv.app X := by
  simp [zigzagBraidDerivedFunctorBraidIso]

end TauCeti
