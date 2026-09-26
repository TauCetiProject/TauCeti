/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Duplex
public import TauCeti.Algebra.Homology.Curved.SquareZeroDuplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The two-periodic complex of a square-zero duplex

The square-zero duplex has the same differential in both parities. Its associated two-periodic
complex has zero homology in both parities whenever homology exists.
-/

public section

universe w v u

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

namespace CurvedDuplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {R : Type w} [Semiring R] [Linear R C]

example (A : C) :
    ((toPeriodicComplex C R).obj (squareZero (R := R) A)).d 0 1 =
      (biprod.fst ≫ biprod.inr : A ⊞ A ⟶ A ⊞ A) := by
  simp

example (A : C) :
    ((toPeriodicComplex C R).obj (squareZero (R := R) A)).d 1 0 =
      (biprod.fst ≫ biprod.inr : A ⊞ A ⟶ A ⊞ A) := by
  simp

/-- The two-periodic complex associated to the square-zero duplex has zero homology in each
parity. -/
theorem isZero_squareZero_periodicHomology [CategoryWithHomology C] (A : C) (i : ZMod 2) :
    IsZero (((toPeriodicComplex C R).obj (squareZero (R := R) A)).homology i) := by
  let K := (toPeriodicComplex C R).obj (squareZero (R := R) A)
  have h₀ := isZero_quotientFunctor_obj_squareZero (R := R) A
  have h₁ : IsZero ((_root_.HomotopyCategory.quotient C
      (ComplexShape.up (ZMod 2))).obj K) := by
    simpa only [K, HomotopyCategory.toPeriodicComplex_obj_quotientFunctor_obj] using
      Functor.map_isZero (HomotopyCategory.toPeriodicComplex C R) h₀
  have h₂ := Functor.map_isZero
    (_root_.HomotopyCategory.homologyFunctor C (ComplexShape.up (ZMod 2)) i) h₁
  exact ((_root_.HomotopyCategory.homologyFunctorFactors C
    (ComplexShape.up (ZMod 2)) i).app K).isZero_iff.mp h₂

end CurvedDuplex

end TauCeti
