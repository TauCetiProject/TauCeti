/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Duplex
public import TauCeti.Algebra.Homology.Curved.Cone
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# A square-zero two-periodic duplex

On each parity take `A ⊞ A`, and in both directions use the map that sends the first summand
to the second and kills the second. The two composites vanish. The map sending the second
summand back to the first contracts the duplex, so its associated two-periodic complex has
zero homology in both parities whenever homology exists. The shift negates the two differentials,
and the cone of the identity is contractible. The example makes the curvature-zero specialization
of duplexes into genuine two-periodic complexes explicit.
-/

public section

universe w v u

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

namespace CurvedDuplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {R : Type w} [Semiring R] [Linear R C]

/-- The square-zero duplex with both parity pieces `A ⊞ A` and differential
`(a,b) ↦ (0,a)`. -/
@[expose, implicit_reducible] noncomputable def squareZero (A : C) : CurvedDuplex C (0 : R) where
  X₀ := A ⊞ A
  X₁ := A ⊞ A
  d₀ := biprod.fst ≫ biprod.inr
  d₁ := biprod.fst ≫ biprod.inr
  d₀_comp_d₁ := by simp
  d₁_comp_d₀ := by simp

@[simp] theorem squareZero_X₀ (A : C) : (squareZero (R := R) A).X₀ = (A ⊞ A) := rfl
@[simp] theorem squareZero_X₁ (A : C) : (squareZero (R := R) A).X₁ = (A ⊞ A) := rfl
@[simp] theorem squareZero_d₀ (A : C) :
    (squareZero (R := R) A).d₀ = biprod.fst ≫ biprod.inr := rfl
@[simp] theorem squareZero_d₁ (A : C) :
    (squareZero (R := R) A).d₁ = biprod.fst ≫ biprod.inr := rfl

/-- Sending the second summand to the first is a contracting homotopy of the square-zero
duplex. -/
theorem squareZero_nullHomotopicMap (A : C) :
    nullHomotopicMap (X := squareZero (R := R) A) (Y := squareZero (R := R) A)
      (biprod.snd ≫ biprod.inl) (biprod.snd ≫ biprod.inl) = 𝟙 _ := by
  ext <;> simp [squareZero, ← biprod.total]

/-- The square-zero duplex is zero in the homotopy category. -/
theorem squareZero_isZero_homotopyCategory (A : C) :
    IsZero ((nullHomotopic C (0 : R)).quotientFunctor.obj (squareZero (R := R) A)) := by
  rw [MorphismIdeal.isZero_quotientFunctor_obj_iff, mem_nullHomotopic_iff]
  exact ⟨_, _, squareZero_nullHomotopicMap (R := R) A⟩

/-- The two-periodic complex associated to the square-zero duplex has the displayed
differential in even degree. -/
@[simp] theorem squareZero_toPeriodicComplex_d_zero_one (A : C) :
    ((toPeriodicComplex C R).obj (squareZero (R := R) A)).d 0 1 =
      (biprod.fst ≫ biprod.inr : A ⊞ A ⟶ A ⊞ A) := by
  simp

/-- The two-periodic complex associated to the square-zero duplex has the same differential
in odd degree. -/
@[simp] theorem squareZero_toPeriodicComplex_d_one_zero (A : C) :
    ((toPeriodicComplex C R).obj (squareZero (R := R) A)).d 1 0 =
      (biprod.fst ≫ biprod.inr : A ⊞ A ⟶ A ⊞ A) := by
  simp

/-- The associated two-periodic complex has zero homology in each parity. This follows from
its explicit contraction, through the comparison of duplex and complex homotopies. -/
theorem squareZero_isZero_periodicHomology [CategoryWithHomology C] (A : C) (i : ZMod 2) :
    IsZero (((toPeriodicComplex C R).obj (squareZero (R := R) A)).homology i) := by
  let K := (toPeriodicComplex C R).obj (squareZero (R := R) A)
  have h₀ := squareZero_isZero_homotopyCategory (R := R) A
  have h₁ : IsZero ((_root_.HomotopyCategory.quotient C
      (ComplexShape.up (ZMod 2))).obj K) := by
    simpa only [K, HomotopyCategory.toPeriodicComplex_obj_quotientFunctor_obj] using
      Functor.map_isZero (HomotopyCategory.toPeriodicComplex C R) h₀
  have h₂ := Functor.map_isZero
    (_root_.HomotopyCategory.homologyFunctor C (ComplexShape.up (ZMod 2)) i) h₁
  exact ((_root_.HomotopyCategory.homologyFunctorFactors C
    (ComplexShape.up (ZMod 2)) i).app K).isZero_iff.mp h₂

/-- The parity shift exchanges the two identical components and negates their differential. -/
@[simp] theorem squareZero_parityShift_d₀ (A : C) :
    ((parityShift C (0 : R)).obj (squareZero (R := R) A)).d₀ =
      -(biprod.fst ≫ biprod.inr : A ⊞ A ⟶ A ⊞ A) := by
  simp

/-- The parity shift exchanges the two identical components and negates their differential. -/
@[simp] theorem squareZero_parityShift_d₁ (A : C) :
    ((parityShift C (0 : R)).obj (squareZero (R := R) A)).d₁ =
      -(biprod.fst ≫ biprod.inr : A ⊞ A ⟶ A ⊞ A) := by
  simp

/-- The cone of the identity of the square-zero duplex is contractible. -/
theorem squareZero_isZero_cone_id (A : C) :
    IsZero ((nullHomotopic C (0 : R)).quotientFunctor.obj
      (cone (𝟙 (squareZero (R := R) A)))) :=
  isZero_quotientFunctor_obj_cone_isIso _

end CurvedDuplex

end TauCeti
