/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Cone

/-!
# A square-zero curved duplex

On each parity take `A ⊞ A`, and in both directions use the map that sends the first summand
to the second and kills the second. Sending the second summand back to the first contracts the
duplex. The parity shift negates both differentials.
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
@[expose] noncomputable def squareZero (A : C) : CurvedDuplex C (0 : R) where
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
theorem nullHomotopicMap_squareZero (A : C) :
    nullHomotopicMap (X := squareZero (R := R) A) (Y := squareZero (R := R) A)
      (biprod.snd ≫ biprod.inl) (biprod.snd ≫ biprod.inl) = 𝟙 _ := by
  ext <;> simp [squareZero, ← biprod.total]

/-- The square-zero duplex is zero in the homotopy category. -/
theorem isZero_quotientFunctor_obj_squareZero (A : C) :
    IsZero ((nullHomotopic C (0 : R)).quotientFunctor.obj (squareZero (R := R) A)) := by
  rw [MorphismIdeal.isZero_quotientFunctor_obj_iff, mem_nullHomotopic_iff]
  exact ⟨_, _, nullHomotopicMap_squareZero (R := R) A⟩

example (A : C) :
    ((parityShift C (0 : R)).obj (squareZero (R := R) A)).d₀ =
      -(biprod.fst ≫ biprod.inr : A ⊞ A ⟶ A ⊞ A) := by
  simp [squareZero]

example (A : C) :
    ((parityShift C (0 : R)).obj (squareZero (R := R) A)).d₁ =
      -(biprod.fst ≫ biprod.inr : A ⊞ A ⟶ A ⊞ A) := by
  simp [squareZero]

example (A : C) :
    IsZero ((nullHomotopic C (0 : R)).quotientFunctor.obj
      (cone (𝟙 (squareZero (R := R) A)))) :=
  isZero_quotientFunctor_obj_cone_isIso _

end CurvedDuplex

end TauCeti
