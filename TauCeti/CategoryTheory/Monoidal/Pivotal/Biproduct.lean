/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Trace

/-!
# Pivotal traces and dimensions of biproducts

The left and right trace of an endomorphism of a finite biproduct are the sums of the traces
of its diagonal components. In particular, both pivotal dimensions are additive on finite
biproducts. These identities allow dimensions to descend through the direct-sum relations in a
Grothendieck group.

The diagonal formulas apply to arbitrary endomorphisms, including ones with nonzero
off-diagonal components. Only the particular biproduct in the statement is required to exist;
neither an abelian category nor existence of all finite biproducts is assumed.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [PivotalCategory C] [Preadditive C] [MonoidalPreadditive C]

section Finite

variable {ι : Type*} [Fintype ι] {X : ι → C} [HasBiproduct X]

/-- The left trace of an endomorphism of a finite biproduct is the sum of the left traces
of its diagonal components. -/
theorem leftTrace_biproduct (f : ⨁ X ⟶ ⨁ X) :
    leftTrace f = ∑ i, leftTrace (biproduct.ι X i ≫ f ≫ biproduct.π X i) := by
  calc
    leftTrace f = leftTrace ((∑ i, biproduct.π X i ≫ biproduct.ι X i) ≫ f) := by simp
    _ = ∑ i, leftTrace ((biproduct.π X i ≫ biproduct.ι X i) ≫ f) := by
      rw [Preadditive.sum_comp, leftTrace_sum]
    _ = ∑ i, leftTrace (biproduct.ι X i ≫ f ≫ biproduct.π X i) := by
      congr 1
      funext i
      rw [Category.assoc, leftTrace_comm, Category.assoc]

/-- The right trace of an endomorphism of a finite biproduct is the sum of the right traces
of its diagonal components. -/
theorem rightTrace_biproduct (f : ⨁ X ⟶ ⨁ X) :
    rightTrace f = ∑ i, rightTrace (biproduct.ι X i ≫ f ≫ biproduct.π X i) := by
  calc
    rightTrace f = rightTrace ((∑ i, biproduct.π X i ≫ biproduct.ι X i) ≫ f) := by simp
    _ = ∑ i, rightTrace ((biproduct.π X i ≫ biproduct.ι X i) ≫ f) := by
      rw [Preadditive.sum_comp, rightTrace_sum]
    _ = ∑ i, rightTrace (biproduct.ι X i ≫ f ≫ biproduct.π X i) := by
      congr 1
      funext i
      rw [Category.assoc, rightTrace_comm, Category.assoc]

/-- The left trace of a block-diagonal morphism is the sum of the left traces of its blocks. -/
@[simp]
theorem leftTrace_biproduct_map (f : ∀ i, X i ⟶ X i) :
    leftTrace (biproduct.map f) = ∑ i, leftTrace (f i) := by
  rw [leftTrace_biproduct]
  simp

/-- The right trace of a block-diagonal morphism is the sum of the right traces of its blocks. -/
@[simp]
theorem rightTrace_biproduct_map (f : ∀ i, X i ⟶ X i) :
    rightTrace (biproduct.map f) = ∑ i, rightTrace (f i) := by
  rw [rightTrace_biproduct]
  simp

/-- Left pivotal dimension is additive on finite biproducts. -/
@[simp]
theorem leftDim_biproduct : leftDim (⨁ X) = ∑ i, leftDim (X i) := by
  rw [← leftTrace_id, leftTrace_biproduct]
  simp

/-- Right pivotal dimension is additive on finite biproducts. -/
@[simp]
theorem rightDim_biproduct : rightDim (⨁ X) = ∑ i, rightDim (X i) := by
  rw [← rightTrace_id, rightTrace_biproduct]
  simp

end Finite

section Binary

variable {X Y : C} [HasBinaryBiproduct X Y]

/-- The left trace of an endomorphism of a binary biproduct is the sum of the left traces
of its two diagonal components. -/
theorem leftTrace_biprod (f : X ⊞ Y ⟶ X ⊞ Y) :
    leftTrace f = leftTrace (biprod.inl ≫ f ≫ biprod.fst) +
      leftTrace (biprod.inr ≫ f ≫ biprod.snd) := by
  calc
    leftTrace f = leftTrace ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ f) := by
      simp
    _ = _ := by
      rw [Preadditive.add_comp, leftTrace_add]
      simp only [Category.assoc, leftTrace_comm (biprod.fst : X ⊞ Y ⟶ X),
        leftTrace_comm (biprod.snd : X ⊞ Y ⟶ Y)]

/-- The right trace of an endomorphism of a binary biproduct is the sum of the right traces
of its two diagonal components. -/
theorem rightTrace_biprod (f : X ⊞ Y ⟶ X ⊞ Y) :
    rightTrace f = rightTrace (biprod.inl ≫ f ≫ biprod.fst) +
      rightTrace (biprod.inr ≫ f ≫ biprod.snd) := by
  calc
    rightTrace f = rightTrace ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ f) := by
      simp
    _ = _ := by
      rw [Preadditive.add_comp, rightTrace_add]
      simp only [Category.assoc, rightTrace_comm (biprod.fst : X ⊞ Y ⟶ X),
        rightTrace_comm (biprod.snd : X ⊞ Y ⟶ Y)]

/-- The left trace of a binary block-diagonal morphism is the sum of its block traces. -/
@[simp]
theorem leftTrace_biprod_map (f : X ⟶ X) (g : Y ⟶ Y) :
    leftTrace (biprod.map f g) = leftTrace f + leftTrace g := by
  rw [leftTrace_biprod]
  simp

/-- The right trace of a binary block-diagonal morphism is the sum of its block traces. -/
@[simp]
theorem rightTrace_biprod_map (f : X ⟶ X) (g : Y ⟶ Y) :
    rightTrace (biprod.map f g) = rightTrace f + rightTrace g := by
  rw [rightTrace_biprod]
  simp

/-- Left pivotal dimension is additive on binary biproducts. -/
@[simp]
theorem leftDim_biprod : leftDim (X ⊞ Y) = leftDim X + leftDim Y := by
  rw [← leftTrace_id, leftTrace_biprod]
  simp

/-- Right pivotal dimension is additive on binary biproducts. -/
@[simp]
theorem rightDim_biprod : rightDim (X ⊞ Y) = rightDim X + rightDim Y := by
  rw [← rightTrace_id, rightTrace_biprod]
  simp

end Binary

end TauCeti
