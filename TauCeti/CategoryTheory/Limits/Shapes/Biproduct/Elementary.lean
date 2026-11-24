/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Elementary binary biproduct constructions

This module collects basic constructions on binary biproducts that only depend on Mathlib's
binary biproduct interface:

* `TauCeti.biprodFourMiddleIso`: the middle-four interchange isomorphism
  `(W ⊞ X) ⊞ (Y ⊞ Z) ≅ (W ⊞ Y) ⊞ (X ⊞ Z)` together with its projection lemmas.
* `TauCeti.addCommMonoidOfBiprod`: constructing an `AddCommMonoid` structure from a surjective,
  isomorphism-invariant object map sending binary biproducts to addition and the zero object to `0`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v w u

section FourMiddle

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The middle-four interchange isomorphism `(W ⊞ X) ⊞ (Y ⊞ Z) ≅ (W ⊞ Y) ⊞ (X ⊞ Z)` for binary
biproducts. -/
noncomputable def biprodFourMiddleIso (W X Y Z : C)
    [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] [HasBinaryBiproduct (W ⊞ X) (Y ⊞ Z)]
    [HasBinaryBiproduct W Y] [HasBinaryBiproduct X Z] [HasBinaryBiproduct (W ⊞ Y) (X ⊞ Z)] :
    (W ⊞ X) ⊞ (Y ⊞ Z) ≅ (W ⊞ Y) ⊞ (X ⊞ Z) where
  hom := biprod.lift (biprod.lift (biprod.fst ≫ biprod.fst) (biprod.snd ≫ biprod.fst))
    (biprod.lift (biprod.fst ≫ biprod.snd) (biprod.snd ≫ biprod.snd))
  inv := biprod.lift (biprod.lift (biprod.fst ≫ biprod.fst) (biprod.snd ≫ biprod.fst))
    (biprod.lift (biprod.fst ≫ biprod.snd) (biprod.snd ≫ biprod.snd))
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

@[reassoc (attr := simp)]
theorem biprodFourMiddleIso_hom_fst_fst (W X Y Z : C)
    [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] [HasBinaryBiproduct (W ⊞ X) (Y ⊞ Z)]
    [HasBinaryBiproduct W Y] [HasBinaryBiproduct X Z] [HasBinaryBiproduct (W ⊞ Y) (X ⊞ Z)] :
    (biprodFourMiddleIso W X Y Z).hom ≫ biprod.fst ≫ biprod.fst =
      biprod.fst ≫ biprod.fst := by
  simp [biprodFourMiddleIso]

@[reassoc (attr := simp)]
theorem biprodFourMiddleIso_hom_fst_snd (W X Y Z : C)
    [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] [HasBinaryBiproduct (W ⊞ X) (Y ⊞ Z)]
    [HasBinaryBiproduct W Y] [HasBinaryBiproduct X Z] [HasBinaryBiproduct (W ⊞ Y) (X ⊞ Z)] :
    (biprodFourMiddleIso W X Y Z).hom ≫ biprod.fst ≫ biprod.snd =
      biprod.snd ≫ biprod.fst := by
  simp [biprodFourMiddleIso]

@[reassoc (attr := simp)]
theorem biprodFourMiddleIso_hom_snd_fst (W X Y Z : C)
    [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] [HasBinaryBiproduct (W ⊞ X) (Y ⊞ Z)]
    [HasBinaryBiproduct W Y] [HasBinaryBiproduct X Z] [HasBinaryBiproduct (W ⊞ Y) (X ⊞ Z)] :
    (biprodFourMiddleIso W X Y Z).hom ≫ biprod.snd ≫ biprod.fst =
      biprod.fst ≫ biprod.snd := by
  simp [biprodFourMiddleIso]

@[reassoc (attr := simp)]
theorem biprodFourMiddleIso_hom_snd_snd (W X Y Z : C)
    [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] [HasBinaryBiproduct (W ⊞ X) (Y ⊞ Z)]
    [HasBinaryBiproduct W Y] [HasBinaryBiproduct X Z] [HasBinaryBiproduct (W ⊞ Y) (X ⊞ Z)] :
    (biprodFourMiddleIso W X Y Z).hom ≫ biprod.snd ≫ biprod.snd =
      biprod.snd ≫ biprod.snd := by
  simp [biprodFourMiddleIso]

@[reassoc (attr := simp)]
theorem biprodFourMiddleIso_inv_fst_fst (W X Y Z : C)
    [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] [HasBinaryBiproduct (W ⊞ X) (Y ⊞ Z)]
    [HasBinaryBiproduct W Y] [HasBinaryBiproduct X Z] [HasBinaryBiproduct (W ⊞ Y) (X ⊞ Z)] :
    (biprodFourMiddleIso W X Y Z).inv ≫ biprod.fst ≫ biprod.fst =
      biprod.fst ≫ biprod.fst := by
  simp [biprodFourMiddleIso]

@[reassoc (attr := simp)]
theorem biprodFourMiddleIso_inv_fst_snd (W X Y Z : C)
    [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] [HasBinaryBiproduct (W ⊞ X) (Y ⊞ Z)]
    [HasBinaryBiproduct W Y] [HasBinaryBiproduct X Z] [HasBinaryBiproduct (W ⊞ Y) (X ⊞ Z)] :
    (biprodFourMiddleIso W X Y Z).inv ≫ biprod.fst ≫ biprod.snd =
      biprod.snd ≫ biprod.fst := by
  simp [biprodFourMiddleIso]

@[reassoc (attr := simp)]
theorem biprodFourMiddleIso_inv_snd_fst (W X Y Z : C)
    [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] [HasBinaryBiproduct (W ⊞ X) (Y ⊞ Z)]
    [HasBinaryBiproduct W Y] [HasBinaryBiproduct X Z] [HasBinaryBiproduct (W ⊞ Y) (X ⊞ Z)] :
    (biprodFourMiddleIso W X Y Z).inv ≫ biprod.snd ≫ biprod.fst =
      biprod.fst ≫ biprod.snd := by
  simp [biprodFourMiddleIso]

@[reassoc (attr := simp)]
theorem biprodFourMiddleIso_inv_snd_snd (W X Y Z : C)
    [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] [HasBinaryBiproduct (W ⊞ X) (Y ⊞ Z)]
    [HasBinaryBiproduct W Y] [HasBinaryBiproduct X Z] [HasBinaryBiproduct (W ⊞ Y) (X ⊞ Z)] :
    (biprodFourMiddleIso W X Y Z).inv ≫ biprod.snd ≫ biprod.snd =
      biprod.snd ≫ biprod.snd := by
  simp [biprodFourMiddleIso]

end FourMiddle

section AddCommMonoid

open ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  [HasBinaryBiproducts C]

/-- Construct an `AddCommMonoid` structure on a type `M` already equipped with `Add` and `Zero`
from a surjective, isomorphism-invariant object map `f : C → M` sending binary biproducts to
addition and the zero object to `0`. -/
@[expose, instance_reducible]
def addCommMonoidOfBiprod {M : Type w} [Add M] [Zero M] (f : C → M)
    (hsurj : Function.Surjective f) (hiso : ∀ ⦃X Y : C⦄, (X ≅ Y) → f X = f Y)
    (hbiprod : ∀ X Y : C, f (X ⊞ Y) = f X + f Y) (hzero : f 0 = 0) :
    AddCommMonoid M where
  nsmul := nsmulRec
  add_assoc a b c := by
    obtain ⟨X, rfl⟩ := hsurj a
    obtain ⟨Y, rfl⟩ := hsurj b
    obtain ⟨Z, rfl⟩ := hsurj c
    simpa only [hbiprod] using hiso (biprod.associator X Y Z)
  add_comm a b := by
    obtain ⟨X, rfl⟩ := hsurj a
    obtain ⟨Y, rfl⟩ := hsurj b
    simpa only [hbiprod] using hiso (biprod.braiding X Y)
  add_zero a := by
    obtain ⟨X, rfl⟩ := hsurj a
    simpa only [hbiprod, hzero] using (hiso (isoBiprodZero (isZero_zero C))).symm
  zero_add a := by
    obtain ⟨X, rfl⟩ := hsurj a
    simpa only [hbiprod, hzero] using (hiso (isoZeroBiprod (isZero_zero C))).symm

end AddCommMonoid

end TauCeti
