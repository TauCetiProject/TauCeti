/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Whitehead's isomorphism of a binary biproduct

Whitehead's lemma says that for an invertible matrix `u` the block matrix `diag(u, u⁻¹)` is a
product of elementary matrices. Its categorical form, for objects `X`, `Y` of a preadditive
category with binary biproducts and morphisms `b : X ⟶ Y`, `c : Y ⟶ X`, is the isomorphism

```text
Biprod.whiteheadIso b c : X ⊞ Y ≅ Y ⊞ X,
```

the composite of the unipotent isomorphisms with off-diagonal entries `c`, `-b`, `c`, the sign
`𝟙 ⊞ -𝟙` and the braiding. It is an isomorphism for **all** `b` and `c`, and its matrix is

```text
( b            𝟙 - b ≫ c         )
( c ≫ b - 𝟙   c + (c - c ≫ b ≫ c) ),
```

so that it is the diagonal `biprod.map b c` as soon as `b` and `c` are mutually inverse
(`Biprod.whiteheadIso_hom_eq_biprod_map`). The point of the explicit formula is that it can be
transported along an additive functor `F`: when `F.map b` and `F.map c` are mutually inverse but
`b` and `c` are not, `F` still sends `Biprod.whiteheadIso b c` to the diagonal isomorphism with
entries `F.map b` and `F.map c`. For a full additive functor every isomorphism `F X ≅ F Y` has
this form, so its diagonal sum with its inverse lifts to an isomorphism `X ⊞ Y ≅ Y ⊞ X`. This is
the step behind the stable equality criterion of the relative Grothendieck group of a full
functor.

## Main definitions

* `CategoryTheory.Biprod.whiteheadIso b c`: the isomorphism `X ⊞ Y ≅ Y ⊞ X` above.

## Main results

* `CategoryTheory.Biprod.whiteheadIso_hom`, `CategoryTheory.Biprod.whiteheadIso_inv`: its matrix
  and the matrix of its inverse.
* `CategoryTheory.Biprod.whiteheadIso_hom_fst`, `CategoryTheory.Biprod.whiteheadIso_hom_snd`: its
  two components, and `CategoryTheory.Biprod.whiteheadIso_inv_fst`,
  `CategoryTheory.Biprod.whiteheadIso_inv_snd` those of its inverse.
* `CategoryTheory.Biprod.whiteheadIso_hom_eq_biprod_map`: it is `biprod.map b c` when `b` and `c`
  are mutually inverse.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Chapter III, Lemma 1.3.3
  (Whitehead's lemma), and Chapter II, Exercise 2.17, where it is used for the relative group of
  a cofinal functor.
-/

public section

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C] {X Y : C}

namespace Biprod

/-- The sign isomorphism `𝟙 ⊞ -𝟙` of a binary biproduct. -/
private noncomputable def negSnd (X Y : C) : X ⊞ Y ≅ X ⊞ Y where
  hom := biprod.map (𝟙 X) (-𝟙 Y)
  inv := biprod.map (𝟙 X) (-𝟙 Y)

/-- **Whitehead's isomorphism.** For arbitrary morphisms `b : X ⟶ Y` and `c : Y ⟶ X`, the
isomorphism `X ⊞ Y ≅ Y ⊞ X` obtained by composing the unipotent isomorphisms with off-diagonal
entries `c`, `-b` and `c`, the sign `𝟙 ⊞ -𝟙` and the braiding. Its matrix is
`Biprod.ofComponents b (𝟙 - b ≫ c) (c ≫ b - 𝟙) (c + (c - c ≫ b ≫ c))`
(`CategoryTheory.Biprod.whiteheadIso_hom`); when `b` and `c` are mutually inverse it is
`biprod.map b c` (`CategoryTheory.Biprod.whiteheadIso_hom_eq_biprod_map`). -/
noncomputable def whiteheadIso (b : X ⟶ Y) (c : Y ⟶ X) : X ⊞ Y ≅ Y ⊞ X :=
  unipotentLower c ≪≫ unipotentUpper (-b) ≪≫ unipotentLower c ≪≫ negSnd X Y ≪≫
    biprod.braiding X Y

/-- The matrix of Whitehead's isomorphism. -/
theorem whiteheadIso_hom (b : X ⟶ Y) (c : Y ⟶ X) :
    (whiteheadIso b c).hom =
      ofComponents b (𝟙 X - b ≫ c) (c ≫ b - 𝟙 Y) (c + (c - c ≫ b ≫ c)) := by
  have hneg : (negSnd X Y).hom = ofComponents (𝟙 X) 0 0 (-𝟙 Y) := by ext <;> simp [negSnd]
  have hbraid : (biprod.braiding X Y).hom = ofComponents 0 (𝟙 X) (𝟙 Y) 0 := by ext <;> simp
  simp only [whiteheadIso, Iso.trans_hom, unipotentLower_hom, unipotentUpper_hom, hneg, hbraid,
    ofComponents_comp]
  congr 1 <;> simp <;> abel

/-- The matrix of the inverse of Whitehead's isomorphism. -/
theorem whiteheadIso_inv (b : X ⟶ Y) (c : Y ⟶ X) :
    (whiteheadIso b c).inv =
      ofComponents (c + (c - c ≫ b ≫ c)) (c ≫ b - 𝟙 Y) (𝟙 X - b ≫ c) b := by
  have hneg : (negSnd X Y).inv = ofComponents (𝟙 X) 0 0 (-𝟙 Y) := by ext <;> simp [negSnd]
  have hbraid : (biprod.braiding X Y).inv = ofComponents 0 (𝟙 Y) (𝟙 X) 0 := by ext <;> simp
  simp only [whiteheadIso, Iso.trans_inv, unipotentLower_inv, unipotentUpper_inv, hneg, hbraid,
    ofComponents_comp]
  congr 1 <;> simp <;> abel

/-- The first component of Whitehead's isomorphism. -/
@[reassoc (attr := simp)]
theorem whiteheadIso_hom_fst (b : X ⟶ Y) (c : Y ⟶ X) :
    (whiteheadIso b c).hom ≫ biprod.fst = biprod.fst ≫ b + biprod.snd ≫ (c ≫ b - 𝟙 Y) := by
  rw [whiteheadIso_hom, ofComponents_fst]

/-- The second component of Whitehead's isomorphism. -/
@[reassoc (attr := simp)]
theorem whiteheadIso_hom_snd (b : X ⟶ Y) (c : Y ⟶ X) :
    (whiteheadIso b c).hom ≫ biprod.snd =
      biprod.fst ≫ (𝟙 X - b ≫ c) + biprod.snd ≫ (c + (c - c ≫ b ≫ c)) := by
  rw [whiteheadIso_hom, ofComponents_snd]

/-- The first component of the inverse of Whitehead's isomorphism. -/
@[reassoc (attr := simp)]
theorem whiteheadIso_inv_fst (b : X ⟶ Y) (c : Y ⟶ X) :
    (whiteheadIso b c).inv ≫ biprod.fst =
      biprod.fst ≫ (c + (c - c ≫ b ≫ c)) + biprod.snd ≫ (𝟙 X - b ≫ c) := by
  rw [whiteheadIso_inv, ofComponents_fst]

/-- The second component of the inverse of Whitehead's isomorphism. -/
@[reassoc (attr := simp)]
theorem whiteheadIso_inv_snd (b : X ⟶ Y) (c : Y ⟶ X) :
    (whiteheadIso b c).inv ≫ biprod.snd = biprod.fst ≫ (c ≫ b - 𝟙 Y) + biprod.snd ≫ b := by
  rw [whiteheadIso_inv, ofComponents_snd]

/-- **Whitehead's lemma.** For mutually inverse `b` and `c`, the diagonal isomorphism
`biprod.map b c : X ⊞ Y ⟶ Y ⊞ X` is Whitehead's isomorphism, a composite of unipotent
isomorphisms, a sign and the braiding. -/
theorem whiteheadIso_hom_eq_biprod_map {b : X ⟶ Y} {c : Y ⟶ X} (hbc : b ≫ c = 𝟙 X)
    (hcb : c ≫ b = 𝟙 Y) : (whiteheadIso b c).hom = biprod.map b c := by
  ext <;> simp [whiteheadIso_hom, hbc, hcb]

end Biprod

end CategoryTheory
