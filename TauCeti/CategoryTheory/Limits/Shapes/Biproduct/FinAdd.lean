/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Biproducts of copies of an object indexed by `Fin (n + m)`

For an object `M`, the binary biproduct of the finite biproducts `Mⁿ` and `Mᵐ` is `Mⁿ⁺ᵐ`
(`TauCeti.biprodBiproductIso`): the summands of `Mⁿ` are the indices `Fin.castAdd m j` and the
summands of `Mᵐ` are the indices `Fin.natAdd n j` of `Mⁿ⁺ᵐ`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasFiniteBiproducts C]

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

variable (M : C)

/-- The biproduct of `Mⁿ` and `Mᵐ` is `Mⁿ⁺ᵐ`. -/
noncomputable def biprodBiproductIso (n m : ℕ) :
    (⨁ fun _ : Fin n ↦ M) ⊞ (⨁ fun _ : Fin m ↦ M) ≅ ⨁ fun _ : Fin (n + m) ↦ M where
  hom := biprod.desc (biproduct.desc fun j ↦ biproduct.ι (fun _ ↦ M) (Fin.castAdd m j))
    (biproduct.desc fun j ↦ biproduct.ι (fun _ ↦ M) (Fin.natAdd n j))
  inv := biproduct.desc fun k ↦ Fin.addCases (motive := fun _ ↦ M ⟶ _)
    (fun j ↦ biproduct.ι (fun _ : Fin n ↦ M) j ≫ biprod.inl)
    (fun j ↦ biproduct.ι (fun _ : Fin m ↦ M) j ≫ biprod.inr) k
  hom_inv_id := by
    ext <;> simp
  inv_hom_id := by
    refine biproduct.hom_ext' _ _ fun k ↦ ?_
    induction k using Fin.addCases <;> simp

variable {M} {n m : ℕ}

/-- `TauCeti.biprodBiproductIso` sends the `j`-th summand of `Mⁿ` to the summand
`Fin.castAdd m j` of `Mⁿ⁺ᵐ`. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_biprod_inl_biprodBiproductIso_hom (j : Fin n) :
    biproduct.ι (fun _ : Fin n ↦ M) j ≫ biprod.inl ≫ (biprodBiproductIso M n m).hom =
      biproduct.ι (fun _ : Fin (n + m) ↦ M) (Fin.castAdd m j) := by
  simp [biprodBiproductIso]

/-- `TauCeti.biprodBiproductIso` sends the `j`-th summand of `Mᵐ` to the summand
`Fin.natAdd n j` of `Mⁿ⁺ᵐ`. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_biprod_inr_biprodBiproductIso_hom (j : Fin m) :
    biproduct.ι (fun _ : Fin m ↦ M) j ≫ biprod.inr ≫ (biprodBiproductIso M n m).hom =
      biproduct.ι (fun _ : Fin (n + m) ↦ M) (Fin.natAdd n j) := by
  simp [biprodBiproductIso]

/-- The inverse of `TauCeti.biprodBiproductIso` sends the summand `Fin.castAdd m j` of `Mⁿ⁺ᵐ`
to the `j`-th summand of `Mⁿ`. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_castAdd_biprodBiproductIso_inv (j : Fin n) :
    biproduct.ι (fun _ : Fin (n + m) ↦ M) (Fin.castAdd m j) ≫ (biprodBiproductIso M n m).inv =
      biproduct.ι (fun _ : Fin n ↦ M) j ≫ biprod.inl := by
  rw [Iso.comp_inv_eq, Category.assoc, biproduct_ι_biprod_inl_biprodBiproductIso_hom]

/-- The inverse of `TauCeti.biprodBiproductIso` sends the summand `Fin.natAdd n j` of `Mⁿ⁺ᵐ`
to the `j`-th summand of `Mᵐ`. -/
@[reassoc (attr := simp)]
theorem biproduct_ι_natAdd_biprodBiproductIso_inv (j : Fin m) :
    biproduct.ι (fun _ : Fin (n + m) ↦ M) (Fin.natAdd n j) ≫ (biprodBiproductIso M n m).inv =
      biproduct.ι (fun _ : Fin m ↦ M) j ≫ biprod.inr := by
  rw [Iso.comp_inv_eq, Category.assoc, biproduct_ι_biprod_inr_biprodBiproductIso_hom]

end TauCeti
