/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import TauCeti.Algebra.Category.ModuleCat.SymmetricPower.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading

/-!
# Multiplication of symmetric powers in the category of modules

For `M : ModuleCat R` the product in the symmetric algebra of `M` sends the symmetric powers
`Symⁱ M` and `Symʲ M` into `Symⁱ⁺ʲ M`. This file packages it as a morphism
`ModuleCat.symmetricPower.mul M i j : Symⁱ M ⊗ Symʲ M ⟶ Symⁱ⁺ʲ M` of the monoidal category
`ModuleCat R`, natural in `M`, and proves that together with the unit `R ≅ Sym⁰ M` it is
unital, associative and commutative up to the identifications of degrees. These are the
homogeneous laws of a commutative monoid object in graded modules, in the form taken by
`CategoryTheory.GradedObject.monObjOfHomogeneous`; they are the sectionwise input for the graded
symmetric algebra of a sheaf of modules.

The bilinear multiplication is Mathlib's `DirectSum.gMulLHom` for the grading
`TauCeti.SymmetricAlgebra.gradedAlgebra` of the symmetric algebra by its homogeneous pieces, as
Mathlib's `exteriorPower.wedge` does for exterior powers.

## Main declarations

* `ModuleCat.symmetricPower.mul`: the multiplication `Symⁱ M ⊗ Symʲ M ⟶ Symⁱ⁺ʲ M`, computed by
  `ModuleCat.symmetricPower.coe_mul_tmul`;
* `ModuleCat.symmetricPower.mul_naturality`: naturality in `M`;
* `ModuleCat.symmetricPower.mul_surjective`: the multiplication is surjective, since `Symⁱ⁺ʲ M`
  is spanned by products of elements of `Symⁱ M` and `Symʲ M`; hence it is an epimorphism
  (`ModuleCat.symmetricPower.epi_mul`);
* `ModuleCat.symmetricPower.mul_assoc`, `mul_comm`, `one_mul` and `mul_one`: the graded
  associativity, commutativity and unit laws.
-/

public section

universe u

open CategoryTheory MonoidalCategory

namespace ModuleCat.symmetricPower

variable {R : Type u} [CommRing R]

open TauCeti.SymmetricAlgebra (homogeneousSubmodule)

/-- The multiplication of the symmetric algebra of `M`, restricted to the symmetric powers
`Symⁱ M` and `Symʲ M`, as a morphism `Symⁱ M ⊗ Symʲ M ⟶ Symⁱ⁺ʲ M` in `ModuleCat R`. -/
noncomputable def mul (M : ModuleCat.{u} R) (i j : ℕ) :
    M.symmetricPower i ⊗ M.symmetricPower j ⟶ M.symmetricPower (i + j) :=
  ofHom (TensorProduct.lift (DirectSum.gMulLHom R fun n ↦ homogeneousSubmodule R M n))

/-- The multiplication of symmetric powers is the product in the symmetric algebra. -/
@[simp]
lemma coe_mul_tmul (M : ModuleCat.{u} R) {i j : ℕ} (x : M.symmetricPower i)
    (y : M.symmetricPower j) :
    Subtype.val (mul M i j (x ⊗ₜ y)) = x.1 * y.1 :=
  (rfl)

/-- Transport along an equality of degrees does not change the underlying element of the
symmetric algebra. -/
@[simp]
lemma coe_eqToHom_apply (M : ModuleCat.{u} R) {i j : ℕ} (h : i = j) (x : M.symmetricPower i) :
    Subtype.val (eqToHom (congrArg M.symmetricPower h) x) = x.1 := by
  subst h
  rfl

/-- The multiplication of symmetric powers is natural in the module. -/
@[reassoc]
lemma mul_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) (i j : ℕ) :
    (map f i ⊗ₘ map f j) ≫ mul N i j = mul M i j ≫ map f (i + j) := by
  refine MonoidalCategory.tensor_ext fun x y ↦ Subtype.ext ?_
  simp only [ConcreteCategory.comp_apply]
  rw [coe_map_apply, coe_mul_tmul, MonoidalCategory.tensorHom_tmul, coe_mul_tmul, coe_map_apply,
    coe_map_apply, map_mul]

/-- The multiplication `Symⁱ M ⊗ Symʲ M ⟶ Symⁱ⁺ʲ M` is surjective: `Symⁱ⁺ʲ M` is the product
of the submodules `Symⁱ M` and `Symʲ M` of the symmetric algebra. -/
lemma mul_surjective (M : ModuleCat.{u} R) (i j : ℕ) : Function.Surjective (mul M i j) := by
  rintro ⟨x, hx⟩
  rw [homogeneousSubmodule, pow_add, ← Submodule.mulMap_range] at hx
  obtain ⟨t, rfl⟩ := hx
  -- `mul M i j` is `Submodule.mulMap` with its codomain restricted to `Symⁱ⁺ʲ M`
  have h : (homogeneousSubmodule R M (i + j)).subtype ∘ₗ (mul M i j).hom =
      Submodule.mulMap (homogeneousSubmodule R M i) (homogeneousSubmodule R M j) :=
    TensorProduct.ext' fun _ _ ↦ rfl
  exact ⟨t, Subtype.ext (LinearMap.congr_fun h t)⟩

/-- The multiplication `Symⁱ M ⊗ Symʲ M ⟶ Symⁱ⁺ʲ M` is an epimorphism. -/
instance epi_mul (M : ModuleCat.{u} R) (i j : ℕ) : Epi (mul M i j) :=
  (ModuleCat.epi_iff_surjective _).2 (mul_surjective M i j)

/-- The multiplication of symmetric powers is associative, up to the identification of the
degrees `i + (j + k)` and `i + j + k`. -/
@[reassoc]
lemma mul_assoc (M : ModuleCat.{u} R) (i j k : ℕ) :
    (mul M i j ▷ M.symmetricPower k) ≫ mul M (i + j) k =
      (α_ _ _ _).hom ≫ (M.symmetricPower i ◁ mul M j k) ≫ mul M i (j + k) ≫
        eqToHom (congrArg M.symmetricPower (add_assoc i j k).symm) := by
  refine MonoidalCategory.tensor_ext₃' fun x y z ↦ Subtype.ext ?_
  simp only [ConcreteCategory.comp_apply]
  rw [MonoidalCategory.whiskerRight_apply, coe_mul_tmul, coe_mul_tmul,
    MonoidalCategory.associator_hom_apply, MonoidalCategory.whiskerLeft_apply,
    coe_eqToHom_apply M (add_assoc i j k).symm, coe_mul_tmul, coe_mul_tmul, _root_.mul_assoc]

/-- The multiplication of symmetric powers is commutative, up to the identification of the
degrees `i + j` and `j + i`. -/
@[reassoc]
lemma mul_comm (M : ModuleCat.{u} R) (i j : ℕ) :
    (β_ (M.symmetricPower i) (M.symmetricPower j)).hom ≫ mul M j i =
      mul M i j ≫ eqToHom (congrArg M.symmetricPower (add_comm i j)) := by
  refine MonoidalCategory.tensor_ext fun x y ↦ Subtype.ext ?_
  simp only [ConcreteCategory.comp_apply]
  rw [MonoidalCategory.braiding_hom_apply, coe_mul_tmul, coe_eqToHom_apply M (add_comm i j),
    coe_mul_tmul, _root_.mul_comm]

/-- The unit `R ≅ Sym⁰ M` is a left identity for the multiplication of symmetric powers, up to
the identification of the degrees `0 + n` and `n`. -/
@[reassoc]
lemma one_mul (M : ModuleCat.{u} R) (n : ℕ) :
    ((iso₀ M).inv ▷ M.symmetricPower n) ≫ mul M 0 n =
      (λ_ (M.symmetricPower n)).hom ≫ eqToHom (congrArg M.symmetricPower (zero_add n).symm) := by
  refine MonoidalCategory.tensor_ext fun r x ↦ Subtype.ext ?_
  simp only [ConcreteCategory.comp_apply]
  rw [MonoidalCategory.whiskerRight_apply, coe_mul_tmul, coe_iso₀_inv_apply,
    MonoidalCategory.leftUnitor_hom_apply, coe_eqToHom_apply M (zero_add n).symm,
    Submodule.coe_smul, Algebra.smul_def]

/-- The unit `R ≅ Sym⁰ M` is a right identity for the multiplication of symmetric powers, up to
the identification of the degrees `n + 0` and `n`. -/
@[reassoc]
lemma mul_one (M : ModuleCat.{u} R) (n : ℕ) :
    (M.symmetricPower n ◁ (iso₀ M).inv) ≫ mul M n 0 =
      (ρ_ (M.symmetricPower n)).hom ≫ eqToHom (congrArg M.symmetricPower (add_zero n).symm) := by
  refine MonoidalCategory.tensor_ext fun x r ↦ Subtype.ext ?_
  simp only [ConcreteCategory.comp_apply]
  rw [MonoidalCategory.whiskerLeft_apply, coe_mul_tmul, coe_iso₀_inv_apply,
    MonoidalCategory.rightUnitor_hom_apply, coe_eqToHom_apply M (add_zero n).symm,
    Submodule.coe_smul, Algebra.smul_def, _root_.mul_comm]

end ModuleCat.symmetricPower
