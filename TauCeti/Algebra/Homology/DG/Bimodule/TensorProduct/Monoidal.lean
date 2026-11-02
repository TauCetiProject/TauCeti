/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Associator
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Unit

/-!
# The monoidal category of DG bimodules

DG bimodules over a fixed DG algebra form an `R`-linear monoidal category under ordinary
balanced tensor product. The unit is the universe-lifted regular bimodule. The associator
and unitors are the existing DG bimodule isomorphisms, so their grading and differential
compatibility are retained. The triangle identity is the balancing relation.

This structure allows tensor-algebra multiplication to be expressed as a monoid object,
with the usual categorical associativity and unit laws. It is an underived structure:
using it to model a derived tensor algebra additionally requires suitable resolutions.
The scalar universe is independent. As for Mathlib's monoidal category of modules,
bimodules and the algebra are taken in the same universe.

## References

* B. Keller, *Deriving DG categories*, Section 6.1.
* B. Keller, *Deformed Calabi--Yau completions*, Section 4.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti.DGBimoduleCat

universe v uR uA uB uC

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A}
  {hA : IsDGAlgebra 𝒜 dA}

open BalancedTensorProduct

attribute [local instance 100] leftModule rightModule leftIsScalarTower rightIsScalarTower
  outerSMulCommClass

section Triangle

variable {B : Type uB} {C : Type uC} [Ring B] [Ring C] [Algebra R B] [Algebra R C]
  {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [GradedAlgebra ℬ] [GradedAlgebra 𝒞] {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {hB : IsDGAlgebra ℬ dB} {hC : IsDGAlgebra 𝒞 dC}
  (M : DGBimoduleCat.{uR, uA, uB, max v uB} hA hB)
  (N : DGBimoduleCat.{uR, uB, uC, max v uB} hB hC)

/-- Reassociation followed by evaluation of the middle regular bimodule agrees with
evaluation before tensoring. This is the triangle identity for balanced tensor product. -/
theorem tensorAssoc_triangle :
    (tensorAssoc M (tensorUnit.{v} hB) N).hom ≫
        tensorMap (𝟙 M) (tensorLeftUnitorHom.{v} hB hC N) =
      tensorMap (tensorRightUnitorHom.{v} hA hB M) (𝟙 N) := by
  apply tensorObj_hom_ext
  intro z n
  induction z using BalancedTensorProduct.induction_on with
  | ht m x =>
      rw [comp_apply, tensorAssoc_hom_tmul, tensorMap_tmul, id_apply,
        tensorLeftUnitorHom_tmul, tensorMap_tmul, tensorRightUnitorHom_tmul, id_apply]
      exact (balance R B x.down m n).symm
  | ha z w hz hw => simp only [add_tmul, map_add, hz, hw]

end Triangle

variable (M N : DGBimoduleCat.{uR, uA, uA, uA} hA hA)

/-- The balanced tensor product, regular bimodule and canonical reassociations.
This is not a separate instance: the full monoidal instance supplies the structure data.
The data are exposed so dependent tensor carriers can reduce in importing modules. -/
@[expose, instance_reducible]
def monoidalCategoryStruct :
    MonoidalCategoryStruct (DGBimoduleCat.{uR, uA, uA, uA} hA hA) where
  tensorObj := tensorObj
  tensorUnit := tensorUnit.{uA} hA
  tensorHom := tensorMap
  whiskerLeft M _ _ g := tensorMap (𝟙 M) g
  whiskerRight f N := tensorMap f (𝟙 N)
  associator := tensorAssoc
  leftUnitor := tensorLeftUnitor.{uA} hA hA
  rightUnitor := tensorRightUnitor.{uA} hA hA

/-- Ordinary DG bimodule tensor composition is monoidal. -/
instance instMonoidalCategory :
    MonoidalCategory (DGBimoduleCat.{uR, uA, uA, uA} hA hA) :=
  @MonoidalCategory.ofTensorHom _ _ (monoidalCategoryStruct (hA := hA))
    (id_tensorHom_id := tensorMap_id)
    (id_tensorHom := fun _ _ _ _ ↦ rfl)
    (tensorHom_id := fun _ _ ↦ rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ ↦ (tensorMap_comp f₁ f₂ g₁ g₂).symm)
    (associator_naturality := fun f g h ↦ tensorAssoc_naturality f g h)
    (leftUnitor_naturality := fun f ↦ by
      simpa only [MonoidalCategoryStruct.tensorHom, MonoidalCategoryStruct.tensorUnit,
        MonoidalCategoryStruct.leftUnitor, monoidalCategoryStruct, tensorLeftUnitor_hom] using
        tensorLeftUnitorHom_naturality hA hA _ f)
    (rightUnitor_naturality := fun f ↦ by
      simpa only [MonoidalCategoryStruct.tensorHom, MonoidalCategoryStruct.tensorUnit,
        MonoidalCategoryStruct.rightUnitor, monoidalCategoryStruct, tensorRightUnitor_hom] using
        tensorRightUnitorHom_naturality hA hA _ f)
    (pentagon := fun W X Y Z ↦ tensorAssoc_pentagon W X Y Z)
    (triangle := fun M N ↦ by
      simpa only [MonoidalCategoryStruct.tensorHom, MonoidalCategoryStruct.tensorUnit,
        MonoidalCategoryStruct.associator, MonoidalCategoryStruct.leftUnitor,
        MonoidalCategoryStruct.rightUnitor, monoidalCategoryStruct, tensorLeftUnitor_hom,
        tensorRightUnitor_hom] using tensorAssoc_triangle M N)

open MonoidalCategory

/-- The categorical tensor product uses the balanced DG bimodule tensor product. -/
theorem tensorObj_eq : M ⊗ N = tensorObj M N := (rfl)

/-- The categorical unit is the lifted regular DG bimodule. -/
theorem tensorUnit_eq :
    𝟙_ (DGBimoduleCat.{uR, uA, uA, uA} hA hA) = tensorUnit.{uA} hA := (rfl)

variable {M N}
  {M' N' : DGBimoduleCat.{uR, uA, uA, uA} hA hA}

/-- The categorical tensor of morphisms is the balanced tensor map. -/
theorem tensorHom_eq (f : M ⟶ M') (g : N ⟶ N') : f ⊗ₘ g = tensorMap f g := (rfl)

/-- Left whiskering tensors with the identity of the left factor. -/
theorem whiskerLeft_eq (M : DGBimoduleCat.{uR, uA, uA, uA} hA hA)
    (g : N ⟶ N') : M ◁ g = tensorMap (𝟙 M) g := (rfl)

/-- Right whiskering tensors with the identity of the right factor. -/
theorem whiskerRight_eq (f : M ⟶ M')
    (N : DGBimoduleCat.{uR, uA, uA, uA} hA hA) :
    f ▷ N = tensorMap f (𝟙 N) := (rfl)

/-- The categorical associator is the canonical balanced reassociation. -/
theorem associator_eq (M N P : DGBimoduleCat.{uR, uA, uA, uA} hA hA) :
    α_ M N P = tensorAssoc M N P := (rfl)

/-- The categorical left unitor evaluates the regular left factor. -/
theorem leftUnitor_eq (M : DGBimoduleCat.{uR, uA, uA, uA} hA hA) :
    λ_ M = tensorLeftUnitor.{uA} hA hA M := (rfl)

/-- The categorical right unitor evaluates the regular right factor. -/
theorem rightUnitor_eq (M : DGBimoduleCat.{uR, uA, uA, uA} hA hA) :
    ρ_ M = tensorRightUnitor.{uA} hA hA M := (rfl)

/-- The categorical tensor of morphisms acts factorwise on pure tensors. -/
@[simp]
theorem tensorHom_tmul (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    (f ⊗ₘ g) (tmul R A m n) = tmul R A (f m) (g n) := by
  rw [tensorHom_eq, tensorMap_tmul]

/-- Left whiskering applies the morphism to the right tensor factor. -/
@[simp]
theorem whiskerLeft_tmul (M : DGBimoduleCat.{uR, uA, uA, uA} hA hA)
    (g : N ⟶ N') (m : M) (n : N) :
    (M ◁ g) (tmul R A m n) = tmul R A m (g n) := by
  rw [whiskerLeft_eq, tensorMap_tmul, id_apply]

/-- Right whiskering applies the morphism to the left tensor factor. -/
@[simp]
theorem whiskerRight_tmul (f : M ⟶ M')
    (N : DGBimoduleCat.{uR, uA, uA, uA} hA hA) (m : M) (n : N) :
    (f ▷ N) (tmul R A m n) = tmul R A (f m) n := by
  rw [whiskerRight_eq, tensorMap_tmul, id_apply]

/-- The categorical associator changes only parentheses on pure tensors. -/
@[simp]
theorem associator_hom_tmul {P : DGBimoduleCat.{uR, uA, uA, uA} hA hA}
    (m : M) (n : N) (p : P) :
    (α_ M N P).hom (tmul R A (tmul R A m n) p) = tmul R A m (tmul R A n p) := by
  rw [associator_eq, tensorAssoc_hom_tmul]

/-- The inverse categorical associator restores parentheses on pure tensors. -/
@[simp]
theorem associator_inv_tmul {P : DGBimoduleCat.{uR, uA, uA, uA} hA hA}
    (m : M) (n : N) (p : P) :
    (α_ M N P).inv (tmul R A m (tmul R A n p)) = tmul R A (tmul R A m n) p := by
  rw [associator_eq, tensorAssoc_inv_tmul]

/-- The categorical left unitor evaluates the regular left tensor factor. -/
@[simp]
theorem leftUnitor_hom_tmul (x : 𝟙_ (DGBimoduleCat.{uR, uA, uA, uA} hA hA)) (m : M) :
    (λ_ M).hom (tmul R A x m) = x.down • m := by
  rw [leftUnitor_eq, tensorLeftUnitor_hom, tensorLeftUnitorHom_tmul]

/-- The inverse categorical left unitor inserts the algebra unit on the left. -/
@[simp]
theorem leftUnitor_inv_apply (m : M) :
    (λ_ M).inv m = tmul R A (tensorUnitEquiv.{uA} hA 1) m := by
  rw [leftUnitor_eq, tensorLeftUnitor_inv, tensorLeftUnitorInv_apply]

/-- The categorical right unitor evaluates the regular right tensor factor. -/
@[simp]
theorem rightUnitor_hom_tmul (m : M) (x : 𝟙_ (DGBimoduleCat.{uR, uA, uA, uA} hA hA)) :
    (ρ_ M).hom (tmul R A m x) = op x.down • m := by
  rw [rightUnitor_eq, tensorRightUnitor_hom, tensorRightUnitorHom_tmul]

/-- The inverse categorical right unitor inserts the algebra unit on the right. -/
@[simp]
theorem rightUnitor_inv_apply (m : M) :
    (ρ_ M).inv m = tmul R A m (tensorUnitEquiv.{uA} hA 1) := by
  rw [rightUnitor_eq, tensorRightUnitor_inv, tensorRightUnitorInv_apply]

/-- Tensoring DG bimodule morphisms is additive in each factor. -/
instance instMonoidalPreadditive :
    MonoidalPreadditive (DGBimoduleCat.{uR, uA, uA, uA} hA hA) where
  whiskerLeft_zero := by intros; exact tensorMap_zero_right _
  zero_whiskerRight := by intros; exact tensorMap_zero_left _
  whiskerLeft_add := by intros; exact tensorMap_add_right _ _ _
  add_whiskerRight := by intros; exact tensorMap_add_left _ _ _

/-- Tensoring DG bimodule morphisms is linear over the ground ring in each factor. -/
instance instMonoidalLinear :
    MonoidalLinear R (DGBimoduleCat.{uR, uA, uA, uA} hA hA) where
  whiskerLeft_smul := by intros; exact tensorMap_smul_right _ _ _
  smul_whiskerRight := by intros; exact tensorMap_smul_left _ _ _

end TauCeti.DGBimoduleCat
