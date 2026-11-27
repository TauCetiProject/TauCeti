/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Category.FiniteIsocrystal.Basic

/-!
# The tensor product of finite isocrystals

The tensor product of finite isocrystals `D` and `D'` over `(L, σ)` is the `L`-vector space
`D ⊗[L] D'` with the Frobenius `x ⊗ y ↦ Φ x ⊗ Φ' y`. This Frobenius is again `σ`-semilinear and
bijective, so it is a finite isocrystal. The unit is `L` itself with Frobenius `σ`. The tensor
product of two morphisms is the tensor product of their underlying linear maps, and the
associator, unitors and braiding of `L`-vector spaces intertwine the Frobenii. So the category of
finite isocrystals is a symmetric monoidal category, and the forgetful functor to `ModuleCat L` is
a symmetric monoidal functor. The tensor product is `E`-bilinear on morphisms.

This is the tensor structure in which slopes are computed: over the completion of the maximal
unramified extension of a local field, the tensor product of isocrystals of slopes `a` and `b` is
isoclinic of slope `a + b`, and the functor from isocrystals to vector bundles on the
Fargues–Fontaine curve is a tensor functor. Those slope statements rest on the Dieudonné–Manin
classification and are not proved here. The dual isocrystal, which makes this category rigid, is
in `TauCeti.Algebra.Category.FiniteIsocrystal.Dual`.

## Main definitions

* `TauCeti.FiniteIsocrystal.instMonoidalCategory`: the monoidal structure, with tensor product
  `D ⊗[L] D'` with Frobenius `Φ ⊗ Φ'` and unit `L` with Frobenius `σ`.
* The `SymmetricCategory` and `MonoidalLinear E` instances on finite isocrystals; the braiding is
  the symmetry `x ⊗ y ↦ y ⊗ x`.

## Main results

* `TauCeti.FiniteIsocrystal.map_frobenius_bijective`: `Φ ⊗ Φ'` is bijective.
* `TauCeti.FiniteIsocrystal.hom_tensorHom`, `TauCeti.FiniteIsocrystal.hom_hom_associator` and
  their companions: the underlying linear maps of the monoidal structure maps are those of
  `ModuleCat L`.
* `TauCeti.FiniteIsocrystal.finrank_tensorObj`: the rank of `D ⊗ D'` is the product of the ranks.

## Implementation notes

The construction mirrors Mathlib's
`Mathlib/LinearAlgebra/QuadraticForm/QuadraticModuleCat/Monoidal.lean`, which is itself modelled
on `Mathlib/Algebra/Category/AlgCat/Monoidal.lean`: the monoidal structure is `Monoidal.induced`
along the faithful forgetful functor to `ModuleCat L`, with structure maps built from those of
`ModuleCat L`, and the braiding is transported the same way with `BraidedCategory.ofFaithful`.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), §8.2.3, Proposition 8.2.6.
* K. S. Kedlaya, *A p-adic local monodromy theorem*, Ann. of Math. 160 (2004), Definition 3.1.5.
-/

public section

open CategoryTheory TensorProduct
open scoped MonoidalCategory

universe u

namespace TauCeti

namespace FiniteIsocrystal

variable {E : Type*} {L : Type u} [CommRing E] [Field L] [Algebra E L] {σ : L ≃ₐ[E] L}

/-! ### The tensor product and the unit -/

section Tensor

variable (D D' : FiniteIsocrystal.{u} σ)

/-- The Frobenius `Φ ⊗ Φ'` of a tensor product of finite isocrystals, the `σ`-semilinear map
`x ⊗ y ↦ Φ x ⊗ Φ' y`, is bijective. -/
theorem map_frobenius_bijective :
    Function.Bijective (TensorProduct.map D.frobenius D'.frobenius) := by
  rw [← D.toLinearMap_frobeniusEquiv, ← D'.toLinearMap_frobeniusEquiv,
    ← TensorProduct.toLinearMap_congr]
  exact (TensorProduct.congr _ _).bijective

end Tensor

namespace instMonoidalCategory

/-- Auxiliary definition used to build `TauCeti.FiniteIsocrystal.instMonoidalCategory`: the tensor
product of two finite isocrystals, `D ⊗[L] D'` with Frobenius `Φ ⊗ Φ'`. -/
abbrev tensorObj (D D' : FiniteIsocrystal.{u} σ) : FiniteIsocrystal.{u} σ :=
  of σ (D ⊗[L] D') (TensorProduct.map D.frobenius D'.frobenius) (map_frobenius_bijective D D')

variable (σ) in
/-- Auxiliary definition used to build `TauCeti.FiniteIsocrystal.instMonoidalCategory`: the unit
finite isocrystal, the field `L` with Frobenius `σ`. -/
abbrev unit : FiniteIsocrystal.{u} σ :=
  of σ L (σ : L →+* L).toSemilinearMap σ.bijective

/-- Auxiliary definition used to build `TauCeti.FiniteIsocrystal.instMonoidalCategory`: the tensor
product of two morphisms of finite isocrystals. -/
abbrev tensorHom {D₁ D₂ D₃ D₄ : FiniteIsocrystal.{u} σ} (f : D₁ ⟶ D₂) (g : D₃ ⟶ D₄) :
    tensorObj D₁ D₃ ⟶ tensorObj D₂ D₄ :=
  ofHom (TensorProduct.map f.hom g.hom) fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simp_all

end instMonoidalCategory

open instMonoidalCategory

variable {D₁ D₂ D₃ D₄ : FiniteIsocrystal.{u} σ}

instance : MonoidalCategoryStruct (FiniteIsocrystal.{u} σ) where
  tensorObj D D' := tensorObj D D'
  whiskerLeft D _ _ f := tensorHom (𝟙 D) f
  whiskerRight f D := tensorHom f (𝟙 D)
  tensorHom := tensorHom
  tensorUnit := unit σ
  associator D₁ D₂ D₃ := isoMk (TensorProduct.assoc L D₁ D₂ D₃) fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul x z =>
      induction x using TensorProduct.inductionOn with
      | tmul x y => simp
      | add x y hx hy => simp_all [add_tmul]
    | add x y hx hy => simp_all
  leftUnitor D := isoMk (TensorProduct.lid L D) fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul c x => simp
    | add x y hx hy => simp_all
  rightUnitor D := isoMk (TensorProduct.rid L D) fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul x c => simp
    | add x y hx hy => simp_all

/-! ### Underlying linear maps of the monoidal structure maps -/

section Hom

@[simp]
theorem tensorObj_frobenius (D D' : FiniteIsocrystal.{u} σ) :
    (D ⊗ D').frobenius = TensorProduct.map D.frobenius D'.frobenius := (rfl)

@[simp]
theorem tensorUnit_frobenius_apply (c : L) : (𝟙_ (FiniteIsocrystal.{u} σ)).frobenius c = σ c :=
  (rfl)

@[simp]
theorem hom_tensorHom (f : D₁ ⟶ D₂) (g : D₃ ⟶ D₄) :
    (f ⊗ₘ g).hom = TensorProduct.map f.hom g.hom := (rfl)

@[simp]
theorem hom_whiskerLeft (D : FiniteIsocrystal.{u} σ) (f : D₁ ⟶ D₂) :
    (D ◁ f).hom = f.hom.lTensor D := (rfl)

@[simp]
theorem hom_whiskerRight (f : D₁ ⟶ D₂) (D : FiniteIsocrystal.{u} σ) :
    (f ▷ D).hom = f.hom.rTensor D := (rfl)

@[simp]
theorem hom_hom_associator (D₁ D₂ D₃ : FiniteIsocrystal.{u} σ) :
    (α_ D₁ D₂ D₃).hom.hom = (TensorProduct.assoc L D₁ D₂ D₃).toLinearMap :=
  isoMk_hom_hom _ _

@[simp]
theorem hom_inv_associator (D₁ D₂ D₃ : FiniteIsocrystal.{u} σ) :
    (α_ D₁ D₂ D₃).inv.hom = (TensorProduct.assoc L D₁ D₂ D₃).symm.toLinearMap :=
  isoMk_inv_hom _ _

@[simp]
theorem hom_hom_leftUnitor (D : FiniteIsocrystal.{u} σ) :
    (λ_ D).hom.hom = (TensorProduct.lid L D).toLinearMap :=
  isoMk_hom_hom _ _

@[simp]
theorem hom_inv_leftUnitor (D : FiniteIsocrystal.{u} σ) :
    (λ_ D).inv.hom = (TensorProduct.lid L D).symm.toLinearMap :=
  isoMk_inv_hom _ _

@[simp]
theorem hom_hom_rightUnitor (D : FiniteIsocrystal.{u} σ) :
    (ρ_ D).hom.hom = (TensorProduct.rid L D).toLinearMap :=
  isoMk_hom_hom _ _

@[simp]
theorem hom_inv_rightUnitor (D : FiniteIsocrystal.{u} σ) :
    (ρ_ D).inv.hom = (TensorProduct.rid L D).symm.toLinearMap :=
  isoMk_inv_hom _ _

end Hom

/-! ### The monoidal structure -/

instance instMonoidalCategory : MonoidalCategory (FiniteIsocrystal.{u} σ) :=
  Monoidal.induced (forget₂ (FiniteIsocrystal σ) (ModuleCat L))
    { μIso _ _ := Iso.refl _
      εIso := Iso.refl _
      whiskerLeft_eq _ _ _ _ := by ext1; exact TensorProduct.ext' fun _ _ => rfl
      whiskerRight_eq _ _ := by ext1; exact TensorProduct.ext' fun _ _ => rfl
      tensorHom_eq _ _ := by ext1; exact TensorProduct.ext' fun _ _ => rfl
      associator_eq _ _ _ := by
        ext1
        rw [forget₂_map, hom_hom_associator]
        exact TensorProduct.ext (TensorProduct.ext rfl)
      leftUnitor_eq _ := by
        ext1
        rw [forget₂_map, hom_hom_leftUnitor]
        exact TensorProduct.ext rfl
      rightUnitor_eq _ := by
        ext1
        rw [forget₂_map, hom_hom_rightUnitor]
        exact TensorProduct.ext rfl }

/-- The forgetful functor from finite isocrystals to `L`-vector spaces is monoidal. -/
instance : (forget₂ (FiniteIsocrystal.{u} σ) (ModuleCat.{u} L)).Monoidal :=
  Monoidal.fromInducedMonoidal _ _

/-- The braiding of finite isocrystals is the symmetry `x ⊗ y ↦ y ⊗ x`. -/
instance : BraidedCategory (FiniteIsocrystal.{u} σ) :=
  .ofFaithful (forget₂ (FiniteIsocrystal σ) (ModuleCat L))
    (fun D D' => isoMk (D := D ⊗ D') (D' := D' ⊗ D) (TensorProduct.comm L D D') fun x =>
      (TensorProduct.map_comm _ _ x).symm) fun D D' => by
    ext1
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, forget₂_map, isoMk_hom_hom]
    exact TensorProduct.ext' fun _ _ => rfl

@[simp]
theorem hom_hom_braiding (D D' : FiniteIsocrystal.{u} σ) :
    (β_ D D').hom.hom = (TensorProduct.comm L D D').toLinearMap :=
  isoMk_hom_hom (D := D ⊗ D') (D' := D' ⊗ D) _ _

@[simp]
theorem hom_inv_braiding (D D' : FiniteIsocrystal.{u} σ) :
    (β_ D D').inv.hom = (TensorProduct.comm L D D').symm.toLinearMap :=
  isoMk_inv_hom (D := D ⊗ D') (D' := D' ⊗ D) _ _

/-- The forgetful functor from finite isocrystals to `L`-vector spaces is braided. -/
instance : (forget₂ (FiniteIsocrystal.{u} σ) (ModuleCat.{u} L)).Braided where

instance : SymmetricCategory (FiniteIsocrystal.{u} σ) :=
  .ofFaithful (forget₂ (FiniteIsocrystal σ) (ModuleCat L))

instance : MonoidalPreadditive (FiniteIsocrystal.{u} σ) where
  whiskerLeft_zero := by intros; ext1; simp
  zero_whiskerRight := by intros; ext1; simp
  whiskerLeft_add := by intros; ext1; simp
  add_whiskerRight := by intros; ext1; simp

instance : MonoidalLinear E (FiniteIsocrystal.{u} σ) where
  whiskerLeft_smul := by intros; ext1; simp [LinearMap.lTensor_smul]
  smul_whiskerRight := by intros; ext1; simp [LinearMap.rTensor_smul]

/-! ### Rank -/

/-- The rank of a tensor product of finite isocrystals is the product of the ranks. -/
@[simp]
theorem finrank_tensorObj (D D' : FiniteIsocrystal.{u} σ) :
    Module.finrank L (D ⊗ D' : FiniteIsocrystal.{u} σ) = Module.finrank L D * Module.finrank L D' :=
  Module.finrank_tensorProduct

/-- The unit finite isocrystal has rank one. -/
@[simp]
theorem finrank_tensorUnit : Module.finrank L (𝟙_ (FiniteIsocrystal.{u} σ)) = 1 :=
  Module.finrank_self L

end FiniteIsocrystal

end TauCeti
