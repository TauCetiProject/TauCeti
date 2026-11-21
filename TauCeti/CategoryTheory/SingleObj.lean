/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.CategoryTheory.SingleObj

/-!
# Pointwise algebraic structures on functors to a single-object category

For a category `C` and a commutative monoid `M`, functors `C ⥤ SingleObj M` form a commutative
monoid under pointwise multiplication of morphism values: `(F * G).map f = F.map f * G.map f`.
Commutativity of `M` is essential so that pointwise multiplication respects composition in
`SingleObj M`, where `a ≫ b = b * a`. When `M` is a commutative group, `C ⥤ SingleObj M` is a
commutative group under pointwise inversion.

In particular, when `C` is a groupoid and `A` is an abelian group, `C ⥤ SingleObj A` is the
abelian group of `A`-valued groupoid characters of `C`.

## Main declarations

* `CategoryTheory.SingleObj.functor_ext`: two functors into `SingleObj M` are equal once they
  agree on every morphism.
* `CategoryTheory.SingleObj.functorOne`, `CategoryTheory.SingleObj.functorCommMonoid`,
  `CategoryTheory.SingleObj.functorCommGroup`: pointwise `One`, `CommMonoid`, and `CommGroup`
  instances on `C ⥤ SingleObj M`.
* `CategoryTheory.SingleObj.evalMonoidHom`: evaluating a functor `C ⥤ SingleObj M` at a morphism
  `f : X ⟶ Y` is a monoid homomorphism `(C ⥤ SingleObj M) →* M`.
* `CategoryTheory.SingleObj.whiskerLeftMonoidHom`: precomposition with a functor `E : D ⥤ C` is a
  monoid homomorphism `(C ⥤ SingleObj M) →* (D ⥤ SingleObj M)`.
* `CategoryTheory.SingleObj.mapHomMulEquiv`: `CategoryTheory.SingleObj.mapHom` upgraded to a
  multiplicative equivalence `(N →* M) ≃* (SingleObj N ⥤ SingleObj M)` for commutative `M`.
-/

public section

universe v₁ v₂ u₁ u₂ w₁ w₂

namespace CategoryTheory.SingleObj

section Monoid

variable {C : Type u₁} [Category.{v₁} C] {M : Type w₁} [Monoid M]

/-- Two functors into `SingleObj M` are equal if they agree on every morphism. -/
theorem functor_ext {F G : C ⥤ SingleObj M}
    (h : ∀ {X Y : C} (f : X ⟶ Y), F.map f = G.map f) : F = G := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ f ↦ ?_
  simpa using h f

/-- The trivial functor `C ⥤ SingleObj M`, sending every morphism to `1`. -/
instance functorOne : One (C ⥤ SingleObj M) where
  one :=
    { obj := fun _ ↦ SingleObj.star M
      map := fun _ ↦ (1 : M)
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ (one_mul (1 : M)).symm }

@[simp]
theorem functor_one_obj (X : C) : (1 : C ⥤ SingleObj M).obj X = SingleObj.star M :=
  (rfl)

@[simp]
theorem functor_one_map {X Y : C} (f : X ⟶ Y) : (1 : C ⥤ SingleObj M).map f = (1 : M) :=
  (rfl)

end Monoid

section CommMonoid

variable {C : Type u₁} [Category.{v₁} C] {M : Type w₁} [CommMonoid M]

/-- Pointwise multiplication of functors into `SingleObj M` for a commutative monoid `M`. -/
instance functorMul : Mul (C ⥤ SingleObj M) where
  mul F G :=
    { obj := fun _ ↦ SingleObj.star M
      map := fun f ↦ (F.map f : M) * (G.map f : M)
      map_id := fun X ↦ by simp [SingleObj.id_as_one]
      map_comp := fun f g ↦ by simp [SingleObj.comp_as_mul, mul_mul_mul_comm] }

@[simp]
theorem functor_mul_obj (F G : C ⥤ SingleObj M) (X : C) :
    (F * G).obj X = SingleObj.star M :=
  (rfl)

@[simp]
theorem functor_mul_map (F G : C ⥤ SingleObj M) {X Y : C} (f : X ⟶ Y) :
    (F * G).map f = (F.map f : M) * (G.map f : M) :=
  (rfl)

/-- Pointwise natural-number powers of functors into `SingleObj M`. -/
instance functorNatPow : Pow (C ⥤ SingleObj M) ℕ where
  pow F n :=
    { obj := fun _ ↦ SingleObj.star M
      map := fun f ↦ (F.map f : M) ^ n
      map_id := fun X ↦ by simp [SingleObj.id_as_one]
      map_comp := fun f g ↦ by simp [SingleObj.comp_as_mul, mul_pow] }

@[simp]
theorem functor_pow_obj (F : C ⥤ SingleObj M) (n : ℕ) (X : C) :
    (F ^ n).obj X = SingleObj.star M :=
  (rfl)

@[simp]
theorem functor_pow_map (F : C ⥤ SingleObj M) (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (F ^ n).map f = (F.map f : M) ^ n :=
  (rfl)

instance functorCommMonoid : CommMonoid (C ⥤ SingleObj M) where
  mul_assoc _ _ _ := functor_ext fun _ ↦ mul_assoc _ _ _
  one_mul _ := functor_ext fun _ ↦ one_mul _
  mul_one _ := functor_ext fun _ ↦ mul_one _
  npow n F := F ^ n
  npow_zero _ := functor_ext fun _ ↦ pow_zero _
  npow_succ _ _ := functor_ext fun _ ↦ pow_succ _ _
  mul_comm _ _ := functor_ext fun _ ↦ mul_comm _ _

/-- Evaluating a functor `C ⥤ SingleObj M` on a fixed morphism `f` is a monoid homomorphism. -/
def evalMonoidHom {X Y : C} (f : X ⟶ Y) : (C ⥤ SingleObj M) →* M where
  toFun F := F.map f
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem evalMonoidHom_apply {X Y : C} (f : X ⟶ Y) (F : C ⥤ SingleObj M) :
    evalMonoidHom f F = F.map f :=
  (rfl)

/-- Precomposition with a functor `E : D ⥤ C` as a monoid homomorphism on `SingleObj M`-valued
functors. -/
def whiskerLeftMonoidHom {D : Type u₂} [Category.{v₂} D] (E : D ⥤ C) :
    (C ⥤ SingleObj M) →* (D ⥤ SingleObj M) where
  toFun F := E ⋙ F
  map_one' := functor_ext fun _ ↦ rfl
  map_mul' _ _ := functor_ext fun _ ↦ rfl

@[simp]
theorem whiskerLeftMonoidHom_apply {D : Type u₂} [Category.{v₂} D] (E : D ⥤ C)
    (F : C ⥤ SingleObj M) : whiskerLeftMonoidHom E F = E ⋙ F :=
  (rfl)

/-- For a monoid `N` and a commutative monoid `M`, `CategoryTheory.SingleObj.mapHom` is a
multiplicative equivalence `(N →* M) ≃* (SingleObj N ⥤ SingleObj M)`. -/
def mapHomMulEquiv (N : Type w₂) [Monoid N] (M : Type w₁) [CommMonoid M] :
    (N →* M) ≃* (SingleObj N ⥤ SingleObj M) :=
  { SingleObj.mapHom N M with
    map_mul' := fun _ _ ↦ functor_ext fun _ ↦ rfl }

@[simp]
theorem mapHomMulEquiv_apply (N : Type w₂) [Monoid N] (M : Type w₁) [CommMonoid M]
    (f : N →* M) : mapHomMulEquiv N M f = SingleObj.mapHom N M f :=
  (rfl)

@[simp]
theorem mapHomMulEquiv_symm_apply (N : Type w₂) [Monoid N] (M : Type w₁) [CommMonoid M]
    (F : SingleObj N ⥤ SingleObj M) :
    (mapHomMulEquiv N M).symm F = (SingleObj.mapHom N M).symm F :=
  (rfl)

end CommMonoid

section CommGroup

variable {C : Type u₁} [Category.{v₁} C] {G : Type w₁} [CommGroup G]

/-- Pointwise inversion of functors into `SingleObj G` for a commutative group `G`. -/
instance functorInv : Inv (C ⥤ SingleObj G) where
  inv F :=
    { obj := fun _ ↦ SingleObj.star G
      map := fun f ↦ (F.map f : G)⁻¹
      map_id := fun X ↦ by simp [SingleObj.id_as_one]
      map_comp := fun f g ↦ by simp [SingleObj.comp_as_mul, mul_comm] }

@[simp]
theorem functor_inv_obj (F : C ⥤ SingleObj G) (X : C) :
    F⁻¹.obj X = SingleObj.star G :=
  (rfl)

@[simp]
theorem functor_inv_map (F : C ⥤ SingleObj G) {X Y : C} (f : X ⟶ Y) :
    F⁻¹.map f = (F.map f : G)⁻¹ :=
  (rfl)

/-- Pointwise division of functors into `SingleObj G` for a commutative group `G`. -/
instance functorDiv : Div (C ⥤ SingleObj G) where
  div F H :=
    { obj := fun _ ↦ SingleObj.star G
      map := fun f ↦ (F.map f : G) / (H.map f : G)
      map_id := fun X ↦ by simp [SingleObj.id_as_one]
      map_comp := fun f g ↦ by simp [SingleObj.comp_as_mul, mul_div_mul_comm] }

@[simp]
theorem functor_div_obj (F H : C ⥤ SingleObj G) (X : C) :
    (F / H).obj X = SingleObj.star G :=
  (rfl)

@[simp]
theorem functor_div_map (F H : C ⥤ SingleObj G) {X Y : C} (f : X ⟶ Y) :
    (F / H).map f = (F.map f : G) / (H.map f : G) :=
  (rfl)

/-- Pointwise integer powers of functors into `SingleObj G` for a commutative group `G`. -/
instance functorIntPow : Pow (C ⥤ SingleObj G) ℤ where
  pow F n :=
    { obj := fun _ ↦ SingleObj.star G
      map := fun f ↦ (F.map f : G) ^ n
      map_id := fun X ↦ by simp [SingleObj.id_as_one]
      map_comp := fun f g ↦ by simp [SingleObj.comp_as_mul, mul_zpow] }

@[simp]
theorem functor_zpow_obj (F : C ⥤ SingleObj G) (n : ℤ) (X : C) :
    (F ^ n).obj X = SingleObj.star G :=
  (rfl)

@[simp]
theorem functor_zpow_map (F : C ⥤ SingleObj G) (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    (F ^ n).map f = (F.map f : G) ^ n :=
  (rfl)

instance functorCommGroup : CommGroup (C ⥤ SingleObj G) where
  zpow n F := F ^ n
  zpow_zero' _ := functor_ext fun _ ↦ zpow_zero _
  zpow_succ' n F := functor_ext fun f ↦ DivInvMonoid.zpow_succ' n (F.map f)
  zpow_neg' n F := functor_ext fun f ↦ DivInvMonoid.zpow_neg' n (F.map f)
  div_eq_mul_inv _ _ := functor_ext fun _ ↦ div_eq_mul_inv _ _
  inv_mul_cancel _ := functor_ext fun _ ↦ inv_mul_cancel _

end CommGroup

end CategoryTheory.SingleObj
