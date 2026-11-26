/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Grp

/-!
# Monoid and group axioms after a monoidal functor

Let `F : C ⥤ D` be a monoidal functor and let `X : C` carry candidate structure morphisms
`one : 𝟙_ C ⟶ X`, `mul : X ⊗ X ⟶ X` (and `inv : X ⟶ X`), not assumed to satisfy any axioms. This
file compares these data with monoid (group) object structures on `F.obj X`, in both directions.

* If the images of the data under `F` are the structure morphisms of a monoid (group) object
  `F.obj X`, then each axiom holds for the data on `X` after applying `F`
  (`CategoryTheory.Functor.map_one_mul` and its companions).
* Conversely, if each axiom holds for the data on `X` after applying `F`, the images of the data
  make `F.obj X` a monoid (group) object (`CategoryTheory.Functor.monObjObjOfMap`,
  `CategoryTheory.Functor.grpObjObjOfMap`). When the axioms already hold on `X` this is Mathlib's
  `CategoryTheory.Functor.monObjObj` (`CategoryTheory.Functor.grpObjObj`), whose construction and
  proofs these follow.
* For a morphism `f` of monoid objects, `F.map f` is a homomorphism exactly when the equations
  expressing that `f` is one hold after applying `F`
  (`CategoryTheory.Functor.isMonHom_map_iff_map_eq`).
* A monoidal natural transformation `τ : F ⟶ G` is a homomorphism `F.obj X ⟶ G.obj X` between
  monoid objects whose structure morphisms are the images of the same data on `X`
  (`CategoryTheory.NatTrans.isMonHom_app`).

The first statement lets a faithful functor reflect the axioms
(`CategoryTheory.Functor.monObjOfFaithful`). Together, the statements move monoid and group
objects along functors which are not faithful, such as the base change functors from a member of a
cofiltered system of schemes to its limit: a group law over the limit is spread out to a member by
lifting its structure morphisms and then the equalities expressing its axioms, and a homomorphism
by spreading out the equalities expressing that it is one.
-/

public section

namespace CategoryTheory.Functor

open MonoidalCategory MonObj OplaxMonoidal LaxMonoidal CartesianMonoidalCategory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section Monoidal

variable [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)

section OplaxMonoidal

variable [F.OplaxMonoidal] {X : C} [MonObj (F.obj X)] {one : 𝟙_ C ⟶ X} {mul : X ⊗ X ⟶ X}

/-- If `one` and `mul` lift the unit and the multiplication of `F.obj X`, then the left unit
axiom holds for them after applying `F`. -/
theorem map_one_mul (h_one : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) :
    F.map (one ▷ X ≫ mul) = F.map (λ_ X).hom := by
  simp [h_one, h_mul, ← δ_natural_left_assoc]

/-- If `one` and `mul` lift the unit and the multiplication of `F.obj X`, then the right unit
axiom holds for them after applying `F`. -/
theorem map_mul_one (h_one : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) :
    F.map (X ◁ one ≫ mul) = F.map (ρ_ X).hom := by
  simp [h_one, h_mul, ← δ_natural_right_assoc]

/-- If `mul` lifts the multiplication of `F.obj X`, then the associativity axiom holds for it
after applying `F`. -/
theorem map_mul_assoc (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) :
    F.map (mul ▷ X ≫ mul) = F.map ((α_ X X X).hom ≫ X ◁ mul ≫ mul) := by
  simp [h_mul, ← δ_natural_left_assoc, ← δ_natural_right_assoc]

end OplaxMonoidal

section IsMonHom

open scoped Obj

variable [F.Monoidal] {X Y : C} [MonObj X] [MonObj Y]

/-- For a monoidal functor `F` and a morphism `f` of monoid objects, `F.map f` is a homomorphism
between the image monoid objects exactly when the two homomorphism equations for `f` hold after
applying `F`. -/
theorem isMonHom_map_iff_map_eq (f : X ⟶ Y) :
    IsMonHom (F.map f) ↔
      F.map (η[X] ≫ f) = F.map η[Y] ∧ F.map (μ[X] ≫ f) = F.map ((f ⊗ₘ f) ≫ μ[Y]) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h_one, h_mul⟩ ↦ ⟨?_, ?_⟩⟩
  · simpa [← cancel_epi (ε F)] using h.one_hom
  · simpa [← cancel_epi (LaxMonoidal.μ F X X)] using h.mul_hom
  · rw [obj.η_def, obj.η_def, Category.assoc, ← F.map_comp, h_one]
  · rw [obj.μ_def, obj.μ_def, Category.assoc, ← F.map_comp, h_mul, F.map_comp,
      LaxMonoidal.μ_natural_assoc]

end IsMonHom

variable [F.LaxMonoidal] {X : C} (one : 𝟙_ C ⟶ X) (mul : X ⊗ X ⟶ X)

/-- The monoid object structure on `F.obj X` given by the images `ε ≫ F.map one` and
`μ ≫ F.map mul` of candidate structure morphisms on `X` which satisfy the monoid axioms after
applying `F`. -/
@[simps]
abbrev monObjObjOfMap (h_one_mul : F.map (one ▷ X ≫ mul) = F.map (λ_ X).hom)
    (h_mul_one : F.map (X ◁ one ≫ mul) = F.map (ρ_ X).hom)
    (h_mul_assoc : F.map (mul ▷ X ≫ mul) = F.map ((α_ X X X).hom ≫ X ◁ mul ≫ mul)) :
    MonObj (F.obj X) where
  one := ε F ≫ F.map one
  mul := LaxMonoidal.μ F X X ≫ F.map mul
  one_mul := by
    simp [← F.map_comp, h_one_mul]
  mul_one := by
    simp [← F.map_comp, h_mul_one]
  mul_assoc := by
    simp_rw [comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, μ_natural_right_assoc]
    rw [← F.map_comp, h_mul_assoc]
    simp

end Monoidal

section Cartesian

variable [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] (F : C ⥤ D)

section OplaxMonoidal

variable [F.OplaxMonoidal] {X : C} [GrpObj (F.obj X)] {one : 𝟙_ C ⟶ X} {mul : X ⊗ X ⟶ X}
  {inv : X ⟶ X}

/-- If `one`, `mul` and `inv` lift the structure morphisms of the group object `F.obj X`, then
the left inverse axiom holds for them after applying `F`. -/
theorem map_left_inv (h_one : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) (h_inv : F.map inv = ι[F.obj X]) :
    F.map (lift inv (𝟙 X) ≫ mul) = F.map (toUnit X ≫ one) := by
  simp [h_one, h_mul, h_inv, OplaxMonoidal.η_of_cartesianMonoidalCategory]

/-- If `one`, `mul` and `inv` lift the structure morphisms of the group object `F.obj X`, then
the right inverse axiom holds for them after applying `F`. -/
theorem map_right_inv (h_one : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (h_mul : F.map mul = δ F X X ≫ μ[F.obj X]) (h_inv : F.map inv = ι[F.obj X]) :
    F.map (lift (𝟙 X) inv ≫ mul) = F.map (toUnit X ≫ one) := by
  simp [h_one, h_mul, h_inv, OplaxMonoidal.η_of_cartesianMonoidalCategory]

end OplaxMonoidal

variable [F.Monoidal] {X : C} (one : 𝟙_ C ⟶ X) (mul : X ⊗ X ⟶ X) (inv : X ⟶ X)

/-- The group object structure on `F.obj X` given by the images of candidate structure morphisms
on `X` which satisfy the group axioms after applying `F`. -/
@[simps]
abbrev grpObjObjOfMap (h_one_mul : F.map (one ▷ X ≫ mul) = F.map (λ_ X).hom)
    (h_mul_one : F.map (X ◁ one ≫ mul) = F.map (ρ_ X).hom)
    (h_mul_assoc : F.map (mul ▷ X ≫ mul) = F.map ((α_ X X X).hom ≫ X ◁ mul ≫ mul))
    (h_left_inv : F.map (lift inv (𝟙 X) ≫ mul) = F.map (toUnit X ≫ one))
    (h_right_inv : F.map (lift (𝟙 X) inv ≫ mul) = F.map (toUnit X ≫ one)) :
    GrpObj (F.obj X) where
  __ := F.monObjObjOfMap one mul h_one_mul h_mul_one h_mul_assoc
  inv := F.map inv
  left_inv := by
    simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
      Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp, h_left_inv]
  right_inv := by
    simp [← Functor.map_id, Functor.Monoidal.lift_μ_assoc,
      Functor.Monoidal.toUnit_ε_assoc, ← Functor.map_comp, h_right_inv]

end Cartesian

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

open MonoidalCategory MonObj Functor.LaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (τ : F ⟶ G) [τ.IsMonoidal] {X : C}
  [hF : MonObj (F.obj X)] [hG : MonObj (G.obj X)] {one : 𝟙_ C ⟶ X} {mul : X ⊗ X ⟶ X}

/-- A monoidal natural transformation `τ : F ⟶ G` is a homomorphism of monoid objects
`F.obj X ⟶ G.obj X` when the units and the multiplications of both are the images of the same
morphisms `one` and `mul` on `X`. -/
theorem isMonHom_app (hF_one : η[F.obj X] = ε F ≫ F.map one)
    (hF_mul : μ[F.obj X] = «μ» F X X ≫ F.map mul) (hG_one : η[G.obj X] = ε G ≫ G.map one)
    (hG_mul : μ[G.obj X] = «μ» G X X ≫ G.map mul) : IsMonHom (τ.app X) where
  one_hom := by rw [hF_one, hG_one, Category.assoc, τ.naturality, IsMonoidal.unit_assoc]
  mul_hom := by rw [hF_mul, hG_mul, Category.assoc, τ.naturality, IsMonoidal.tensor_assoc]

end CategoryTheory.NatTrans
