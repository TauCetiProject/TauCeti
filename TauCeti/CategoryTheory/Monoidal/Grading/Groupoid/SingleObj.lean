/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid.VertexGroup
public import TauCeti.CategoryTheory.Monoidal.Grading.Groupoid.Basic
public import TauCeti.CategoryTheory.Monoidal.Grading.Universal
public import TauCeti.CategoryTheory.SingleObj

/-!
# Comparison between the universal grading groupoid and group functors

Without assuming `[Simple (𝟙_ C)]` or `[RigidCategory C]`, for any monoid `G`,
`TauCeti.universalGradingGroupoid.singleObjFunctorEquiv` gives a bijection
`(universalGradingGroupoid C ⥤ SingleObj G) ≃ (universalGradingGroup C →* Gᵐᵒᵖ)`. For a
commutative monoid `A`, `singleObjFunctorMulEquiv` upgrades this to a multiplicative equivalence
`(universalGradingGroupoid C ⥤ SingleObj A) ≃* (universalGradingGroup C →* A)`.

When `[Simple (𝟙_ C)]`, `universalGradingGroupoid C` has a unique object (`Unique`) and is
equivalent to `SingleObj (universalGradingGroup C)ᵐᵒᵖ` (`singleObjEquivalence`), identifying its
vertex group with `universalGradingGroup C` (`vertexGroupMulEquiv`).

## Main declarations

* `TauCeti.universalGradingGroupoid.singleObjFunctorEquiv`: bijection
  `(universalGradingGroupoid C ⥤ SingleObj G) ≃ (universalGradingGroup C →* Gᵐᵒᵖ)`.
* `TauCeti.universalGradingGroupoid.singleObjFunctorMulEquiv`: multiplicative equivalence
  `(universalGradingGroupoid C ⥤ SingleObj A) ≃* (universalGradingGroup C →* A)`.
* `TauCeti.universalGradingGroupoid.singleObjEquivalence`: equivalence
  `universalGradingGroupoid C ≌ SingleObj (universalGradingGroup C)ᵐᵒᵖ` when `[Simple (𝟙_ C)]`.
* `TauCeti.universalGradingGroupoid.vertexGroupMulEquiv`: group isomorphism between the vertex
  group of `universalGradingGroupoid C` and `universalGradingGroup C` when `[Simple (𝟙_ C)]`.

## References

* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  Higher Structures **4** (2020), no. 2, 22–56 (arXiv:1808.00323), §3.3
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.14
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe v₁ u₁ w

namespace TauCeti.universalGradingGroupoid

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [IsFiniteSemisimpleCategory C]

section SingleObjComparison

/-- For any monoid `G`, functors `universalGradingGroupoid C ⥤ SingleObj G` correspond
bijectively to monoid homomorphisms `universalGradingGroup C →* Gᵐᵒᵖ` (the opposite monoid
accounts for `SingleObj`'s reversed composition `f ≫ g = g * f`, and every arrow of
`universalGradingGroupoid C` maps into the units `Gˣ`). Neither `[Simple (𝟙_ C)]` nor
`[RigidCategory C]` is required. -/
def singleObjFunctorEquiv (G : Type w) [Monoid G] :
    (universalGradingGroupoid C ⥤ SingleObj G) ≃ (universalGradingGroup C →* Gᵐᵒᵖ) where
  toFun F :=
    universalGradingGroup.liftOfIsUnit
      (fun S ↦ MulOpposite.op (F.map (degree S)))
      (fun S ↦ Units.isUnit (⟨MulOpposite.op (F.map (degree S)),
        MulOpposite.op (F.map (inv (degree S))),
        MulOpposite.unop_injective <| by
          change (F.map (inv (degree S)) : G) * (F.map (degree S) : G) = 1
          rw [← SingleObj.comp_as_mul, ← CategoryTheory.Functor.map_comp,
            IsIso.hom_inv_id, CategoryTheory.Functor.map_id, SingleObj.id_as_one],
        MulOpposite.unop_injective <| by
          change (F.map (degree S) : G) * (F.map (inv (degree S)) : G) = 1
          rw [← SingleObj.comp_as_mul, ← CategoryTheory.Functor.map_comp,
            IsIso.inv_hom_id, CategoryTheory.Functor.map_id, SingleObj.id_as_one]⟩ : Gᵐᵒᵖˣ))
      fun S T U f hf ↦ MulOpposite.unop_injective <| by
        change (F.map (degree U) : G) = (F.map (degree T) : G) * (F.map (degree S) : G)
        rw [← SingleObj.comp_as_mul, degree_comp f hf]
        simp only [CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_refl,
          Category.id_comp, Category.comp_id]
  invFun χ :=
    lift
      { obj := fun _ ↦ SingleObj.star Gˣ
        deg := fun S ↦
          Units.mk
            (MulOpposite.unop (χ (universalGradingGroup.degree S)))
            (MulOpposite.unop (χ (universalGradingGroup.degree S)⁻¹))
            (MulOpposite.op_injective <| by simp [← map_mul])
            (MulOpposite.op_injective <| by simp [← map_mul])
        deg_comp := fun {S T U} f hf ↦ Units.ext <| by
          simp only [eqToHom_refl, Category.id_comp, Category.comp_id, SingleObj.comp_as_mul]
          rw [universalGradingGroup.degree_mul S T U f hf, map_mul, MulOpposite.unop_mul]
          rfl } ⋙
      SingleObj.mapHom Gˣ G (Units.coeHom G)
  left_inv F := functor_ext (fun _ ↦ rfl) fun S ↦ by
    simp [eqToHom_refl]
  right_inv χ := universalGradingGroup.hom_ext fun S ↦ by
    simp [eqToHom_refl]

@[simp]
theorem singleObjFunctorEquiv_apply_degree (G : Type w) [Monoid G]
    (F : universalGradingGroupoid C ⥤ SingleObj G) (S : SimpleClasses C) :
    singleObjFunctorEquiv G F (universalGradingGroup.degree S) =
      MulOpposite.op (F.map (degree S)) := by
  simp [singleObjFunctorEquiv]

theorem singleObjFunctorEquiv_apply_degree_classOf (G : Type w) [Monoid G]
    (F : universalGradingGroupoid C ⥤ SingleObj G) (X : C) [Simple X] :
    singleObjFunctorEquiv G F (universalGradingGroup.degree (SimpleClasses.classOf X)) =
      MulOpposite.op (F.map (degreeOf X)) := by
  rw [singleObjFunctorEquiv_apply_degree]
  simp only [degreeOf_def, CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_refl,
    Category.id_comp, Category.comp_id]

@[simp]
theorem singleObjFunctorEquiv_symm_map_degree (G : Type w) [Monoid G]
    (χ : universalGradingGroup C →* Gᵐᵒᵖ) (S : SimpleClasses C) :
    ((singleObjFunctorEquiv G).symm χ).map (degree S) =
      MulOpposite.unop (χ (universalGradingGroup.degree S)) := by
  simp [singleObjFunctorEquiv]

@[simp]
theorem singleObjFunctorEquiv_symm_map_degreeOf (G : Type w) [Monoid G]
    (χ : universalGradingGroup C →* Gᵐᵒᵖ) (X : C) [Simple X] :
    ((singleObjFunctorEquiv G).symm χ).map (degreeOf X) =
      MulOpposite.unop (χ (universalGradingGroup.degree (SimpleClasses.classOf X))) := by
  simp only [degreeOf_def, CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_refl,
    Category.id_comp, Category.comp_id, singleObjFunctorEquiv_symm_map_degree]

/-- For a commutative monoid `A`, `A`-valued groupoid characters
`universalGradingGroupoid C ⥤ SingleObj A` are canonically isomorphic as a monoid to characters
`universalGradingGroup C →* A` of the universal grading group. Neither `[Simple (𝟙_ C)]` nor
`[RigidCategory C]` is required. -/
def singleObjFunctorMulEquiv (A : Type w) [CommMonoid A] :
    (universalGradingGroupoid C ⥤ SingleObj A) ≃* (universalGradingGroup C →* A) where
  toFun F := (MulOpposite.opMulEquiv (M := A)).symm.toMonoidHom.comp (singleObjFunctorEquiv A F)
  invFun χ := (singleObjFunctorEquiv A).symm ((MulOpposite.opMulEquiv (M := A)).toMonoidHom.comp χ)
  left_inv F := (singleObjFunctorEquiv A).injective <| by ext x; simp
  right_inv χ := by ext x; simp
  map_mul' F₁ F₂ := universalGradingGroup.hom_ext fun S ↦ by simp [SingleObj.functor_mul_map]

@[simp]
theorem singleObjFunctorMulEquiv_apply_degree (A : Type w) [CommMonoid A]
    (F : universalGradingGroupoid C ⥤ SingleObj A) (S : SimpleClasses C) :
    singleObjFunctorMulEquiv A F (universalGradingGroup.degree S) = F.map (degree S) := by
  simp [singleObjFunctorMulEquiv]

theorem singleObjFunctorMulEquiv_apply_degree_classOf (A : Type w) [CommMonoid A]
    (F : universalGradingGroupoid C ⥤ SingleObj A) (X : C) [Simple X] :
    singleObjFunctorMulEquiv A F (universalGradingGroup.degree (SimpleClasses.classOf X)) =
      F.map (degreeOf X) := by
  rw [singleObjFunctorMulEquiv_apply_degree]
  simp only [degreeOf_def, CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_refl,
    Category.id_comp, Category.comp_id]

@[simp]
theorem singleObjFunctorMulEquiv_symm_map_degree (A : Type w) [CommMonoid A]
    (χ : universalGradingGroup C →* A) (S : SimpleClasses C) :
    ((singleObjFunctorMulEquiv A).symm χ).map (degree S) = χ (universalGradingGroup.degree S) := by
  change ((singleObjFunctorEquiv A).symm
      ((MulOpposite.opMulEquiv (M := A)).toMonoidHom.comp χ)).map (degree S) = _
  simp

@[simp]
theorem singleObjFunctorMulEquiv_symm_map_degreeOf (A : Type w) [CommMonoid A]
    (χ : universalGradingGroup C →* A) (X : C) [Simple X] :
    ((singleObjFunctorMulEquiv A).symm χ).map (degreeOf X) =
      χ (universalGradingGroup.degree (SimpleClasses.classOf X)) := by
  simp only [degreeOf_def, CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_refl,
    Category.id_comp, Category.comp_id, singleObjFunctorMulEquiv_symm_map_degree]

end SingleObjComparison

section SimpleUnit

variable [Simple (𝟙_ C)]

instance instUnique : Unique (universalGradingGroupoid C) where
  default := mkObj UnitSimpleClasses.unit
  uniq x := by
    obtain ⟨I, rfl⟩ := mkObj.surjective x
    exact congrArg mkObj (Subsingleton.elim I UnitSimpleClasses.unit)

@[simp]
theorem default_eq_mkObj_unit :
    (default : universalGradingGroupoid C) = mkObj UnitSimpleClasses.unit := (rfl)

private def toSingleObjGradingGroup :
    universalGradingGroupoid C ⥤ SingleObj (universalGradingGroup C)ᵐᵒᵖ :=
  (singleObjFunctorEquiv (universalGradingGroup C)ᵐᵒᵖ).symm
    (MulEquiv.opOp (universalGradingGroup C)).toMonoidHom

private def fromSingleObjGradingGroupHom :
    universalGradingGroup C →* ((default : universalGradingGroupoid C) ⟶ default) :=
  universalGradingGroup.lift
    (fun S ↦ eqToHom (Subsingleton.elim _ _) ≫ degree S ≫ eqToHom (Subsingleton.elim _ _))
    fun S T U f hf ↦ by
      rw [degree_comp f hf]; simp [CategoryTheory.Groupoid.vertexGroup_mul, Category.assoc]

private def fromSingleObjGradingGroup :
    SingleObj (universalGradingGroup C)ᵐᵒᵖ ⥤ universalGradingGroupoid C where
  obj _ := default
  map m := fromSingleObjGradingGroupHom (MulOpposite.unop m)
  map_id _ := fromSingleObjGradingGroupHom.map_one
  map_comp m₁ m₂ := fromSingleObjGradingGroupHom.map_mul (MulOpposite.unop m₁) (MulOpposite.unop m₂)

private theorem toSingleObj_comp_fromSingleObj :
    toSingleObjGradingGroup (C := C) ⋙ fromSingleObjGradingGroup (C := C) =
      𝟭 (universalGradingGroupoid C) := by
  refine functor_ext (fun _ ↦ Subsingleton.elim _ _) fun S ↦ ?_
  simp [toSingleObjGradingGroup, fromSingleObjGradingGroup, fromSingleObjGradingGroupHom]

private theorem fromSingleObj_comp_toSingleObj :
    fromSingleObjGradingGroup (C := C) ⋙ toSingleObjGradingGroup (C := C) =
      𝟭 (SingleObj (universalGradingGroup C)ᵐᵒᵖ) := by
  refine SingleObj.functor_ext fun m ↦ MulOpposite.unop_injective ?_
  let ψ : universalGradingGroup C →* universalGradingGroup C :=
    { toFun := fun x ↦
        MulOpposite.unop ((toSingleObjGradingGroup (C := C)).map (fromSingleObjGradingGroupHom x))
      map_one' := by
        rw [map_one, CategoryTheory.Groupoid.vertexGroup_one, CategoryTheory.Functor.map_id]; rfl
      map_mul' := fun x y ↦ by
        rw [map_mul, CategoryTheory.Groupoid.vertexGroup_mul, CategoryTheory.Functor.map_comp]
        rfl }
  have hψ : ψ = MonoidHom.id (universalGradingGroup C) := by
    ext S
    simp [ψ, fromSingleObjGradingGroupHom, toSingleObjGradingGroup, eqToHom_map, eqToHom_refl]
  exact DFunLike.congr_fun hψ (MulOpposite.unop m)

/-- When `𝟙_ C` is simple, `universalGradingGroupoid C` is equivalent (in fact, isomorphic) to
`SingleObj (universalGradingGroup C)ᵐᵒᵖ`. -/
def singleObjEquivalence :
    universalGradingGroupoid C ≌ SingleObj (universalGradingGroup C)ᵐᵒᵖ where
  functor := toSingleObjGradingGroup
  inverse := fromSingleObjGradingGroup
  unitIso := eqToIso toSingleObj_comp_fromSingleObj.symm
  counitIso := eqToIso fromSingleObj_comp_toSingleObj
  functor_unitIso_comp _ := by simp [eqToHom_map]

@[simp]
theorem singleObjEquivalence_functor_obj (x : universalGradingGroupoid C) :
    singleObjEquivalence.functor.obj x = SingleObj.star _ := (rfl)

@[simp]
theorem singleObjEquivalence_inverse_obj (x : SingleObj (universalGradingGroup C)ᵐᵒᵖ) :
    singleObjEquivalence.inverse.obj x = default := (rfl)

@[simp]
theorem singleObjEquivalence_functor_map_degree (S : SimpleClasses C) :
    singleObjEquivalence.functor.map (degree S) =
      MulOpposite.op (universalGradingGroup.degree S) := by
  simp [singleObjEquivalence, toSingleObjGradingGroup]

@[simp]
theorem singleObjEquivalence_functor_map_degreeOf (X : C) [Simple X] :
    singleObjEquivalence.functor.map (degreeOf X) =
      MulOpposite.op (universalGradingGroup.degree (SimpleClasses.classOf X)) := by
  simp [singleObjEquivalence, toSingleObjGradingGroup]

@[simp]
theorem singleObjEquivalence_inverse_map_op_degree (S : SimpleClasses C) :
    singleObjEquivalence.inverse.map
        (X := SingleObj.star (universalGradingGroup C)ᵐᵒᵖ)
        (Y := SingleObj.star (universalGradingGroup C)ᵐᵒᵖ)
        (MulOpposite.op (universalGradingGroup.degree S)) =
      eqToHom (Subsingleton.elim _ _) ≫ degree S ≫ eqToHom (Subsingleton.elim _ _) := by
  simp [singleObjEquivalence, fromSingleObjGradingGroup, fromSingleObjGradingGroupHom]

theorem singleObjEquivalence_inverse_map_op_degree_classOf (X : C) [Simple X] :
    singleObjEquivalence.inverse.map
        (X := SingleObj.star (universalGradingGroup C)ᵐᵒᵖ)
        (Y := SingleObj.star (universalGradingGroup C)ᵐᵒᵖ)
        (MulOpposite.op (universalGradingGroup.degree (SimpleClasses.classOf X))) =
      eqToHom (Subsingleton.elim _ _) ≫ degreeOf X ≫ eqToHom (Subsingleton.elim _ _) := by
  simp [singleObjEquivalence_inverse_map_op_degree, degreeOf_def, Category.assoc]

/-- When `𝟙_ C` is simple, the vertex group of `universalGradingGroupoid C` at its unique object is
canonically isomorphic to `universalGradingGroup C`. -/
def vertexGroupMulEquiv :
    ((default : universalGradingGroupoid C) ⟶ default) ≃* universalGradingGroup C where
  toFun g := MulOpposite.unop ((toSingleObjGradingGroup (C := C)).map g)
  invFun := fromSingleObjGradingGroupHom
  left_inv g :=
    eq_of_heq (CategoryTheory.Functor.hcongr_hom (toSingleObj_comp_fromSingleObj (C := C)) g)
  right_inv x := by
    let m : SingleObj.star (universalGradingGroup C)ᵐᵒᵖ ⟶
        SingleObj.star (universalGradingGroup C)ᵐᵒᵖ := MulOpposite.op x
    simpa [fromSingleObjGradingGroup, m] using
      congrArg MulOpposite.unop
        (CategoryTheory.Functor.congr_hom (fromSingleObj_comp_toSingleObj (C := C)) m)
  map_mul' g₁ g₂ := by
    rw [CategoryTheory.Groupoid.vertexGroup_mul, CategoryTheory.Functor.map_comp]; rfl

@[simp]
theorem vertexGroupMulEquiv_degree (S : SimpleClasses C) :
    vertexGroupMulEquiv
        (eqToHom (Subsingleton.elim _ _) ≫ degree S ≫ eqToHom (Subsingleton.elim _ _)) =
      universalGradingGroup.degree S := by
  simp [vertexGroupMulEquiv, toSingleObjGradingGroup, eqToHom_map, eqToHom_refl]

@[simp]
theorem vertexGroupMulEquiv_degreeOf (X : C) [Simple X] :
    vertexGroupMulEquiv
        (eqToHom (Subsingleton.elim _ _) ≫ degreeOf X ≫ eqToHom (Subsingleton.elim _ _)) =
      universalGradingGroup.degree (SimpleClasses.classOf X) := by
  simp [vertexGroupMulEquiv, toSingleObjGradingGroup, eqToHom_map, eqToHom_refl]

@[simp]
theorem vertexGroupMulEquiv_symm_degree (S : SimpleClasses C) :
    vertexGroupMulEquiv.symm (universalGradingGroup.degree S) =
      eqToHom (Subsingleton.elim _ _) ≫ degree S ≫ eqToHom (Subsingleton.elim _ _) := by
  simp [vertexGroupMulEquiv, fromSingleObjGradingGroupHom]

theorem vertexGroupMulEquiv_symm_degree_classOf (X : C) [Simple X] :
    vertexGroupMulEquiv.symm (universalGradingGroup.degree (SimpleClasses.classOf X)) =
      eqToHom (Subsingleton.elim _ _) ≫ degreeOf X ≫ eqToHom (Subsingleton.elim _ _) := by
  rw [vertexGroupMulEquiv_symm_degree, degreeOf_def]; simp [Category.assoc]

end SimpleUnit

end TauCeti.universalGradingGroupoid
