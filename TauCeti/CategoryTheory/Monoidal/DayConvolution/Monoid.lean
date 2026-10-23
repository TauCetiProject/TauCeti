/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import TauCeti.CategoryTheory.Monoidal.DayConvolution.Braided

/-!
# Lax monoidal functors as Day convolution monoids

For monoidal categories `C` and `V`, a monoid for the Day convolution product on `C ⊛⥤ V` is the
same thing as a lax monoidal functor `C ⥤ V`: by the universal property of the Day convolution
`F ⊗ F` as a left Kan extension of `F ⊠ F` along the tensor product of `C`, a multiplication
`F ⊗ F ⟶ F` is a natural family `F x ⊗ F y ⟶ F (x ⊗ y)`, and a unit `𝟙_ ⟶ F` is a morphism
`𝟙_ V ⟶ F (𝟙_ C)`. This file constructs the direction used to build monoids: the tensorator and
unit of a lax monoidal functor `F` make `F` a monoid object of `C ⊛⥤ V`, which is commutative when
`F` is lax braided and the braiding of `C` is symmetric. Monoidal natural transformations become
monoid morphisms.

The symmetry assumption on `C` comes from the convention of Mathlib's Day convolution braiding,
which restricts along the units to `F x ⊗ G y ⟶ G y ⊗ F x ⟶ (G ⊗ F) (y ⊗ x) ⟶ (G ⊗ F) (x ⊗ y)`,
the last map being the braiding `β_ y x` of `C`.

The main application is the sphere symmetric sequence `n ↦ (S¹)^∧n`, a lax braided functor out
of the finite-bijection groupoid, whose Day convolution monoid structure is the ring structure of
the sphere symmetric spectrum.

To verify the monoid laws, we restate Mathlib's characterisations of the whiskerings, the
associator and the unitors of `C ⊛⥤ V` along the Day convolution units `η F G` and `ν C V`, and
prove that morphisms out of `(F ⊗ G) ⊗ H`, `𝟙_ ⊗ F` and `F ⊗ 𝟙_` are determined by their
restrictions along these units.

## Main definitions

* `DayFunctor.monObj`: the Day convolution monoid structure on a lax monoidal functor.
* `DayFunctor.isCommMonObj`: it is commutative for a lax braided functor out of a symmetric
  monoidal category.
* `DayFunctor.isMonHom`: monoidal natural transformations are monoid morphisms.

## Main statements

* `DayFunctor.ν_comp_one_natTrans_app`, `DayFunctor.η_app_comp_mul_natTrans_app`: the unit and
  multiplication restrict along the Day convolution units to the unit and the tensorator of `F`.
* `DayFunctor.tensor_tensor_hom_ext`, `DayFunctor.unit_tensor_hom_ext`,
  `DayFunctor.tensor_unit_hom_ext`: extensionality for morphisms out of iterated Day convolutions.

## References

* B. Day, *On closed categories of functors*, Reports of the Midwest Category Seminar IV,
  Lecture Notes in Math. 137 (1970), 1-38.
* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 2.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.MonoidalCategory.DayFunctor

open scoped ExternalProduct
open LawfulDayConvolutionMonoidalCategoryStruct

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]
    [∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)]
    [(Functor.fromPUnit.{0} <| 𝟙_ C).HasPointwiseLeftKanExtension
      (Functor.fromPUnit.{0} <| 𝟙_ V)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (tensor C) d) (tensorRight v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorLeft v)]
    [∀ (v : V) (d : C), Limits.PreservesColimitsOfShape
      (CostructuredArrow (Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
      (CostructuredArrow ((𝟭 C).prod <| Functor.fromPUnit.{0} <| 𝟙_ C) d) (tensorRight v)]
    [∀ (v : V) (d : C × C), Limits.PreservesColimitsOfShape
      (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight v)]

/-! ### The monoidal structure along the Day convolution units -/

/-- The left whiskering `F ◁ g` restricted along the Day convolution unit `η F G`. -/
@[reassoc (attr := simp)]
lemma η_app_comp_whiskerLeft_natTrans_app (F : C ⊛⥤ V) {G G' : C ⊛⥤ V} (g : G ⟶ G') (x y : C) :
    (η F G).app (x, y) ≫ (F ◁ g).natTrans.app (x ⊗ y) =
      F.functor.obj x ◁ g.natTrans.app y ≫ (η F G').app (x, y) :=
  convolutionExtensionUnit_comp_ι_map_whiskerLeft_app V F g x y

/-- The right whiskering `f ▷ G` restricted along the Day convolution unit `η F G`. -/
@[reassoc (attr := simp)]
lemma η_app_comp_whiskerRight_natTrans_app {F F' : C ⊛⥤ V} (f : F ⟶ F') (G : C ⊛⥤ V) (x y : C) :
    (η F G).app (x, y) ≫ (f ▷ G).natTrans.app (x ⊗ y) =
      f.natTrans.app x ▷ G.functor.obj y ≫ (η F' G).app (x, y) :=
  convolutionExtensionUnit_comp_ι_map_whiskerRight_app C V f G x y

/-- The tensor product `f ⊗ₘ g` restricted along the Day convolution unit `η F G`. -/
@[reassoc (attr := simp)]
lemma η_app_comp_tensorHom_natTrans_app {F F' G G' : C ⊛⥤ V} (f : F ⟶ F') (g : G ⟶ G')
    (x y : C) :
    (η F G).app (x, y) ≫ (f ⊗ₘ g).natTrans.app (x ⊗ y) =
      (f.natTrans.app x ⊗ₘ g.natTrans.app y) ≫ (η F' G').app (x, y) :=
  convolutionExtensionUnit_comp_ι_map_tensorHom_app C V f g x y

/-- The associator `(F ⊗ G) ⊗ H ≅ F ⊗ G ⊗ H` restricted along the Day convolution units: at
`(x, y, z)` it is the associator of `V`, followed by the units and the action of
`F ⊗ G ⊗ H` on the inverse associator of `C`. -/
@[reassoc (attr := simp)]
lemma η_app_whiskerRight_comp_η_app_comp_associator_hom_natTrans_app (F G H : C ⊛⥤ V)
    (x y z : C) :
    (η F G).app (x, y) ▷ H.functor.obj z ≫ (η (F ⊗ G) H).app (x ⊗ y, z) ≫
        (α_ F G H).hom.natTrans.app ((x ⊗ y) ⊗ z) =
      (α_ _ _ _).hom ≫ F.functor.obj x ◁ (η G H).app (y, z) ≫ (η F (G ⊗ H)).app (x, y ⊗ z) ≫
        (F ⊗ G ⊗ H).functor.map (α_ x y z).inv :=
  associator_hom_unit_unit V F G H x y z

/-- The left unitor `𝟙_ ⊗ F ≅ F` restricted along the Day convolution units. -/
@[reassoc (attr := simp)]
lemma ν_whiskerRight_comp_η_app_comp_leftUnitor_hom_natTrans_app (F : C ⊛⥤ V) (y : C) :
    ν C V ▷ F.functor.obj y ≫ (η (𝟙_ (C ⊛⥤ V)) F).app (𝟙_ C, y) ≫
        (λ_ F).hom.natTrans.app (𝟙_ C ⊗ y) =
      (λ_ (F.functor.obj y)).hom ≫ F.functor.map (λ_ y).inv :=
  leftUnitor_hom_unit_app V F y

/-- The right unitor `F ⊗ 𝟙_ ≅ F` restricted along the Day convolution units. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_ν_comp_η_app_comp_rightUnitor_hom_natTrans_app (F : C ⊛⥤ V) (x : C) :
    F.functor.obj x ◁ ν C V ≫ (η F (𝟙_ (C ⊛⥤ V))).app (x, 𝟙_ C) ≫
        (ρ_ F).hom.natTrans.app (x ⊗ 𝟙_ C) =
      (ρ_ (F.functor.obj x)).hom ≫ F.functor.map (ρ_ x).inv :=
  rightUnitor_hom_unit_app V F x

/-- Morphisms out of `𝟙_ ⊗ F` are determined by their restrictions along `ν C V` and the Day
convolution unit `η (𝟙_ _) F`. -/
lemma unit_tensor_hom_ext {F G : C ⊛⥤ V} {α β : 𝟙_ (C ⊛⥤ V) ⊗ F ⟶ G}
    (h : ∀ y : C, ν C V ▷ F.functor.obj y ≫ (η (𝟙_ (C ⊛⥤ V)) F).app (𝟙_ C, y) ≫
        α.natTrans.app (𝟙_ C ⊗ y) =
      ν C V ▷ F.functor.obj y ≫ (η (𝟙_ (C ⊛⥤ V)) F).app (𝟙_ C, y) ≫
        β.natTrans.app (𝟙_ C ⊗ y)) :
    α = β := by
  ext1
  apply Functor.hom_ext_of_isLeftKanExtension _ (η _ F) _
  have : ((𝟙_ (C ⊛⥤ V)).functor ⊠ F.functor).IsLeftKanExtension
      (ExternalProduct.extensionUnitLeft _ (νNatTrans C V) F.functor) :=
    (ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitLeft _ (νNatTrans C V)
      F.functor (isPointwiseLeftKanExtensionUnitUnit C V (C ⊛⥤ V))).isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension _
    (ExternalProduct.extensionUnitLeft _ (νNatTrans C V) F.functor) _
  ext ⟨⟨⟩, y⟩
  simpa using h y

/-- Morphisms out of `F ⊗ 𝟙_` are determined by their restrictions along `ν C V` and the Day
convolution unit `η F (𝟙_ _)`. -/
lemma tensor_unit_hom_ext {F G : C ⊛⥤ V} {α β : F ⊗ 𝟙_ (C ⊛⥤ V) ⟶ G}
    (h : ∀ x : C, F.functor.obj x ◁ ν C V ≫ (η F (𝟙_ (C ⊛⥤ V))).app (x, 𝟙_ C) ≫
        α.natTrans.app (x ⊗ 𝟙_ C) =
      F.functor.obj x ◁ ν C V ≫ (η F (𝟙_ (C ⊛⥤ V))).app (x, 𝟙_ C) ≫
        β.natTrans.app (x ⊗ 𝟙_ C)) :
    α = β := by
  ext1
  apply Functor.hom_ext_of_isLeftKanExtension _ (η F _) _
  have : (F.functor ⊠ (𝟙_ (C ⊛⥤ V)).functor).IsLeftKanExtension
      (ExternalProduct.extensionUnitRight _ (νNatTrans C V) F.functor) :=
    (ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitRight _ (νNatTrans C V)
      F.functor (isPointwiseLeftKanExtensionUnitUnit C V (C ⊛⥤ V))).isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension _
    (ExternalProduct.extensionUnitRight _ (νNatTrans C V) F.functor) _
  ext ⟨x, ⟨⟩⟩
  simpa using h x

/-- Morphisms out of `(F ⊗ G) ⊗ H` are determined by their restrictions along the Day
convolution units `η F G` and `η (F ⊗ G) H`. -/
lemma tensor_tensor_hom_ext {F G H K : C ⊛⥤ V} {α β : (F ⊗ G) ⊗ H ⟶ K}
    (h : ∀ x y z : C, (η F G).app (x, y) ▷ H.functor.obj z ≫ (η (F ⊗ G) H).app (x ⊗ y, z) ≫
        α.natTrans.app ((x ⊗ y) ⊗ z) =
      (η F G).app (x, y) ▷ H.functor.obj z ≫ (η (F ⊗ G) H).app (x ⊗ y, z) ≫
        β.natTrans.app ((x ⊗ y) ⊗ z)) :
    α = β := by
  ext1
  apply Functor.hom_ext_of_isLeftKanExtension _ (η (F ⊗ G) H) _
  have : ((F ⊗ G).functor ⊠ H.functor).IsLeftKanExtension
      (ExternalProduct.extensionUnitLeft _ (η F G) H.functor) :=
    (ExternalProduct.isPointwiseLeftKanExtensionExtensionUnitLeft _ (η F G)
      H.functor (isPointwiseLeftKanExtensionConvolutionExtensionUnit F G)).isLeftKanExtension
  apply Functor.hom_ext_of_isLeftKanExtension _
    (ExternalProduct.extensionUnitLeft _ (η F G) H.functor) _
  ext ⟨⟨x, y⟩, z⟩
  simpa using h x y z

section LaxMonoidal

variable (F : C ⊛⥤ V) [F.functor.LaxMonoidal]

/-- The Day convolution monoid structure on a lax monoidal functor `F`: its unit and
multiplication are induced by the unit `ε` and the tensorator `μ` of `F`. -/
instance monObj : MonObj F where
  one := unitDesc (Functor.LaxMonoidal.ε F.functor)
  mul := tensorDesc
    { app p := Functor.LaxMonoidal.μ F.functor p.1 p.2
      naturality p q f := by simp [tensorHom_def] }
  one_mul := unit_tensor_hom_ext fun y ↦ by
    simp [← comp_whiskerRight_assoc]
  mul_one := tensor_unit_hom_ext fun x ↦ by
    simp [← whiskerLeft_comp_assoc]
  mul_assoc := tensor_tensor_hom_ext fun x y z ↦ by
    simp [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc]

/-- The unit of the Day convolution monoid `F` restricts along `ν` to the unit `ε` of `F`. -/
@[reassoc (attr := simp)]
lemma ν_comp_one_natTrans_app :
    ν C V ≫ (MonObj.one : 𝟙_ (C ⊛⥤ V) ⟶ F).natTrans.app (𝟙_ C) =
      Functor.LaxMonoidal.ε F.functor :=
  ν_comp_unitDesc _

/-- The multiplication of the Day convolution monoid `F` restricts along `η F F` to the
tensorator `μ` of `F`. -/
@[reassoc (attr := simp)]
lemma η_app_comp_mul_natTrans_app (x y : C) :
    (η F F).app (x, y) ≫ (MonObj.mul : F ⊗ F ⟶ F).natTrans.app (x ⊗ y) =
      Functor.LaxMonoidal.μ F.functor x y :=
  η_comp_tensorDesc_app _ _ _

end LaxMonoidal

/-- A monoidal natural transformation of lax monoidal functors is a morphism of the associated
Day convolution monoids. -/
instance isMonHom {F G : C ⊛⥤ V} [F.functor.LaxMonoidal] [G.functor.LaxMonoidal] (f : F ⟶ G)
    [NatTrans.IsMonoidal f.natTrans] : IsMonHom f where
  one_hom := unit_hom_ext (by simp)
  mul_hom := tensor_hom_ext fun x y ↦ by simp

section LaxBraided

variable [SymmetricCategory C] [BraidedCategory V] (F : C ⊛⥤ V) [F.functor.LaxBraided]

/-- The Day convolution monoid of a lax braided functor out of a symmetric monoidal category is
commutative. -/
instance isCommMonObj : IsCommMonObj F where
  mul_comm := tensor_hom_ext fun x y ↦ by
    simp [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp]

end LaxBraided

end

end CategoryTheory.MonoidalCategory.DayFunctor
