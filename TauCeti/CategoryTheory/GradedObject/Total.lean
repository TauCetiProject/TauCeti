/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import TauCeti.CategoryTheory.GradedObject.MonObj

/-!
# The total object of a graded object is lax monoidal

For a monoidal category `C` with coproducts and an additive monoid `I`, the total object
`GradedObject.total I C` sends a graded object `X` to the coproduct `∐ᵢ Xᵢ` of its components.
When tensoring on either side preserves coproducts indexed by `I`, the tensor product
`(∐ᵢ Xᵢ) ⊗ (∐ⱼ Yⱼ)` is the coproduct of the `Xᵢ ⊗ Yⱼ`, and sending the summand `Xᵢ ⊗ Yⱼ` to the
summand of degree `i + j` of `X ⊗ Y` makes the total object a lax monoidal functor from graded
objects (with the convolution tensor product) to `C`; its unit is the inclusion of `𝟙_ C` in
degree `0`. When `C` is braided and `I` is commutative, the functor is lax braided.

Consequently a (commutative) monoid object in graded objects, such as a graded algebra, has a
(commutative) monoid object as its total object, through `CategoryTheory.Functor.mapMon` and
`CategoryTheory.Functor.mapCommMon`: this is the direct-sum algebra underlying a graded
algebra.

## Main declarations

* `CategoryTheory.GradedObject.ιTotal`: the inclusion of the summand `Xᵢ` into `∐ᵢ Xᵢ`;
* `CategoryTheory.GradedObject.totalTensorDesc`: the morphism out of `(∐ᵢ Xᵢ) ⊗ (∐ⱼ Yⱼ)` given on
  each summand `Xᵢ ⊗ Yⱼ`, with the extensionality lemma
  `CategoryTheory.GradedObject.total_tensor_hom_ext`;
* `CategoryTheory.GradedObject.totalLaxMonoidal`: the lax monoidal structure on the total
  object, characterized by `CategoryTheory.GradedObject.ιTotal_tensorHom_ιTotal_total_μ` and
  `CategoryTheory.GradedObject.total_ε`;
* `CategoryTheory.GradedObject.totalLaxBraided`: the total object is lax braided.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.GradedObject

universe v u

variable {I : Type} {C : Type u} [Category.{v} C] [HasCoproducts.{0} C]

/-- The inclusion of the summand `X i` into the total object `∐ᵢ Xᵢ` of a graded object. It is
`Sigma.ι` with its target written as `(total I C).obj X`, so that it composes with the action of
`total I C` on morphisms and with its monoidal structure maps. -/
abbrev ιTotal (X : GradedObject I C) (i : I) : X i ⟶ (total I C).obj X :=
  Sigma.ι (fun i ↦ X i) i

/-- On the summand `Xᵢ`, the total object of a morphism of graded objects is its component in
degree `i`. -/
@[reassoc (attr := simp)]
lemma ιTotal_total_map {X Y : GradedObject I C} (f : X ⟶ Y) (i : I) :
    ιTotal X i ≫ (total I C).map f = f i ≫ ιTotal Y i :=
  Sigma.ι_map _ _

variable [MonoidalCategory C]

/-- Morphisms out of `A ⊗ (∐ᵢ Xᵢ)` agree as soon as they agree on every summand `A ⊗ Xᵢ`. -/
lemma whiskerLeft_total_hom_ext {A B : C} [PreservesColimitsOfShape (Discrete I) (tensorLeft A)]
    {X : GradedObject I C} {f g : A ⊗ (total I C).obj X ⟶ B}
    (h : ∀ i, A ◁ ιTotal X i ≫ f = A ◁ ιTotal X i ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (isColimitOfHasCoproductOfPreservesColimit (tensorLeft A) X) _ _ h

/-- Morphisms out of `(∐ᵢ Xᵢ) ⊗ A` agree as soon as they agree on every summand `Xᵢ ⊗ A`. -/
lemma whiskerRight_total_hom_ext {A B : C}
    [PreservesColimitsOfShape (Discrete I) (tensorRight A)] {X : GradedObject I C}
    {f g : (total I C).obj X ⊗ A ⟶ B} (h : ∀ i, ιTotal X i ▷ A ≫ f = ιTotal X i ▷ A ≫ g) :
    f = g :=
  Cofan.IsColimit.hom_ext (isColimitOfHasCoproductOfPreservesColimit (tensorRight A) X) _ _ h

section Ext

variable [∀ A : C, PreservesColimitsOfShape (Discrete I) (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape (Discrete I) (tensorRight A)]

/-- The tensor product `(∐ᵢ Xᵢ) ⊗ (∐ⱼ Yⱼ)` is the coproduct of the `Xᵢ ⊗ Yⱼ`: the morphism out
of it given on each summand `Xᵢ ⊗ Yⱼ` by `φ i j`. -/
def totalTensorDesc {X Y : GradedObject I C} {A : C} (φ : ∀ i j, X i ⊗ Y j ⟶ A) :
    (total I C).obj X ⊗ (total I C).obj Y ⟶ A :=
  Cofan.IsColimit.desc (isColimitOfHasCoproductOfPreservesColimit
      (tensorRight ((total I C).obj Y)) X) fun i ↦
    Cofan.IsColimit.desc (isColimitOfHasCoproductOfPreservesColimit (tensorLeft (X i)) Y)
      fun j ↦ φ i j

/-- On the summand `Xᵢ ⊗ Yⱼ`, `totalTensorDesc φ` is `φ i j`. -/
@[reassoc (attr := simp)]
lemma ιTotal_tensorHom_ιTotal_totalTensorDesc {X Y : GradedObject I C} {A : C}
    (φ : ∀ i j, X i ⊗ Y j ⟶ A) (i j : I) :
    (ιTotal X i ⊗ₘ ιTotal Y j) ≫ totalTensorDesc φ = φ i j := by
  rw [tensorHom_def', Category.assoc]
  exact (congrArg (X i ◁ ιTotal Y j ≫ ·) (Cofan.IsColimit.fac
      (isColimitOfHasCoproductOfPreservesColimit (tensorRight ((total I C).obj Y)) X) _ i)).trans
    (Cofan.IsColimit.fac (isColimitOfHasCoproductOfPreservesColimit (tensorLeft (X i)) Y) _ j)

/-- Morphisms out of `(∐ᵢ Xᵢ) ⊗ (∐ⱼ Yⱼ)` agree as soon as they agree on every summand
`Xᵢ ⊗ Yⱼ`. -/
lemma total_tensor_hom_ext {X Y : GradedObject I C} {A : C}
    {f g : (total I C).obj X ⊗ (total I C).obj Y ⟶ A}
    (h : ∀ i j, (ιTotal X i ⊗ₘ ιTotal Y j) ≫ f = (ιTotal X i ⊗ₘ ιTotal Y j) ≫ g) :
    f = g :=
  whiskerRight_total_hom_ext fun i ↦ whiskerLeft_total_hom_ext fun j ↦ by
    simpa only [tensorHom_def', Category.assoc] using h i j

/-- Morphisms out of `((∐ᵢ Xᵢ) ⊗ (∐ⱼ Yⱼ)) ⊗ (∐ₖ Zₖ)` agree as soon as they agree on every
summand `(Xᵢ ⊗ Yⱼ) ⊗ Zₖ`. -/
lemma total_tensor_tensor_hom_ext {X Y Z : GradedObject I C} {A : C}
    {f g : ((total I C).obj X ⊗ (total I C).obj Y) ⊗ (total I C).obj Z ⟶ A}
    (h : ∀ i j k, ((ιTotal X i ⊗ₘ ιTotal Y j) ⊗ₘ ιTotal Z k) ≫ f =
      ((ιTotal X i ⊗ₘ ιTotal Y j) ⊗ₘ ιTotal Z k) ≫ g) :
    f = g := by
  refine Cofan.IsColimit.hom_ext (isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft _) Z) _ _ fun k ↦ ?_
  refine Cofan.IsColimit.hom_ext (isColimitOfHasCoproductOfPreservesColimit
    (tensorRight ((total I C).obj Y) ⋙ tensorRight (Z k)) X) _ _ fun i ↦ ?_
  refine Cofan.IsColimit.hom_ext (isColimitOfHasCoproductOfPreservesColimit
    (tensorLeft (X i) ⋙ tensorRight (Z k)) Y) _ _ fun j ↦ ?_
  have hijk := h i j k
  rw [tensorHom_def, tensorHom_def', comp_whiskerRight] at hijk
  simp only [Category.assoc] at hijk
  exact hijk

end Ext

section LaxMonoidal

variable [AddMonoid I]
  [∀ A : C, PreservesColimitsOfShape (Discrete I) (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape (Discrete I) (tensorRight A)]
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

@[reassoc]
private lemma ιTotal_tensorHom_ιTotal_totalTensorDesc_ιTensorObj (X Y : GradedObject I C)
    (i j n : I) (h : i + j = n) :
    (ιTotal X i ⊗ₘ ιTotal Y j) ≫ totalTensorDesc (fun i j ↦
      Monoidal.ιTensorObj X Y i j (i + j) rfl ≫ ιTotal (X ⊗ Y) (i + j)) =
      Monoidal.ιTensorObj X Y i j n h ≫ ιTotal (X ⊗ Y) n := by
  subst h
  exact ιTotal_tensorHom_ιTotal_totalTensorDesc _ i j

section Laws

variable (μ' : ∀ X Y : GradedObject I C, (total I C).obj X ⊗ (total I C).obj Y ⟶
    (total I C).obj (X ⊗ Y))
  (hμ' : ∀ (X Y : GradedObject I C) (i j n : I) (h : i + j = n),
    (ιTotal X i ⊗ₘ ιTotal Y j) ≫ μ' X Y = Monoidal.ιTensorObj X Y i j n h ≫ ιTotal (X ⊗ Y) n)
include hμ'

omit [∀ A : C, PreservesColimitsOfShape (Discrete I) (tensorLeft A)]
    [∀ A : C, PreservesColimitsOfShape (Discrete I) (tensorRight A)] in
private lemma total_μ_component {P Q : C} (X Y : GradedObject I C) (i j n : I)
    (h : i + j = n) (f : P ⟶ X i) (g : Q ⟶ Y j) :
    ((f ≫ ιTotal X i) ⊗ₘ (g ≫ ιTotal Y j)) ≫ μ' X Y =
      (f ⊗ₘ g) ≫ Monoidal.ιTensorObj X Y i j n h ≫ ιTotal (X ⊗ Y) n := by
  rw [← tensorHom_comp_tensorHom_assoc, hμ' X Y i j n h]

private lemma total_μ_natural {X Y X' Y' : GradedObject I C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    ((total I C).map f ⊗ₘ (total I C).map g) ≫ μ' Y Y' = μ' X X' ≫ (total I C).map (f ⊗ₘ g) := by
  refine total_tensor_hom_ext fun i j ↦ ?_
  rw [tensorHom_comp_tensorHom_assoc, ιTotal_total_map, ιTotal_total_map,
    total_μ_component μ' hμ' Y Y' i j _ rfl (f i) (g j),
    reassoc_of% (hμ' X X' i j _ rfl),
    ιTotal_total_map, ← Category.assoc, ← Category.assoc]
  -- The tensor product of morphisms of graded objects is `Monoidal.tensorHom`.
  exact congrArg (· ≫ _) (Monoidal.ι_tensorHom f g i j _ rfl).symm

private lemma total_associativity (X Y Z : GradedObject I C) :
    (μ' X Y ⊗ₘ 𝟙 ((total I C).obj Z)) ≫ μ' (X ⊗ Y) Z ≫ (total I C).map (α_ X Y Z).hom =
      (α_ ((total I C).obj X) ((total I C).obj Y) ((total I C).obj Z)).hom ≫
        (𝟙 ((total I C).obj X) ⊗ₘ μ' Y Z) ≫ μ' X (Y ⊗ Z) := by
  refine total_tensor_tensor_hom_ext fun i j k ↦ ?_
  -- On the summand `(Xᵢ ⊗ Yⱼ) ⊗ Zₖ` both sides land in the summand of degree `i + j + k`
  -- through the inclusions of triple tensor products, which the graded associator relates.
  have key := Monoidal.ιTensorObj₃'_associator_hom_assoc X Y Z i j k _ rfl
    (ιTotal (X ⊗ (Y ⊗ Z)) (i + j + k))
  rw [Monoidal.ιTensorObj₃'_eq X Y Z i j k _ rfl (i + j) rfl, Category.assoc,
    Monoidal.ιTensorObj₃_eq_assoc X Y Z i j k _ rfl (j + k) rfl] at key
  refine Eq.trans ?_ (key.trans ?_)
  -- In both cases `rfl` identifies the tensor product and the associator of graded objects with
  -- `Monoidal.tensorObj` and `Monoidal.associator`, in which `key` is stated.
  · rw [tensorHom_comp_tensorHom_assoc, hμ' X Y i j _ rfl]
    simp only [Category.comp_id]
    rw [reassoc_of% (total_μ_component μ' hμ' (X ⊗ Y) Z (i + j) k
        (i + j + k) rfl (Monoidal.ιTensorObj X Y i j (i + j) rfl) (𝟙 (Z k))),
      ιTotal_total_map]
    simp only [tensorHom_id]
    rfl
  · rw [associator_naturality_assoc, tensorHom_comp_tensorHom_assoc, hμ' Y Z j k _ rfl]
    simp only [Category.comp_id]
    rw [← Category.id_comp (ιTotal X i), ← tensorHom_comp_tensorHom_assoc,
      hμ' X (Y ⊗ Z) i (j + k) (i + j + k) (add_assoc i j k).symm]
    simp only [id_tensorHom]
    rfl

omit [∀ A : C, PreservesColimitsOfShape (Discrete I) (tensorRight A)] in
private lemma total_left_unitality (X : GradedObject I C) :
    (λ_ ((total I C).obj X)).hom =
      ((Monoidal.tensorUnit₀.inv ≫ ιTotal (𝟙_ (GradedObject I C)) 0) ⊗ₘ
        𝟙 ((total I C).obj X)) ≫ μ' (𝟙_ (GradedObject I C)) X ≫
        (total I C).map (λ_ X).hom := by
  refine whiskerLeft_total_hom_ext fun i ↦ ?_
  rw [leftUnitor_naturality]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp,
    Category.comp_id]
  conv_rhs => rw [reassoc_of% (total_μ_component μ' hμ' (𝟙_ (GradedObject I C)) X
    0 i i (zero_add i) Monoidal.tensorUnit₀.inv (𝟙 (X i))), ιTotal_total_map,
    tensorHom_id]
  -- The left unitor of graded objects is inverse to the inclusion of `𝟙_ C ⊗ X i` in degree
  -- `0 + i` (`Monoidal.leftUnitor_inv_apply`).
  have h : Monoidal.tensorUnit₀.inv ▷ X i ≫
      Monoidal.ιTensorObj (𝟙_ (GradedObject I C)) X 0 i i (zero_add i) =
        (λ_ (X i)).hom ≫ (λ_ X).inv i :=
    (Iso.inv_comp_eq _).1 (Monoidal.leftUnitor_inv_apply X i).symm
  rw [reassoc_of% h, Iso.inv_hom_id_eval_assoc]

omit [∀ A : C, PreservesColimitsOfShape (Discrete I) (tensorLeft A)] in
private lemma total_right_unitality (X : GradedObject I C) :
    (ρ_ ((total I C).obj X)).hom =
      (𝟙 ((total I C).obj X) ⊗ₘ
        (Monoidal.tensorUnit₀.inv ≫ ιTotal (𝟙_ (GradedObject I C)) 0)) ≫
        μ' X (𝟙_ (GradedObject I C)) ≫ (total I C).map (ρ_ X).hom := by
  refine whiskerRight_total_hom_ext fun i ↦ ?_
  rw [rightUnitor_naturality]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp,
    Category.comp_id]
  conv_rhs => rw [reassoc_of% (total_μ_component μ' hμ' X (𝟙_ (GradedObject I C))
    i 0 i (add_zero i) (𝟙 (X i)) Monoidal.tensorUnit₀.inv), ιTotal_total_map,
    id_tensorHom]
  -- The right unitor of graded objects is inverse to the inclusion of `X i ⊗ 𝟙_ C` in degree
  -- `i + 0` (`Monoidal.rightUnitor_inv_apply`).
  have h : X i ◁ Monoidal.tensorUnit₀.inv ≫
      Monoidal.ιTensorObj X (𝟙_ (GradedObject I C)) i 0 i (add_zero i) =
        (ρ_ (X i)).hom ≫ (ρ_ X).inv i :=
    (Iso.inv_comp_eq _).1 (Monoidal.rightUnitor_inv_apply X i).symm
  rw [reassoc_of% h, Iso.inv_hom_id_eval_assoc]

end Laws

/-- The total object `X ↦ ∐ᵢ Xᵢ` is lax monoidal, when tensoring on either side preserves
coproducts indexed by `I`. Its tensor map sends the summand `Xᵢ ⊗ Yⱼ` of `(∐ᵢ Xᵢ) ⊗ (∐ⱼ Yⱼ)` to
the summand of degree `i + j` of `X ⊗ Y` (`ιTotal_tensorHom_ιTotal_total_μ`), and its unit is
the inclusion of `𝟙_ C` in degree `0` (`total_ε`). -/
-- A definition rather than an `instance` declaration, so that its body, which uses the private
-- lemmas proving the laws, is not exported; `ιTotal_tensorHom_ιTotal_total_μ` and `total_ε`
-- characterize it.
@[instance_reducible, instance]
def totalLaxMonoidal : (total I C).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (Monoidal.tensorUnit₀.inv ≫ ιTotal (𝟙_ (GradedObject I C)) 0)
    (fun X Y ↦ totalTensorDesc fun i j ↦
      Monoidal.ιTensorObj X Y i j (i + j) rfl ≫ ιTotal (X ⊗ Y) (i + j))
    (total_μ_natural _ ιTotal_tensorHom_ιTotal_totalTensorDesc_ιTensorObj)
    (total_associativity _ ιTotal_tensorHom_ιTotal_totalTensorDesc_ιTensorObj)
    (total_left_unitality _ ιTotal_tensorHom_ιTotal_totalTensorDesc_ιTensorObj)
    (total_right_unitality _ ιTotal_tensorHom_ιTotal_totalTensorDesc_ιTensorObj)

/-- On the summand `Xᵢ ⊗ Yⱼ`, the tensor map of the total object is the inclusion of `Xᵢ ⊗ Yⱼ`
into the summand of degree `n = i + j` of `X ⊗ Y`. -/
@[reassoc (attr := simp)]
lemma ιTotal_tensorHom_ιTotal_total_μ (X Y : GradedObject I C) (i j n : I) (h : i + j = n) :
    (ιTotal X i ⊗ₘ ιTotal Y j) ≫ Functor.LaxMonoidal.μ (total I C) X Y =
      Monoidal.ιTensorObj X Y i j n h ≫ ιTotal (X ⊗ Y) n :=
  ιTotal_tensorHom_ιTotal_totalTensorDesc_ιTensorObj X Y i j n h

/-- The unit of the total object is the inclusion of `𝟙_ C` as the summand of degree `0`. -/
@[simp, reassoc]
lemma total_ε :
    Functor.LaxMonoidal.ε (total I C) =
      Monoidal.tensorUnit₀.inv ≫ ιTotal (𝟙_ (GradedObject I C)) 0 :=
  (rfl)

end LaxMonoidal

section LaxBraided

variable [AddCommMonoid I] [BraidedCategory C]
  [∀ A : C, PreservesColimitsOfShape (Discrete I) (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape (Discrete I) (tensorRight A)]
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- When `C` is braided and `I` is commutative, the total object is lax braided: on the summand
`Xᵢ ⊗ Yⱼ`, both composites are the braiding `Xᵢ ⊗ Yⱼ ≅ Yⱼ ⊗ Xᵢ` followed by the inclusion into
degree `i + j`. -/
instance totalLaxBraided : (total I C).LaxBraided where
  braided X Y := total_tensor_hom_ext fun i j ↦ by
    rw [ιTotal_tensorHom_ιTotal_total_μ_assoc X Y i j _ rfl, ιTotal_total_map,
      ιTensorObj_braiding_hom_assoc, BraidedCategory.braiding_naturality_assoc,
      ιTotal_tensorHom_ιTotal_total_μ Y X j i _ (add_comm j i)]

end LaxBraided

end CategoryTheory.GradedObject
