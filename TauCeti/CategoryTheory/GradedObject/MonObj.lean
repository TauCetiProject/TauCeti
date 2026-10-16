/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.GradedObject.Braiding
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import TauCeti.CategoryTheory.EqToHom

/-!
# Monoid objects in graded objects from homogeneous data

For a monoidal category `C` and an additive monoid `I`, the tensor product of graded objects
`X ⊗ Y` has the coproduct of the `X i ⊗ Y j` with `i + j = n` in degree `n`, and the unit is
`𝟙_ C` placed in degree `0`. A monoid object structure on a graded object `X` is therefore the
same as a family of homogeneous multiplications `X i ⊗ X j ⟶ X (i + j)` together with a unit
`𝟙_ C ⟶ X 0`, subject to the graded associativity and unit laws. This file proves the
introduction direction of that description: it assembles such homogeneous data into a monoid
object, a commutative monoid object when the homogeneous multiplications commute, and recognizes
morphisms of monoid objects by their homogeneous components. This is how graded algebras such as
symmetric algebras, which are naturally described degree by degree, are given the structure of
monoid objects in graded objects.

Homogeneous data can be transported along a lax monoidal functor `F : C ⥤ D`: given
identifications `e n : Y n ≅ F.obj (X n)`, the multiplications
`Y i ⊗ Y j ⟶ F.obj (X i) ⊗ F.obj (X j) ⟶ F.obj (X i ⊗ X j) ⟶ F.obj (X (i + j)) ⟶ Y (i + j)`
and the unit `𝟙_ D ⟶ F.obj (𝟙_ C) ⟶ F.obj (X 0) ⟶ Y 0` satisfy the graded laws whenever the
original data do, and the graded commutativity law too when `F` is lax braided. This is how a
graded algebra described degree by degree on presheaves, such as a sectionwise symmetric algebra,
passes to sheaves along sheafification.

## Main declarations

* `CategoryTheory.GradedObject.Monoidal.mulOfHomogeneous`: the morphism `X ⊗ X ⟶ X` assembled
  from homogeneous multiplications, characterized by
  `CategoryTheory.GradedObject.Monoidal.ιTensorObj_mulOfHomogeneous`;
* `CategoryTheory.GradedObject.Monoidal.oneOfDegreeZero`: the morphism `𝟙_ ⟶ X` determined by a
  morphism `𝟙_ C ⟶ X 0`;
* `CategoryTheory.GradedObject.monObjOfHomogeneous`: the monoid object structure defined by
  homogeneous data satisfying the graded associativity and unit laws;
* `CategoryTheory.GradedObject.isCommMonObj_monObjOfHomogeneous`: commutativity of that monoid
  object from graded commutativity of the homogeneous multiplications;
* `CategoryTheory.GradedObject.isMonHom_of_homogeneous`: a morphism of graded objects between
  monoid objects is a monoid morphism once it preserves the unit in degree zero and the
  multiplication of homogeneous components;
* `CategoryTheory.GradedObject.mul_assoc_of_laxMonoidal`,
  `CategoryTheory.GradedObject.one_mul_of_laxMonoidal`,
  `CategoryTheory.GradedObject.mul_one_of_laxMonoidal` and
  `CategoryTheory.GradedObject.mul_comm_of_laxBraided`: the graded laws of homogeneous data
  transported along a lax monoidal (resp. lax braided) functor;
* `CategoryTheory.GradedObject.map_mul_of_laxMonoidal`: transported morphisms commute with the
  transported homogeneous multiplications.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj

namespace CategoryTheory.GradedObject

variable {I : Type*} {C : Type*} [Category* C] [MonoidalCategory C]

section AddMonoid

variable [AddMonoid I]

namespace Monoidal

section Mul

variable (X : GradedObject I C) [HasTensor X X]

/-- The morphism `X ⊗ X ⟶ X` of graded objects whose restriction to the summand `X i ⊗ X j` of
degree `i + j` is the homogeneous multiplication `mul i j`. -/
def mulOfHomogeneous (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j)) : tensorObj X X ⟶ X :=
  fun _ ↦ tensorObjDesc fun i j h ↦ mul i j ≫ eqToHom (congrArg X h)

/-- On the summand `X i ⊗ X j` of degree `n = i + j`, the assembled multiplication is the
homogeneous multiplication followed by the transport along `i + j = n`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_mulOfHomogeneous (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j)) (i j n : I)
    (h : i + j = n) :
    ιTensorObj X X i j n h ≫ mulOfHomogeneous X mul n = mul i j ≫ eqToHom (congrArg X h) :=
  ι_tensorObjDesc _ _ _ _

end Mul

section One

variable [DecidableEq I] [HasInitial C]

/-- Two morphisms out of the tensor unit of graded objects agree as soon as they agree in degree
zero, since the unit is initial in every other degree. -/
lemma tensorUnit_hom_ext {X : GradedObject I C} (f g : tensorUnit ⟶ X) (h : f 0 = g 0) :
    f = g := by
  ext i
  by_cases hi : i = 0
  · subst hi
    exact h
  · exact (isInitialTensorUnitApply i hi).hom_ext _ _

variable (X : GradedObject I C)

/-- The morphism `𝟙_ ⟶ X` of graded objects given in degree zero by `one : 𝟙_ C ⟶ X 0`; in
every other degree the tensor unit is initial. -/
def oneOfDegreeZero (one : 𝟙_ C ⟶ X 0) : tensorUnit ⟶ X := fun i ↦
  if h : i = 0 then (singleObjApplyIsoOfEq 0 (𝟙_ C) i h).hom ≫ one ≫ eqToHom (congrArg X h.symm)
  else (isInitialTensorUnitApply i h).to (X i)

/-- In degree zero, the unit determined by `one` is `one`, up to the identification of the
degree-zero part of the tensor unit with `𝟙_ C`. -/
@[simp]
lemma oneOfDegreeZero_zero (one : 𝟙_ C ⟶ X 0) :
    oneOfDegreeZero X one 0 = tensorUnit₀.hom ≫ one := by
  simp [oneOfDegreeZero, tensorUnit₀]

end One

end Monoidal

section MonObj

variable
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- A morphism of graded objects between monoid objects is a morphism of monoid objects as soon
as it preserves the unit in degree zero and commutes with multiplication on every pair of
homogeneous components. -/
lemma isMonHom_of_homogeneous {X Y : GradedObject I C} [MonObj X] [MonObj Y] (f : X ⟶ Y)
    (one_f : η[X] 0 ≫ f 0 = η[Y] 0)
    (mul_f : ∀ i j, Monoidal.ιTensorObj X X i j (i + j) rfl ≫ μ[X] (i + j) ≫ f (i + j) =
      (f i ⊗ₘ f j) ≫ Monoidal.ιTensorObj Y Y i j (i + j) rfl ≫ μ[Y] (i + j)) :
    IsMonHom f where
  one_hom := Monoidal.tensorUnit_hom_ext _ _ one_f
  mul_hom := by
    ext n
    refine Monoidal.tensorObj_ext _ _ fun i j h ↦ ?_
    subst h
    -- The tensor product of morphisms of graded objects is `Monoidal.tensorHom`.
    change Monoidal.ιTensorObj X X i j (i + j) rfl ≫ (μ[X] ≫ f) (i + j) =
      Monoidal.ιTensorObj X X i j (i + j) rfl ≫ (Monoidal.tensorHom f f ≫ μ[Y]) (i + j)
    simpa using mul_f i j

variable (X : GradedObject I C) (one : 𝟙_ C ⟶ X 0) (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j))
  (one_mul : ∀ n, (one ▷ X n) ≫ mul 0 n = (λ_ (X n)).hom ≫ eqToHom (congrArg X (zero_add n).symm))
  (mul_one : ∀ n, (X n ◁ one) ≫ mul n 0 = (ρ_ (X n)).hom ≫ eqToHom (congrArg X (add_zero n).symm))
  (mul_assoc : ∀ i j k, (mul i j ▷ X k) ≫ mul (i + j) k =
    (α_ _ _ _).hom ≫ (X i ◁ mul j k) ≫ mul i (j + k) ≫
      eqToHom (congrArg X (add_assoc i j k).symm))

/-- The monoid object structure on a graded object `X` given by a unit `one : 𝟙_ C ⟶ X 0` and
homogeneous multiplications `mul i j : X i ⊗ X j ⟶ X (i + j)` satisfying the graded unit and
associativity laws, in which the degrees are identified along `0 + n = n`, `n + 0 = n` and
`i + (j + k) = i + j + k`. -/
abbrev monObjOfHomogeneous :
    MonObj X where
  one := Monoidal.oneOfDegreeZero X one
  mul := Monoidal.mulOfHomogeneous X mul
  one_mul := by
    rw [← cancel_epi (λ_ X).inv, Iso.inv_hom_id]
    ext n
    -- The inverse left unitor of graded objects includes `𝟙_ C ⊗ X n` as the summand `(0, n)`,
    -- and right whiskering of graded objects is `Monoidal.tensorHom`.
    change ((Monoidal.leftUnitor X).inv ≫
      Monoidal.tensorHom (Monoidal.oneOfDegreeZero X one) (𝟙 X) ≫
        Monoidal.mulOfHomogeneous X mul) n = 𝟙 _
    simp [Monoidal.leftUnitor_inv_apply, reassoc_of% one_mul n]
  mul_one := by
    rw [← cancel_epi (ρ_ X).inv, Iso.inv_hom_id]
    ext n
    -- The inverse right unitor of graded objects includes `X n ⊗ 𝟙_ C` as the summand `(n, 0)`,
    -- and left whiskering of graded objects is `Monoidal.tensorHom`.
    change ((Monoidal.rightUnitor X).inv ≫
      Monoidal.tensorHom (𝟙 X) (Monoidal.oneOfDegreeZero X one) ≫
        Monoidal.mulOfHomogeneous X mul) n = 𝟙 _
    simp [Monoidal.rightUnitor_inv_apply, reassoc_of% mul_one n]
  mul_assoc := by
    ext n
    refine Monoidal.tensorObj₃'_ext _ _ fun i j k h ↦ ?_
    -- The associator of graded objects is `Monoidal.associator`, which sends the summand
    -- `(X i ⊗ X j) ⊗ X k` to `X i ⊗ (X j ⊗ X k)` by the associator of `C`; whiskering of
    -- graded objects is `Monoidal.tensorHom`.
    change Monoidal.ιTensorObj₃' X X X i j k n h ≫ (Monoidal.tensorHom
        (Monoidal.mulOfHomogeneous X mul) (𝟙 X) ≫ Monoidal.mulOfHomogeneous X mul) n =
      Monoidal.ιTensorObj₃' X X X i j k n h ≫ (Monoidal.associator X X X).hom n ≫
        (Monoidal.tensorHom (𝟙 X) (Monoidal.mulOfHomogeneous X mul) ≫
          Monoidal.mulOfHomogeneous X mul) n
    rw [Monoidal.ιTensorObj₃'_associator_hom_assoc,
      Monoidal.ιTensorObj₃'_eq X X X i j k n h (i + j) rfl,
      Monoidal.ιTensorObj₃_eq X X X i j k n h (j + k) rfl]
    simp [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc, reassoc_of% mul_assoc i j k]

/-- The multiplication of the monoid object defined by homogeneous data is assembled from the
homogeneous multiplications. -/
@[simp]
lemma mul_monObjOfHomogeneous :
    MonObj.mul (self := monObjOfHomogeneous X one mul one_mul mul_one mul_assoc) =
      Monoidal.mulOfHomogeneous X mul :=
  rfl

/-- The unit of the monoid object defined by homogeneous data is the given unit in degree zero. -/
@[simp]
lemma one_monObjOfHomogeneous :
    MonObj.one (self := monObjOfHomogeneous X one mul one_mul mul_one mul_assoc) =
      Monoidal.oneOfDegreeZero X one :=
  rfl

end MonObj

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid I] [BraidedCategory C]
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- On the summand `X i ⊗ Y j`, the braiding of graded objects is the braiding of `C` followed
by the inclusion of the summand `Y j ⊗ X i`. -/
@[reassoc (attr := simp)]
lemma ιTensorObj_braiding_hom (X Y : GradedObject I C) (i j n : I) (h : i + j = n) :
    Monoidal.ιTensorObj X Y i j n h ≫ (β_ X Y).hom n =
      (β_ (X i) (Y j)).hom ≫ Monoidal.ιTensorObj Y X j i n (by rw [add_comm, h]) := by
  -- The braiding of graded objects is `Monoidal.braiding`, defined summand by summand.
  change Monoidal.ιTensorObj X Y i j n h ≫ (Monoidal.braiding X Y).hom n = _
  simp [Monoidal.braiding]

variable (X : GradedObject I C) (one : 𝟙_ C ⟶ X 0) (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j))
  (one_mul : ∀ n, (one ▷ X n) ≫ mul 0 n = (λ_ (X n)).hom ≫ eqToHom (congrArg X (zero_add n).symm))
  (mul_one : ∀ n, (X n ◁ one) ≫ mul n 0 = (ρ_ (X n)).hom ≫ eqToHom (congrArg X (add_zero n).symm))
  (mul_assoc : ∀ i j k, (mul i j ▷ X k) ≫ mul (i + j) k =
    (α_ _ _ _).hom ≫ (X i ◁ mul j k) ≫ mul i (j + k) ≫
      eqToHom (congrArg X (add_assoc i j k).symm))

/-- The monoid object defined by homogeneous data is commutative when the homogeneous
multiplications commute up to the identification of the degrees `i + j` and `j + i`. -/
lemma isCommMonObj_monObjOfHomogeneous
    (mul_comm : ∀ i j, (β_ (X i) (X j)).hom ≫ mul j i =
      mul i j ≫ eqToHom (congrArg X (add_comm i j))) :
    letI := monObjOfHomogeneous X one mul one_mul mul_one mul_assoc
    IsCommMonObj X :=
  letI := monObjOfHomogeneous X one mul one_mul mul_one mul_assoc
  { mul_comm := by
      ext n
      refine Monoidal.tensorObj_ext _ _ fun i j h ↦ ?_
      simp [reassoc_of% mul_comm i j] }

end AddCommMonoid

section LaxMonoidal

variable {I : Type*} [AddMonoid I] {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D] {F : C ⥤ D} [F.LaxMonoidal]
  {X : GradedObject I C} {Y : GradedObject I D} {e : ∀ n, Y n ≅ F.obj (X n)}
  (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j)) (mul' : ∀ i j, Y i ⊗ Y j ⟶ Y (i + j))
  (hmul : ∀ i j, mul' i j =
    ((e i).hom ⊗ₘ (e j).hom) ≫ Functor.LaxMonoidal.μ F (X i) (X j) ≫ F.map (mul i j) ≫
      (e (i + j)).inv)
include hmul

/-- Homogeneous multiplications transported along a lax monoidal functor `F` and identifications
`e n : Y n ≅ F.obj (X n)` are associative, up to the identification of the degrees
`i + (j + k)` and `i + j + k`, when the original ones are. -/
lemma mul_assoc_of_laxMonoidal
    (mul_assoc : ∀ i j k, (mul i j ▷ X k) ≫ mul (i + j) k =
      (α_ _ _ _).hom ≫ (X i ◁ mul j k) ≫ mul i (j + k) ≫
        eqToHom (congrArg X (add_assoc i j k).symm)) (i j k : I) :
    (mul' i j ▷ Y k) ≫ mul' (i + j) k =
      (α_ _ _ _).hom ≫ (Y i ◁ mul' j k) ≫ mul' i (j + k) ≫
        eqToHom (congrArg Y (add_assoc i j k).symm) := by
  have core : ((Functor.LaxMonoidal.μ F (X i) (X j) ≫ F.map (mul i j)) ⊗ₘ 𝟙 (F.obj (X k))) ≫
      Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul (i + j) k) =
        (α_ _ _ _).hom ≫ (𝟙 (F.obj (X i)) ⊗ₘ (Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul j k))) ≫
          Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul i (j + k)) ≫
            F.map (eqToHom (congrArg X (add_assoc i j k).symm)) := by
    rw [tensorHom_id, id_tensorHom, comp_whiskerRight, Category.assoc,
      Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp, mul_assoc]
    simp
  calc (mul' i j ▷ Y k) ≫ mul' (i + j) k
      = (((e i).hom ⊗ₘ (e j).hom) ⊗ₘ (e k).hom) ≫
          ((Functor.LaxMonoidal.μ F (X i) (X j) ≫ F.map (mul i j)) ⊗ₘ 𝟙 (F.obj (X k))) ≫
            Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul (i + j) k) ≫ (e _).inv := by
        rw [hmul, hmul, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          tensorHom_comp_tensorHom_assoc]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    _ = _ := by
        rw [reassoc_of% core, associator_naturality_assoc, tensorHom_comp_tensorHom_assoc,
          TauCeti.eqToHom_eq_iso_hom_map_eqToHom F e (add_assoc i j k).symm, hmul, hmul,
          ← id_tensorHom]
        simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id,
          Iso.inv_hom_id_assoc, Category.comp_id, Category.id_comp]

/-- Morphisms transported along a lax monoidal functor `F` and identifications
`e n : Y n ≅ F.obj (X n)`, `e' n : Y' n ≅ F.obj (X' n)` commute with the transported homogeneous
multiplications when the original morphisms commute with the original ones. -/
lemma map_mul_of_laxMonoidal {X' : GradedObject I C} {Y' : GradedObject I D}
    {e' : ∀ n, Y' n ≅ F.obj (X' n)} (mulX' : ∀ i j, X' i ⊗ X' j ⟶ X' (i + j))
    (mulY' : ∀ i j, Y' i ⊗ Y' j ⟶ Y' (i + j))
    (hmulY' : ∀ i j, mulY' i j =
      ((e' i).hom ⊗ₘ (e' j).hom) ≫ Functor.LaxMonoidal.μ F (X' i) (X' j) ≫ F.map (mulX' i j) ≫
        (e' (i + j)).inv)
    (f : ∀ n, X n ⟶ X' n) (g : ∀ n, Y n ⟶ Y' n)
    (hg : ∀ n, g n = (e n).hom ≫ F.map (f n) ≫ (e' n).inv)
    (map_mul : ∀ i j, (f i ⊗ₘ f j) ≫ mulX' i j = mul i j ≫ f (i + j)) (i j : I) :
    (g i ⊗ₘ g j) ≫ mulY' i j = mul' i j ≫ g (i + j) := by
  rw [hg, hg, hg, hmul, hmulY']
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc,
    Category.comp_id]
  rw [← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural_assoc, ← F.map_comp_assoc,
    map_mul, F.map_comp_assoc]

variable (one : 𝟙_ C ⟶ X 0) (one' : 𝟙_ D ⟶ Y 0)
  (hone : one' = Functor.LaxMonoidal.ε F ≫ F.map one ≫ (e 0).inv)
include hone

/-- A unit and homogeneous multiplications transported along a lax monoidal functor `F` and
identifications `e n : Y n ≅ F.obj (X n)` satisfy the left unit law, up to the identification of
the degrees `0 + n` and `n`, when the original ones do. -/
lemma one_mul_of_laxMonoidal
    (one_mul : ∀ n, (one ▷ X n) ≫ mul 0 n =
      (λ_ (X n)).hom ≫ eqToHom (congrArg X (zero_add n).symm)) (n : I) :
    (one' ▷ Y n) ≫ mul' 0 n = (λ_ (Y n)).hom ≫ eqToHom (congrArg Y (zero_add n).symm) := by
  have core : ((Functor.LaxMonoidal.ε F ≫ F.map one) ⊗ₘ 𝟙 (F.obj (X n))) ≫
      Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul 0 n) =
        (λ_ _).hom ≫ F.map (eqToHom (congrArg X (zero_add n).symm)) := by
    rw [tensorHom_id, comp_whiskerRight, Category.assoc, Functor.LaxMonoidal.μ_natural_left_assoc,
      ← F.map_comp, one_mul, F.map_comp, Functor.LaxMonoidal.left_unitality]
    simp only [Category.assoc]
  calc (one' ▷ Y n) ≫ mul' 0 n
      = (𝟙_ D ◁ (e n).hom) ≫ ((Functor.LaxMonoidal.ε F ≫ F.map one) ⊗ₘ 𝟙 (F.obj (X n))) ≫
          Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul 0 n) ≫ (e _).inv := by
        rw [hone, hmul, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, ← id_tensorHom,
          tensorHom_comp_tensorHom_assoc]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    _ = _ := by
        rw [reassoc_of% core, leftUnitor_naturality_assoc,
          TauCeti.eqToHom_eq_iso_hom_map_eqToHom F e (zero_add n).symm]

/-- A unit and homogeneous multiplications transported along a lax monoidal functor `F` and
identifications `e n : Y n ≅ F.obj (X n)` satisfy the right unit law, up to the identification of
the degrees `n + 0` and `n`, when the original ones do. -/
lemma mul_one_of_laxMonoidal
    (mul_one : ∀ n, (X n ◁ one) ≫ mul n 0 =
      (ρ_ (X n)).hom ≫ eqToHom (congrArg X (add_zero n).symm)) (n : I) :
    (Y n ◁ one') ≫ mul' n 0 = (ρ_ (Y n)).hom ≫ eqToHom (congrArg Y (add_zero n).symm) := by
  have core : (𝟙 (F.obj (X n)) ⊗ₘ (Functor.LaxMonoidal.ε F ≫ F.map one)) ≫
      Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul n 0) =
        (ρ_ _).hom ≫ F.map (eqToHom (congrArg X (add_zero n).symm)) := by
    rw [id_tensorHom, whiskerLeft_comp, Category.assoc, Functor.LaxMonoidal.μ_natural_right_assoc,
      ← F.map_comp, mul_one, F.map_comp, Functor.LaxMonoidal.right_unitality]
    simp only [Category.assoc]
  calc (Y n ◁ one') ≫ mul' n 0
      = ((e n).hom ▷ 𝟙_ D) ≫ (𝟙 (F.obj (X n)) ⊗ₘ (Functor.LaxMonoidal.ε F ≫ F.map one)) ≫
          Functor.LaxMonoidal.μ F _ _ ≫ F.map (mul n 0) ≫ (e _).inv := by
        rw [hone, hmul, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, ← tensorHom_id,
          tensorHom_comp_tensorHom_assoc]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    _ = _ := by
        rw [reassoc_of% core, rightUnitor_naturality_assoc,
          TauCeti.eqToHom_eq_iso_hom_map_eqToHom F e (add_zero n).symm]

end LaxMonoidal

section LaxBraided

variable {I : Type*} [AddCommMonoid I] {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
  {F : C ⥤ D} [F.LaxBraided] {X : GradedObject I C} {Y : GradedObject I D}
  {e : ∀ n, Y n ≅ F.obj (X n)}
  (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j)) (mul' : ∀ i j, Y i ⊗ Y j ⟶ Y (i + j))
  (hmul : ∀ i j, mul' i j =
    ((e i).hom ⊗ₘ (e j).hom) ≫ Functor.LaxMonoidal.μ F (X i) (X j) ≫ F.map (mul i j) ≫
      (e (i + j)).inv)
include hmul

/-- Homogeneous multiplications transported along a lax braided functor `F` and identifications
`e n : Y n ≅ F.obj (X n)` are commutative, up to the identification of the degrees `i + j` and
`j + i`, when the original ones are. -/
lemma mul_comm_of_laxBraided
    (mul_comm : ∀ i j, (β_ (X i) (X j)).hom ≫ mul j i =
      mul i j ≫ eqToHom (congrArg X (add_comm i j))) (i j : I) :
    (β_ (Y i) (Y j)).hom ≫ mul' j i = mul' i j ≫ eqToHom (congrArg Y (add_comm i j)) := by
  rw [hmul, hmul, ← BraidedCategory.braiding_naturality_assoc, ← Functor.LaxBraided.braided_assoc,
    ← F.map_comp_assoc, mul_comm, TauCeti.eqToHom_eq_iso_hom_map_eqToHom F e (add_comm i j)]
  simp

end LaxBraided

end CategoryTheory.GradedObject
